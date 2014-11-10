;Copyright (c) 2012-2014, Joshua Scoggins 
;All rights reserved.
;
;Redistribution and use in source and binary forms, with or without
;modification, are permitted provided that the following conditions are met:
;    * Redistributions of source code must retain the above copyright
;      notice, this list of conditions and the following disclaimer.
;    * Redistributions in binary form must reproduce the above copyright
;      notice, this list of conditions and the following disclaimer in the
;      documentation and/or other materials provided with the distribution.
;
;THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
;ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
;WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
;DISCLAIMED. IN NO EVENT SHALL Joshua Scoggins BE LIABLE FOR ANY
;DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
;(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
;LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
;ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
;------------------------------------------------------------------------------
; The Analysis stage is the first stage that takes place when LLVM hands off
; control to CLIPS. It is tasked with:
; 
; 1) Identifying Parent Hierarchies for BasicBlocks, Regions, Instructions, and
; Loops
; 2) Identifying Variant and Invariant Operands for Instructions and BasicBlocks
; 3) Identifying Producers and Consumers on the Block Level
; 4) Partial Aspect Block Choking using the list of UsedInBlocks found in each
; instruction.
; 
; What's neat about this stage is that the rules can be fired in any order as
; they will evaluate correctly based on salience tweaking and the fact that the
; information is independent of one another. This means that I don't need to
; worry about breaking pre-existing rules as I add new rules to this Stage.
; 
; This stage will contain the most number of rules out of any stage
; 
; As this code is being written this list will be updated.
;------------------------------------------------------------------------------
; Frequency analysis - Determines which regions to apply wavefront scheduling to
;------------------------------------------------------------------------------
(defrule InstanceFrequencyCounter
         "Creates a frequency counter hint for basic blocks"
         (declare (salience 2))
         (Stage FrequencyAnalysis $?)
         (object (is-a Region) (Class Region) (ID ?p) 
                 (CanWavefrontSchedule FALSE))
         (not (exists (object (is-a FrequencyAnalysis) (Parent ?p))))
         =>
         (make-instance of FrequencyAnalysis (Parent ?p)))
;------------------------------------------------------------------------------
(defrule IncrementFrequencyCounter-BasicBlock
         "Goes through a given Region counting the number of basic blocks found
         within the region. Valid blocks are blocks that contain more than one 
         instruction as we don't want to count JS nodes as they don't usually 
         contain code."
         (declare (salience 1))
         (Stage FrequencyAnalysis $?)
         (object (is-a Region) (ID ?p) (Class Region) (Contents $? ?t $?) 
                 (CanWavefrontSchedule FALSE))
         (object (is-a BasicBlock) (ID ?t) (Parent ?p) (Contents $?insts))
         (test (> (length$ $?insts) 1))
         ?fa <- (object (is-a FrequencyAnalysis) (Parent ?p))
         =>
         (send ?fa .IncrementFrequency))
;------------------------------------------------------------------------------
(defrule ImplyEnoughBlocks
         "There are enough blocks within the target region to make it a 
         candidate for wavefront scheduling. Make a hint that says this."
         ;(declare (salience 200))
         (Stage FrequencyAnalysis $?)
         ?fa <- (object (is-a FrequencyAnalysis) (Parent ?p) 
                        (Frequency ?z&:(and (< ?z 100) (> ?z 1))))
         ?region <- (object (is-a Region) (Class Region) (ID ?p))
         =>
         (unmake-instance ?fa)
         (modify-instance ?region (CanWavefrontSchedule TRUE)))
;------------------------------------------------------------------------------
; Block dependency creation - Rules pertaining to the creation of data 
; dependencies between different instructions inside of a basic block
;------------------------------------------------------------------------------
(defrule MarkLocalDependency-Call
 			(declare (salience 1))
         (Stage Analysis $?)
         (object (is-a CallInstruction) (Parent ?p) (ID ?t0) 
                        (ArgumentOperands $? ?o $?))
         (object (is-a Instruction) (ID ?o) (Parent ?p))
         =>
         (assert (Instruction ?o produces ?t0)
                 (Instruction ?t0 consumes ?o)))
;------------------------------------------------------------------------------
(defrule MarkLocalDependency 
         (Stage Analysis $?)
         ?i0 <- (object (is-a Instruction&~CallInstruction) (Parent ?p) (ID ?t0) 
                        (Operands $? ?o $?))
         (object (is-a Instruction) (ID ?o) (Parent ?p))
         =>
         (assert (Instruction ?o produces ?t0)
                 (Instruction ?t0 consumes ?o)))
;------------------------------------------------------------------------------
(defrule MarkInstructionsThatHappenBeforeCall-WritesToMemory
         (Stage Analysis $?)
         (object (is-a BasicBlock) (ID ?v) (Contents $?before ?n0 $?))
         (object (is-a CallInstruction) (ID ?n0) (Parent ?v) 
                 (MayWriteToMemory TRUE))
         =>
         (progn$ (?n1 ?before)
                 (assert (Instruction ?n0 consumes ?n1)
                         (Instruction ?n1 produces ?n0))))
;------------------------------------------------------------------------------
(defrule MarkInstructionsThatHappenBeforeCall-HasSideEffects
         (Stage Analysis $?)
         (object (is-a BasicBlock) (ID ?p) (Contents $?a ?n0 $?))
         (object (is-a CallInstruction) (ID ?n0) (Parent ?p)
                 (MayHaveSideEffects TRUE))
         =>
         (progn$ (?n1 ?a)
                 (assert (Instruction ?n0 consumes ?n1)
                         (Instruction ?n1 produces ?n0))))
;------------------------------------------------------------------------------
(defrule MarkCallInstructionDependency-ModifiesMemory
         "Creates a series of dependencies for all instructions following a 
         call instruction if it turns out that the call could modify memory."
         (Stage Analysis $?)
         (object (is-a BasicBlock) (ID ?p) (Contents $? ?name $?rest))
         (object (is-a CallInstruction) (ID ?name) (Parent ?p)
                 (MayWriteToMemory TRUE))
         =>
         (assert (Element ?p has a CallBarrier))
         (progn$ (?following ?rest)
                 (assert (Instruction ?following has a CallDependency)
                         ;(Instruction ?following consumes ?name)
                         (Instruction ?name produces ?following))))
;------------------------------------------------------------------------------
(defrule MarkCallInstructionDependency-InlineAsm
         "Creates a series of dependencies for all instructions following a 
         call instruction if it turns out that the call is inline asm."
         (Stage Analysis $?)
         (object (is-a BasicBlock) (ID ?p) (Contents $? ?name $?rest))
         (object (is-a CallInstruction) (ID ?name) (Parent ?p) 
                 (IsInlineAsm TRUE))
         =>
         (assert (Element ?p has a CallBarrier))
         (progn$ (?following ?rest)
                 (assert (Instruction ?following has a CallDependency)
                         ;(Instruction ?following consumes ?name)
                         (Instruction ?name produces ?following))))
;------------------------------------------------------------------------------
(defrule MarkCallInstructionDependency-SideEffects
         "Creates a series of dependencies for all instructions following a 
         call instruction if it turns out that the call has side effects."
         (Stage Analysis $?)
         (object (is-a CallInstruction) (ID ?name) (Parent ?p)
                 (MayHaveSideEffects TRUE)) 
         (object (is-a BasicBlock) (ID ?p) (Contents $? ?name $?rest))
         =>
         (assert (Element ?p has a CallBarrier))
         (progn$ (?following ?rest)
                 (assert (Instruction ?following has a CallDependency)
                         ;(Instruction ?following consumes ?name)
                         (Instruction ?name produces ?following))))
;------------------------------------------------------------------------------
(defrule FlagCallBarrierForDiplomat-HasParent
         ;(declare (salience -10))
         (Stage Analysis-Update $?)
         ?fct <- (Element ?z has a CallBarrier)
         ?d <- (object (is-a Diplomat) (ID ?z) (Parent ?p) 
                       (HasCallBarrier FALSE))
         (exists (object (is-a Diplomat) (ID ?p)))
         =>
         (retract ?fct)
         (assert (Element ?p has a CallBarrier))
         (modify-instance ?d (HasCallBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule PropagateCallBarrierForDiplomat-HasParent
         ;(declare (salience -10))
         (Stage Analysis-Update $?)
         ?fct <- (Element ?z has a CallBarrier)
         ?d <- (object (is-a Diplomat) (ID ?z) (Parent ?p) 
                       (HasCallBarrier TRUE))
         (exists (object (is-a Diplomat) (ID ?p)))
         =>
         (retract ?fct)
         (assert (Element ?p has a CallBarrier)))
;------------------------------------------------------------------------------
(defrule FlagCallBarrierForDiplomat-NoParent
         ;(declare (salience -10))
         (Stage Analysis-Update $?)
         ?fct <- (Element ?z has a CallBarrier)
         ?d <- (object (is-a Diplomat) (ID ?z) (Parent ?p) 
                       (HasCallBarrier FALSE))
         (not (exists (object (is-a Diplomat) (ID ?p))))
         =>
         (retract ?fct)
         (modify-instance ?d (HasCallBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule PropagateCallBarrierForDiplomat-NoParent
         ;(declare (salience -10))
         (Stage Analysis-Update $?)
         ?fct <- (Element ?z has a CallBarrier)
         ?d <- (object (is-a Diplomat) (ID ?z) (Parent ?p) 
                       (HasCallBarrier TRUE))
         (not (exists (object (is-a Diplomat) (ID ?p))))
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule MarkHasACallDependency-Set
         (Stage Analysis-Update $?)
         ?fct <- (Instruction ?target has a CallDependency)
         ?inst <- (object (is-a Instruction) (ID ?target) 
                          (HasCallDependency FALSE))
         =>
         (retract ?fct)
         (modify-instance ?inst (HasCallDependency TRUE)))
;------------------------------------------------------------------------------
(defrule MarkHasACallDependency-Ignore
         (Stage Analysis-Update $?)
         ?fct <- (Instruction ?target has a CallDependency)
         ?inst <- (object (is-a Instruction) (ID ?target) 
                          (HasCallDependency TRUE))
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule StoreToLoadDependency
         (Stage ExtendedMemoryAnalysis $?)
         (object (is-a StoreInstruction) (Parent ?p) (ID ?t0)
                 (TimeIndex ?ti0) (MemoryTarget ?sym0))
         (object (is-a LoadInstruction) (Parent ?p) (ID ?t1) 
                 (TimeIndex ?ti1&:(< ?ti0 ?ti1)) (MemoryTarget ?sym1))
         (test (or (eq ?sym0 ?sym1) (eq ?sym0 UNKNOWN)))
         =>
         (assert (Instruction ?t1 consumes ?t0)
                 (Instruction ?t0 produces ?t1)))
;------------------------------------------------------------------------------
(defrule StoreToStoreDependency
         (Stage ExtendedMemoryAnalysis $?)
         (object (is-a StoreInstruction) (Parent ?p) (ID ?t0)
                 (TimeIndex ?ti0) (MemoryTarget ?sym0))
         (object (is-a StoreInstruction) (Parent ?p) (ID ?t1) 
                 (TimeIndex ?ti1&:(< ?ti0 ?ti1)) (MemoryTarget ?sym1))
         (test (or (eq ?sym0 ?sym1) (eq ?sym0 UNKNOWN)))
         =>
         (assert (Instruction ?t1 consumes ?t0)
                 (Instruction ?t0 produces ?t1)))
;------------------------------------------------------------------------------
(defrule LoadToStoreDependency
         (Stage ExtendedMemoryAnalysis $?)
         (object (is-a LoadInstruction) (Parent ?p) (ID ?t0)
                 (TimeIndex ?ti0) (MemoryTarget ?sym0)) 
         (object (is-a StoreInstruction) (Parent ?p) (ID ?t1) 
                 (TimeIndex ?ti1&:(< ?ti0 ?ti1)) (MemoryTarget ?sym1))
         (test (or (eq ?sym0 ?sym1) (eq ?sym0 UNKNOWN)))
         =>
         (assert (Instruction ?t1 consumes ?t0)
                 (Instruction ?t0 produces ?t1)))
;------------------------------------------------------------------------------
; Memory barrier creation - Rules pertaining to the creation of
; memory barriers to prevent loads and stores from being moved above a specific
; point within the program during the act of scheduling.
;------------------------------------------------------------------------------
; Barriers consist of reads and writes that can't be verified as to their exact
; source. 
;------------------------------------------------------------------------------
; TODO: Put in a field for load and store instructions that describes what
; is being referenced. By default this slot is UNKNOWN.
;------------------------------------------------------------------------------
(defrule AssertLoadBarrierEvaluation
         "Creates a fact that tells the system to analyze the given load 
         instruction to see if it is necessary to create a memory barrier for 
         the given instruction"
         (declare (salience 5))
         (Stage Analysis $?)
         (object (is-a LoadInstruction) (ID ?t0) (Operands ?target $?))
         =>
         (assert (Analyze ?target for load ?t0)))
;------------------------------------------------------------------------------
(defrule AssertStoreBarrierEvaluation
         "Creates a fact that tells the system to analyze the given store 
         instruction to see if it is necessary to create a memory barrier for 
         the given instruction"
         (declare (salience 5))
         (Stage Analysis $?)
         (object (is-a StoreInstruction) (ID ?t0) 
                 (DestinationRegisters ?target))
         =>
         (assert (Analyze ?target for store ?t0)))
;------------------------------------------------------------------------------
(defrule IdentifyGetElementPointerLoadBarrier
         "Creates a load memory barrier hint if it turns out that the load 
         instruction refers to a getelementptr instruction but that 
         getelementptr doesn't refer to a alloca instruction or constant."
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for load ?t0)
         ?i0 <- (object (is-a LoadInstruction) (ID ?t0) (Parent ?p))
         (object (is-a GetElementPointerInstruction) (ID ?target) 
                 (Operands ?a $?))
         (object (is-a ~AllocaInstruction&~Constant) (ID ?a))
         (object (is-a BasicBlock) (ID ?p) (Parent ?r))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget UNKNOWN))
         (assert (element ?p reads from UNKNOWN)
                 (Element ?p has a MemoryBarrier)
                 (Element ?r has a MemoryBarrier)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithReadFrom-Alloca
         "Does a check to see if the load instruction refers directly to an
         AllocaInstruction or Constant. If it does then mark it as though the 
         block reads from it"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for load ?t0)
         ?i0 <- (object (is-a LoadInstruction) (ID ?t0) (Parent ?p))
         (object (is-a AllocaInstruction) (ID ?target))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?target))
         (assert (element ?p reads from ?target)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithReadFrom-Constant
         "Does a check to see if the load instruction refers directly to an
         AllocaInstruction or Constant. If it does then mark it as though the 
         block reads from it"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for load ?t0)
         ?i0 <- (object (is-a LoadInstruction) (ID ?t0) (Parent ?p))
         (object (is-a Constant) (ID ?target))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?target))
         (assert (element ?p reads from ?target)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithReadFrom-GetElementPointer-Alloca
         "Does a check to see if a given LoadInstruction referring to a
         GetElementPointerInstruction refers to an AllocaInstruction or 
         Constant. If it does then mark it in the ReadsFrom multifield"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for load ?t0)
         ?i0 <- (object (is-a LoadInstruction) (ID ?t0) (Parent ?p))
         (object (is-a GetElementPointerInstruction) (ID ?target) 
                 (Operands ?a $?))
         (object (is-a AllocaInstruction) (ID ?a))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?a))
         (assert (element ?p reads from ?a)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithReadFrom-GetElementPointer-Constant
         "Does a check to see if a given LoadInstruction referring to a
         GetElementPointerInstruction refers to an AllocaInstruction or 
         Constant. If it does then mark it in the ReadsFrom multifield"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for load ?t0)
         ?i0 <- (object (is-a LoadInstruction) (ID ?t0) (Parent ?p))
         (object (is-a GetElementPointerInstruction) (ID ?target) 
                 (Operands ?a $?))
         (object (is-a Constant) (ID ?a))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?a))
         (assert (element ?p reads from ?a)))
;------------------------------------------------------------------------------
(defrule IdentifyGeneralLoadBarrier
         "Creates a load memory barrier hint if it turns out that the load 
         instruction in question refers to a register that isn't an 
         AllocaInstruction, GetElementPointerInstruction, or Constant."
         (declare (salience 3))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for load ?t0)
         ?i0 <- (object (is-a LoadInstruction) (ID ?t0) (Parent ?p))
         (object (is-a BasicBlock) (ID ?p) (Parent ?r))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget UNKNOWN))
         (assert (element ?p reads from UNKNOWN)
                 (Element ?p has a MemoryBarrier)
                 (Element ?r has a MemoryBarrier)))
;------------------------------------------------------------------------------
(defrule IdentifyGetElementPointerStoreBarrier
         "Creates a store memory barrier hint if it turns out that the store 
         instruction refers to a getelementptr instruction but that 
         getelementptr doesn't refer to a alloca instruction or constant."
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for store ?t0)
         ?i0 <- (object (is-a StoreInstruction) (Parent ?p) (ID ?t0))
         (object (is-a GetElementPointerInstruction) (ID ?target) 
                 (Operands ?a $?))
         (object (is-a ~AllocaInstruction&~Constant) (ID ?a))
         (object (is-a BasicBlock) (ID ?p) (Parent ?r))
         =>
         (modify-instance ?i0 (MemoryTarget UNKNOWN))
         (retract ?fct)
         (assert (element ?p writes to UNKNOWN)
                 (Element ?p has a MemoryBarrier)
                 (Element ?r has a MemoryBarrier)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithWriteTo-Alloca
         "Does a check to see if the load instruction refers directly to an
         AllocaInstruction or Constant. If it does then mark it as though the 
         block writes to it"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for store ?t0)
         ?i0 <- (object (is-a StoreInstruction) (ID ?t0) (Parent ?p))
         (object (is-a AllocaInstruction) (ID ?target))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?target))
         (assert (element ?p writes to ?target)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithWriteTo-Constant
         "Does a check to see if the store instruction refers directly to an
         AllocaInstruction or Constant. If it does then mark it as though the 
         block writes to it"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for store ?t0)
         ?i0 <- (object (is-a StoreInstruction) (ID ?t0) (Parent ?p))
         (object (is-a Constant) (ID ?target))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?target))
         (assert (element ?p writes to ?target)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithWriteTo-Single-Alloca
         "Does a check to see if the store instruction refers directly to an
         AllocaInstruction or Constant. If it does then mark it as though the 
         block writes to it"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for store ?t0)
         ?i0 <- (object (is-a StoreInstruction) (ID ?t0) (Parent ?p))
         (object (is-a AllocaInstruction) (ID ?target))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?target))
         (assert (element ?p writes to ?target)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithWriteTo-Single-Constant
         "Does a check to see if the store instruction refers directly to an
         AllocaInstruction or Constant. If it does then mark it as though the 
         block writes to it"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for store ?t0)
         ?i0 <- (object (is-a StoreInstruction) (ID ?t0) (Parent ?p))
         (object (is-a Constant) (ID ?target))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?target))
         (assert (element ?p writes to ?target)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithWriteTo-GetElementPointer-Alloca
         "Does a check to see if a given StoreInstruction referring to a
         GetElementPointerInstruction refers to an AllocaInstruction or 
         Constant. If it does then mark it in the WritesTo multifield"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for store ?t0)
         ?i0 <- (object (is-a StoreInstruction) (ID ?t0) (Parent ?p))
         (object (is-a GetElementPointerInstruction) (ID ?target) 
                 (Operands ?a $?))
         (object (is-a AllocaInstruction) (ID ?a))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?a))
         (assert (element ?p writes to ?a)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithWriteTo-GetElementPointer-Constant
         "Does a check to see if a given StoreInstruction referring to a
         GetElementPointerInstruction refers to an AllocaInstruction or 
         Constant. If it does then mark it in the WritesTo multifield"
         (declare (salience 4))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for store ?t0)
         ?i0 <- (object (is-a StoreInstruction) (ID ?t0) (Parent ?p))
         (object (is-a GetElementPointerInstruction) (ID ?target) 
                 (Operands ?a $?))
         (object (is-a Constant) (ID ?a))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget ?a))
         (assert (element ?p writes to ?a)))
;------------------------------------------------------------------------------
(defrule IdentifyGeneralStoreBarrier
         "Creates a store memory barrier hint if it turns out that the load 
         instruction in question refers to a register that isn't an 
         AllocaInstruction, GetElementPointerInstruction, or Constant."
         (declare (salience 3))
         (Stage Analysis $?)
         ?fct <- (Analyze ?target for store ?t0)
         ?i0 <- (object (is-a StoreInstruction) (ID ?t0) (Parent ?p))
         (object (is-a BasicBlock) (ID ?p) (Parent ?r))
         =>
         (retract ?fct)
         (modify-instance ?i0 (MemoryTarget UNKNOWN))
         (assert (element ?p writes to UNKNOWN)
                 (Element ?p has a MemoryBarrier)
                 (Element ?r has a MemoryBarrier)))
;------------------------------------------------------------------------------
(defrule MergeReadsFrom
         (Stage Analysis $?)
         ?f0 <- (element ?p reads from $?t0)
         ?f1 <- (element ?p reads from $?t1)
         (test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (element ?p reads from $?t0 $?t1)))
;------------------------------------------------------------------------------
(defrule MergeWritesTo
         (Stage Analysis $?)
         ?f0 <- (element ?p writes to $?t0)
         ?f1 <- (element ?p writes to $?t1)
         (test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (element ?p writes to $?t0 $?t1)))
;------------------------------------------------------------------------------
(defrule InsertIntoDiplomatReadsFrom-ParentDoesntExist
         (declare (salience -9))
         (Stage Analysis $?)
         ?fct <- (element ?p reads from $?t)
         ?bb <- (object (is-a Diplomat) (ID ?p) (Parent ?q))
         (not (exists (object (is-a Diplomat) (ID ?q))))
         =>
         (retract ?fct)
         (slot-insert$ ?bb ReadsFrom 1 ?t))
;------------------------------------------------------------------------------
(defrule InsertIntoDiplomatReadsFrom-ParentExists
         (declare (salience -9))
         (Stage Analysis $?)
         ?fct <- (element ?p reads from $?t)
         ?bb <- (object (is-a Diplomat) (ID ?p) (Parent ?q))
         (exists (object (is-a Diplomat) (ID ?q)))
         =>
         (retract ?fct)
         (assert (element ?q reads from ?t))
         (slot-insert$ ?bb ReadsFrom 1 ?t))
;------------------------------------------------------------------------------
(defrule InsertIntoDiplomatWritesTo-ParentDoesntExist
         (declare (salience -9))
         (Stage Analysis $?)
         ?fct <- (element ?p writes to $?t)
         ?bb <- (object (is-a Diplomat) (ID ?p) (Parent ?q))
         (not (exists (object (is-a Diplomat) (ID ?q))))
         =>
         (retract ?fct)
         (slot-insert$ ?bb WritesTo 1 ?t))
;------------------------------------------------------------------------------
(defrule InsertIntoDiplomatWritesTo-ParentExists
         (declare (salience -9))
         (Stage Analysis $?)
         ?fct <- (element ?p writes to $?t)
         ?bb <- (object (is-a Diplomat) (ID ?p) (Parent ?q))
         (exists (object (is-a Diplomat) (ID ?q)))
         =>
         (retract ?fct)
         (assert (element ?q writes to ?t))
         (slot-insert$ ?bb WritesTo 1 ?t))
;------------------------------------------------------------------------------
(defrule UpdateDiplomatHasMemoryBarrier
         (declare (salience -10))
         (Stage Analysis $?)
         ?fct <- (Element ?b has a MemoryBarrier)
         ?obj <- (object (is-a Diplomat) (ID ?b) (HasMemoryBarrier FALSE)
                         (Parent ?p))
         (exists (object (is-a Diplomat) (ID ?p)))
         =>
         (retract ?fct)
         (assert (Element ?p has a MemoryBarrier))
         (modify-instance ?obj (HasMemoryBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule RetractDiplomatHasMemoryBarrier
         (declare (salience -10))
         (Stage Analysis $?)
         ?fct <- (Element ?b has a MemoryBarrier)
         ?obj <- (object (is-a Diplomat) (ID ?b) (HasMemoryBarrier TRUE)
                         (Parent ?p))
         (exists (object (is-a Diplomat) (ID ?p)))
         =>
         (retract ?fct)
         (assert (Element ?p has a MemoryBarrier)))
;------------------------------------------------------------------------------
(defrule UpdateDiplomatHasMemoryBarrier-ParentDoesntExist
         (declare (salience -10))
         (Stage Analysis $?)
         ?fct <- (Element ?b has a MemoryBarrier)
         ?obj <- (object (is-a Diplomat) (ID ?b) (HasMemoryBarrier FALSE)
                         (Parent ?p))
         (not (exists (object (is-a Diplomat) (ID ?p))))
         =>
         (retract ?fct)
         (modify-instance ?obj (HasMemoryBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule RetractDiplomatHasMemoryBarrier-ParentDoesntExist
         (declare (salience -10))
         (Stage Analysis $?)
         ?fct <- (Element ?b has a MemoryBarrier)
         ?obj <- (object (is-a Diplomat) (ID ?b) (HasMemoryBarrier TRUE)
                         (Parent ?p))
         (not (exists (object (is-a Diplomat) (ID ?p))))
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
; All of the merge rules used in the analysis stages. Performs analysis to
; identify producers and consumers for all instructions in the provided set of
; scheduling material (regions, functions, etc).
;------------------------------------------------------------------------------
(defrule MergeConsumers
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Instruction ?a consumes ?id)
         ?f1 <- (Instruction ?b&~?a consumes ?id)
         =>
         (retract ?f0 ?f1)
         (assert (Instruction ?id consumed ?a ?b)))
;------------------------------------------------------------------------------
(defrule MergeProducers
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Instruction ?a produces ?id)
         ?f1 <- (Instruction ?b&~?a produces ?id)
         =>
         (retract ?f0 ?f1)
         (assert (Instruction ?id produced ?a ?b)))
;------------------------------------------------------------------------------
(defrule MergeConsumers-Multi
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Instruction ?id consumed $?a)
         ?f1 <- (Instruction ?id consumed $?b)
         (test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (Instruction ?id consumed $?a $?b)))
;------------------------------------------------------------------------------
(defrule MergeProducers-Multi
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Instruction ?id produced $?a)
         ?f1 <- (Instruction ?id produced $?b)
         (test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (Instruction ?id produced $?a $?b)))
;------------------------------------------------------------------------------
(defrule MergeConsumers-Only
         (declare (salience -2))
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Instruction ?a consumes ?b)
         =>
         (retract ?f0)
         (assert (Instruction ?b consumed ?a)))
;------------------------------------------------------------------------------
(defrule MergeProducers-Only
         (declare (salience -2))
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Instruction ?a produces ?b)
         =>
         (retract ?f0)
         (assert (Instruction ?b produced ?a)))
;------------------------------------------------------------------------------
(defrule InjectConsumers-Producers-And-LocalDependencies
         "Performs the actions of InjectConsumers and
         InjectProducersAndLocalDependencies in a single rule fire."
         (declare (salience 1))
         (Stage ExtendedMemoryAnalysis-Inject $?)
         ?f0 <- (Instruction ?id consumed $?t0)
         ?f1 <- (Instruction ?id produced $?t1)
         ?inst <- (object (is-a Instruction) (ID ?id) (Consumers $?c) 
                          (Producers $?p) (LocalDependencies $?ld))
         =>
         (retract ?f0 ?f1)
         (bind ?cs $?c)
         (bind ?ps $?p)
         (bind ?lds $?ld)
         (object-pattern-match-delay
         (progn$ (?target ?t0)
                 (if (not (member$ ?target ?cs)) then
                   (bind ?cs (insert$ ?cs 1 ?target))))
         (progn$ (?target ?t1)
                 (if (not (member$ ?target ?lds)) then
                   (bind ?lds (insert$ ?lds 1 ?target)))
                 (if (not (member$ ?target ?ps)) then
                   (bind ?ps (insert$ ?ps 1 ?target))))
         (modify-instance ?inst (Consumers ?cs) (Producers ?ps) 
                          (LocalDependencies ?lds))))
;------------------------------------------------------------------------------
(defrule InjectConsumers
         "Adds a given consumer to the target instruction"
         (Stage ExtendedMemoryAnalysis-Inject $?)
         ?fct <- (Instruction ?id consumed $?targets)
         ?inst <- (object (is-a Instruction) (ID ?id) (Consumers $?cs))
         =>
         (retract ?fct)
         (bind ?cons $?cs)
         (object-pattern-match-delay
         (progn$ (?target ?targets)
                 (if (not (member$ ?target ?cons)) then
                   (bind ?cons (insert$ ?cons 1 ?target))))
         (modify-instance ?inst (Consumers ?cons))))
;------------------------------------------------------------------------------
(defrule InjectProducersAndLocalDependencies
         "Adds a given producer to the target instruction."
         (Stage ExtendedMemoryAnalysis-Inject $?)
         ?fct <- (Instruction ?id produced $?targets)
         ?inst <- (object (is-a Instruction) (ID ?id) (Producers $?ps)
                          (LocalDependencies $?ld))
         =>
         (retract ?fct)
         (bind ?prods $?ps)
         (bind ?lds $?ld)
         (object-pattern-match-delay
         (progn$ (?target ?targets)
                 (if (not (member$ ?target ?lds)) then
                   (bind ?lds (insert$ ?lds 1 ?target)))
                 (if (not (member$ ?target ?prods)) then
                   (bind ?prods (insert$ ?prods 1 ?target))))
         (modify-instance ?inst (Producers ?prods) (LocalDependencies ?lds))))
;------------------------------------------------------------------------------
(defrule SetifyInstructionProducers
         (Stage ExtendedMemoryAnalysis-MakeSet $?)
         ?inst <- (object (is-a Instruction) (Producers $?a ?b $?c ?b $?d))
         =>
         (modify-instance ?inst (Producers $?a ?b $?c $?d)))
;------------------------------------------------------------------------------
(defrule SetifyInstructionConsumers
         (Stage ExtendedMemoryAnalysis-MakeSet $?)
         ?inst <- (object (is-a Instruction) (Consumers $?a ?b $?c ?b $?d))
         =>
         (modify-instance ?inst (Consumers $?a ?b $?c $?d)))
;------------------------------------------------------------------------------
(defrule SetifyLocalDependencies
         (Stage ExtendedMemoryAnalysis-MakeSet $?)
         ?inst <- (object (is-a Instruction) 
                          (LocalDependencies $?a ?b $?c ?b $?d))
         =>
         (modify-instance ?inst (LocalDependencies $?a ?b $?c $?d)))
;------------------------------------------------------------------------------
(defrule SetifyNonLocalDependencies
         (Stage ExtendedMemoryAnalysis-MakeSet $?)
         ?inst <- (object (is-a Instruction) 
                          (NonLocalDependencies $?a ?b $?c ?b $?d))
         =>
         (modify-instance ?inst (NonLocalDependencies $?a ?b $?c $?d)))
;------------------------------------------------------------------------------

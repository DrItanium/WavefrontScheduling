;Copyright (c) 2012, Joshua Scoggins 
;All rights reserved.
;
;Redistribution and use in source and binary forms, with or without
;modification, are permitted provided that the following conditions are met:
;    * Redistributions of source code must retain the above copyright
;      notice, this list of conditions and the following disclaimer.
;    * Redistributions in binary form must reproduce the above copyright
;      notice, this list of conditions and the following disclaimer in the
;      documentation and/or other materials provided with the distribution.
;    * Neither the name of Joshua Scoggins nor the
;      names of its contributors may be used to endorse or promote products
;      derived from this software without specific prior written permission.
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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; This stage is the actual act of scheduling the blocks on the wavefront. 
; The first step is to reacquire all dependencies of the given blocks by
; running the same rules as before. The only difference is that we have to do
; it specially for the blocks on the wavefront. 
; 
; I'm thinking of just copying the rules from the analysis pass to here. It
; would be a duplication but I frankly don't care anymore. 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defrule CreateDependencyAnalysisTargets
				 (declare (salience 10))
				 (Stage WavefrontSchedule $?)
				 (Substage DependencyAnalysis $?)
				 (object (is-a Wavefront) (Parent ?r) (Contents $? ?e $?))
				 (object (is-a BasicBlock) (ID ?e))
				 (object (is-a PathAggregate) (Parent ?e) (OriginalStopIndex ?si))
				 =>
				 ;only look at instructions starting at the original stop index. This
				 ;prevents unncessary recomputation
				 (assert (Evaluate ?e for dependencies starting at ?si)))
    
(defrule IdentifyWAR-Wavefront
				 "Identifies a WAR dependency between two instructions. It will not match if it
				 turns out the values are constant integers or constant floating point values"
				 (Stage WavefrontSchedule $?)
				 (Substage DependencyAnalysis $?)
				 (Evaluate ?p for dependencies starting at ?si)
				 ?i0 <- (object (is-a Instruction) (Parent ?p) (ID ?t0)
												(Operands $? ?c $?) (TimeIndex ?ti0))
				 (object (is-a TaggedObject&~ConstantInteger&~ConstantFloatingPoint) (ID ?c))
				 ?i1 <- (object (is-a Instruction) (Parent ?p) (ID ?t1)
												(TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?ti0 ?ti1)))
												(DestinationRegisters $? ?c $?))
				 =>
				 (assert (Instruction ?t1 consumes ?t0)
								 (Instruction ?t0 produces ?t1)))

(defrule IdentifyRAW-Wavefront
				 "Identifies a RAW dependency between two instructions in the same block. It
				 will not match if it turns out that the values are constant integers or
				 constant floating point values."
				 (Stage WavefrontSchedule $?)
				 (Substage DependencyAnalysis $?)
				 (Evaluate ?p for dependencies starting at ?si)
				 (object (is-a Instruction) (Parent ?p) (ID ?t0)
								 (DestinationRegisters $? ?c $?) (TimeIndex ?ti0))
				 (object (is-a TaggedObject&~ConstantInteger&~ConstantFloatingPoint) (ID ?c))
				 (object (is-a Instruction) (Parent ?p) (ID ?t1)
								 (Operands $? ?c $?) 
								 (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?ti0 ?ti1))))
				 =>
				 (assert (Instruction ?t1 consumes ?t0)
								 (Instruction ?t0 produces ?t1)))

(defrule IdentifyWAW-Wavefront
				 "Identifies a WAW dependency between two instructions in the same block. It
				 will not match if it turns out that the values are constant integers or
				 constant floating point values."
				 (Stage WavefrontSchedule $?)
				 (Substage DependencyAnalysis $?)
				 (Evaluate ?p for dependencies starting at ?si)
				 ?i0 <- (object (is-a Instruction) (Parent ?p) (ID ?t0)
												(DestinationRegisters $? ?c $?) (TimeIndex ?ti0))
				 (object (is-a TaggedObject&~ConstantInteger&~ConstantFloatingPoint) (ID ?c))
				 ?i1 <- (object (is-a Instruction) (Parent ?p) (ID ?t1) 
												(TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?ti0 ?ti1))) 
												(DestinationRegisters $? ?c $?))
				 =>
				 (assert (Instruction ?t1 consumes ?t0)
								 (Instruction ?t0 produces ?t1)))
;these call instruction checks only work for new instructions or those that
; dont have a call dependency. As that was the only way they got into the 
; block in the first place

(defrule MarkCallInstructionDependency-ModifiesMemory-Wavefront
				 "Creates a series of dependencies for all instructions following a call
				 instruction if it turns out that the call could modify memory."
				 (Stage WavefrontSchedule $?)
				 (Substage DependencyAnalysis $?)
				 (Evaluate ?p for dependencies starting at ?si)
				 (object (is-a CallInstruction) (ID ?name) (Parent ?p) 
								 (DoesNotAccessMemory FALSE) (OnlyReadsMemory FALSE) (MayWriteToMemory TRUE)
								 (TimeIndex ?t0))
				 (object (is-a Instruction) (Parent ?p) 
								 (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?t0 ?ti1)))
								 (HasCallDependency FALSE) (ID ?following))
				 =>
				 (assert (Instruction ?following has a CallDependency)
								 (Instruction ?following consumes ?name)
								 (Instruction ?name produces ?following)))

(defrule MarkCallInstructionDependency-InlineAsm-Wavefront
				 "Creates a series of dependencies for all instructions following a call
				 instruction if it turns out that the call is inline asm."
				 (Stage WavefrontSchedule $?)
				 (Substage DependencyAnalysis $?)
				 (Evaluate ?p for dependencies starting at ?si)
				 (object (is-a CallInstruction) (ID ?name) (Parent ?p) (IsInlineAsm TRUE)
								 (TimeIndex ?t0))
				 (object (is-a Instruction) (Parent ?p) 
								 (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?t0 ?ti1)))
								 (HasCallDependency FALSE) (ID ?following))
				 =>
				 (assert (Instruction ?following has a CallDependency)
								 (Instruction ?following consumes ?name)
								 (Instruction ?name produces ?following)))

(defrule MarkCallInstructionDependency-SideEffects-Wavefront
				 "Creates a series of dependencies for all instructions following a call
				 instruction if it turns out that the call is inline asm."
				 (Stage WavefrontSchedule $?)
				 (Substage DependencyAnalysis $?)
				 (Evaluate ?p for dependencies starting at ?si)
				 (object (is-a CallInstruction) (ID ?name) (Parent ?p) 
								 (MayHaveSideEffects TRUE) (MayWriteToMemory TRUE) 
								 (TimeIndex ?t0))
				 (object (is-a Instruction) (Parent ?p) 
								 (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?t0 ?ti1)))
								 (HasCallDependency FALSE) (ID ?following))
				 =>
				 (assert (Instruction ?following has a CallDependency)
								 (Instruction ?following consumes ?name)
								 (Instruction ?name produces ?following)))
(defrule MarkNonLocalDependencies-Wavefront
				 (Stage WavefrontSchedule $?)
				 (Substage DependencyAnalysis $?)
				 (Evaluate ?p for dependencies starting at ?si)
				 ?inst <- (object (is-a Instruction) (Parent ?p) (TimeIndex ?t&:(>= ?t ?si))
													(Operands $? ?o $?))
				 (object (is-a Instruction) (ID ?o) (Parent ~?p))
				 =>
				 (slot-insert$ ?inst NonLocalDependencies 1 ?o))

(defrule Wavefront-MarkHasCallDependency
				 (declare (salience -2))
				 (Stage WavefrontSchedule $?)
				 (Substage DependencyAnalysis $?)
				 ?fct <- (Instruction ?f has a CallDependency)
				 ?obj <- (object (is-a Instruction) (ID ?f))
				 =>
				 (modify-instance ?obj (HasCallDependency TRUE))
				 (retract ?fct))

(defrule InjectConsumers-Wavefront
				 "Adds a given consumer to the target instruction"
				 (declare (salience -5))
				 (Stage WavefrontSchedule $?)
				 (Substage DependencyAnalysis $?)
				 ?fct <- (Instruction ?target consumes ?id)
				 ?inst <- (object (is-a Instruction) (ID ?id))
				 =>
				 (retract ?fct)
				 (if (eq FALSE (member$ ?target (send ?inst get-Consumers))) then 
					 (slot-insert$ ?inst Consumers 1 ?target)))

(defrule InjectProducers-Wavefront
				 "Adds a given producer to the target instruction"
				 (declare (salience -5))
				 (Stage WavefrontSchedule $?)
				 (Substage DependencyAnalysis $?)
				 ?fct <- (Instruction ?target produces ?id)
				 ?inst <- (object (is-a Instruction) (ID ?id))
				 =>
				 (retract ?fct)
				 (if (eq FALSE (member$ ?target (send ?inst get-LocalDependencies))) then
					 (slot-insert$ ?inst LocalDependencies 1 ?target))
				 (if (eq FALSE (member$ ?target (send ?inst get-Producers))) then 
					 (slot-insert$ ?inst Producers 1 ?target)))

(defrule StoreToLoadDependency-Wavefront
				 (Stage WavefrontSchedule $?)
				 (Substage DependencyAnalysis $?)
				 (Evaluate ?p for dependencies starting at ?si)
				 (object (is-a StoreInstruction) (Parent ?p) (ID ?t0)
								 (TimeIndex ?ti0) (MemoryTarget ?sym0))
				 (object (is-a LoadInstruction) (Parent ?p) (ID ?t1) 
								 (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?ti0 ?ti1)))
								 (MemoryTarget ?sym1))
				 (test (or (eq ?sym0 ?sym1) (eq ?sym0 UNKNOWN)))
				 =>
				 (assert (Instruction ?t1 consumes ?t0)
								 (Instruction ?t0 produces ?t1)))

(defrule StoreToStoreDependency-Wavefront
				 (Stage WavefrontSchedule $?)
				 (Substage DependencyAnalysis $?)
				 (Evaluate ?p for dependencies starting at ?si)
				 (object (is-a StoreInstruction) (Parent ?p) (ID ?t0)
								 (TimeIndex ?ti0) (MemoryTarget ?sym0))
				 (object (is-a StoreInstruction) (Parent ?p) (ID ?t1) 
								 (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?ti0 ?ti1)))
								 (MemoryTarget ?sym1))
				 (test (or (eq ?sym0 ?sym1) (eq ?sym0 UNKNOWN)))
				 =>
				 (assert (Instruction ?t1 consumes ?t0)
								 (Instruction ?t0 produces ?t1)))

(defrule LoadToStoreDependency-Wavefront
				 (Stage WavefrontSchedule $?)
				 (Substage DependencyAnalysis $?)
				 (Evaluate ?p for dependencies starting at ?si)
				 (object (is-a LoadInstruction) (Parent ?p) (ID ?t0)
								 (TimeIndex ?ti0) (MemoryTarget ?sym0)) 
				 (object (is-a StoreInstruction) (Parent ?p) (ID ?t1) 
								 (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?ti0 ?ti1)))
								 (MemoryTarget ?sym1))
				 (test (or (eq ?sym0 ?sym1) (eq ?sym0 UNKNOWN)))
				 =>
				 (assert (Instruction ?t1 consumes ?t0)
								 (Instruction ?t0 produces ?t1)))


(defrule FinishedDependencyAnalysis 
				 (declare (salience -800))
				 (Stage WavefrontSchedule $?)
				 (Substage DependencyAnalysis $?)
				 ?fct <- (Evaluate ?p for dependencies starting at ?v)
				 (object (is-a BasicBlock) (ID ?p) (Parent ?r))
				 =>
				 (assert (Schedule ?p for ?r))
				 (retract ?fct))

(defrule RemoveInstructionsFromProducers
				 (declare (salience 768))
				 (Stage WavefrontSchedule $?)
				 (Substage MergeUpdate $?)
				 ?fct <- (Remove evidence of ?tInst from instructions ?inst $?insts)
				 ?iObj <- (object (is-a Instruction) (ID ?inst) (Producers $?pb ?tInst $?pa)
													(LocalDependencies $?ldb ?tInst $?lda))
				 =>
				 (retract ?fct)
				 (assert (Remove evidence of ?tInst from instructions $?insts))
				 (modify-instance ?iObj (Producers $?pb $?pa)
													(LocalDependencies $?ldb $?lda))
				 (slot-insert$ ?iObj NonLocalDependencies 1 ?tInst))

(defrule RetractRemoveInstructionsFromProducers
				 (declare (salience 768))
				 (Stage WavefrontSchedule $?)
				 (Substage MergeUpdate $?)
				 ?fct <- (Remove evidence of ? from instructions)
				 =>
				 (retract ?fct))

(defrule StartRecomputeBlock
				 (declare (salience 100))
				 (Stage WavefrontSchedule $?)
				 (Substage MergeUpdate $?)
				 ?fct <- (Recompute block ?b)
				 ?bb <- (object (is-a BasicBlock) (ID ?b) (Contents $?instructions ?last))
				 (object (is-a TerminatorInstruction) (ID ?last))
				 =>
				 (modify-instance ?bb (ReadsFrom) (WritesTo) (HasMemoryBarrier FALSE))
				 (retract ?fct)
				 (assert (Recompute block ?b with instructions $?instructions)))

(defrule RecomputeNonMemoryInstructionForBlock
				 (declare (salience 99))
				 (Stage WavefrontSchedule $?)
				 (Substage MergeUpdate $?)
				 ?fct <- (Recompute block ?b with instructions ?inst $?rest)
				 (object (is-a BasicBlock) (ID ?b))
				 (object (is-a Instruction&~LoadInstruction&~StoreInstruction) 
													(ID ?inst) (Parent ?b))
				 =>
				 (retract ?fct)
				 (assert (Recompute block ?b with instructions $?rest)))

(defrule RecomputeLoadInstructionForBlock
				 (declare (salience 99))
				 (Stage WavefrontSchedule $?)
				 (Substage MergeUpdate $?)
				 ?fct <- (Recompute block ?b with instructions ?inst $?rest)
				 (object (is-a LoadInstruction) (ID ?inst) (Parent ?b) 
								 (MemoryTarget ?mt)) 
				 ?bb <- (object (is-a BasicBlock) (ID ?b))
				 =>
				 (if (eq FALSE (member$ ?mt (send ?bb get-ReadsFrom))) then
					 (slot-insert$ ?bb ReadsFrom 1 ?mt))
				 (retract ?fct)
				 (assert (Recompute block ?b with instructions $?rest)))

(defrule RecomputeStoreInstructionForBlock
				 (declare (salience 99))
				 (Stage WavefrontSchedule $?)
				 (Substage MergeUpdate $?)
				 ?fct <- (Recompute block ?b with instructions ?inst $?rest)
				 (object (is-a StoreInstruction) (ID ?inst) (Parent ?b) 
								 (MemoryTarget ?mt))
				 ?bb <- (object (is-a BasicBlock) (ID ?b))
				 =>
				 (if (eq FALSE (member$ ?mt (send ?bb get-WritesTo))) then
					 (slot-insert$ ?bb WritesTo 1 ?mt))
				 (retract ?fct)
				 (assert (Recompute block ?b with instructions $?rest)))

(defrule FinishRecomputationForBlock
				 (declare (salience 98))
				 (Stage WavefrontSchedule $?)
				 (Substage MergeUpdate $?)
				 ?fct <- (Recompute block ?b with instructions)
				 ?bb <- (object (is-a BasicBlock) (ID ?b) (ReadsFrom $?rf)
												(WritesTo $?wt))
				 =>
				 (retract ?fct)
				 (if (or (neq FALSE (member$ UNKNOWN ?rf))
								 (neq FALSE (member$ UNKNOWN ?wt))) then
					 (modify-instance ?bb (HasMemoryBarrier TRUE))))

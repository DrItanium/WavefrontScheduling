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
; MemoryBarrierCreation.clp - Contains rules pertaining to the creation of
; memory barriers to prevent loads and stores from being moved above a specific
; point within the program during the act of scheduling.
; Written by Joshua Scoggins (7/1/2012)
;------------------------------------------------------------------------------
; Barriers consist of reads and writes that can't be verified as to their exact
; source. 
;------------------------------------------------------------------------------
; TODO: Put in a field for load and store instructions that describes what
; is being referenced. By default this slot is UNKNOWN.
(defrule AssertLoadBarrierEvaluation
				 "Creates a fact that tells the system to analyze the given load instruction to
				 see if it is necessary to create a memory barrier for the given instruction"
				 (declare (salience 5))
				 (Stage Analysis $?)
				 (object (is-a LoadInstruction) (ID ?t0) (SourceRegisters ?target $?))
				 =>
				 (assert (Analyze ?target for load ?t0)))
;------------------------------------------------------------------------------
(defrule AssertStoreBarrierEvaluation
				 "Creates a fact that tells the system to analyze the given load instruction to
				 see if it is necessary to create a memory barrier for the given instruction"
				 (declare (salience 5))
				 (Stage Analysis $?)
				 (object (is-a StoreInstruction) (ID ?t0) (DestinationRegisters ?target))
				 =>
				 ;(printout t "Looking at " ?t0 " which has destination registers "
				 ; ?target crlf)
				 (assert (Analyze ?target for store ?t0)))
;------------------------------------------------------------------------------
(defrule IdentifyGetElementPointerLoadBarrier
				 "Creates a load memory barrier hint if it turns out that the load instruction
				 refers to a getelementptr instruction but that getelementptr doesn't refer to
				 a alloca instruction or constant."
				 (declare (salience 4))
				 (Stage Analysis $?)
				 ?fct <- (Analyze ?target for load ?t0)
				 (object (is-a LoadInstruction) (ID ?t0) (Parent ?p))
				 (object (is-a GetElementPointerInstruction) (ID ?target) (SourceRegisters ?a $?))
				 (object (is-a ~AllocaInstruction&~Constant) (ID ?a))
				 (object (is-a BasicBlock) (ID ?p) (Parent ?r))
				 =>
				 (retract ?fct)
				 (assert (block ?p reads from UNKNOWN)
								 (instruction ?t0 memory target UNKNOWN)
								 (Block ?p has a MemoryBarrier)
								 (Region ?r has a MemoryBarrier)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithReadFrom-Alloca
				 "Does a check to see if the load instruction refers directly to an
				 AllocaInstruction or Constant. If it does then mark it as though the block
				 reads from it"
				 (declare (salience 4))
				 (Stage Analysis $?)
				 ?fct <- (Analyze ?target for load ?t0)
				 (object (is-a LoadInstruction) (ID ?t0) (Parent ?p))
				 (object (is-a AllocaInstruction) (ID ?target))
				 =>
				 (retract ?fct)
				 (assert (instruction ?t0 memory target ?target)
								 (block ?p reads from ?target)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithReadFrom-Constant
				 "Does a check to see if the load instruction refers directly to an
				 AllocaInstruction or Constant. If it does then mark it as though the block
				 reads from it"
				 (declare (salience 4))
				 (Stage Analysis $?)
				 ?fct <- (Analyze ?target for load ?t0)
				 (object (is-a LoadInstruction) (ID ?t0) (Parent ?p))
				 (object (is-a Constant) (ID ?target))
				 =>
				 (retract ?fct)
				 (assert (instruction ?t0 memory target ?target)
								 (block ?p reads from ?target)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithReadFrom-GetElementPointer-Alloca
				 "Does a check to see if a given LoadInstruction referring to a
				 GetElementPointerInstruction refers to an AllocaInstruction or Constant. If it
				 does then mark it in the ReadsFrom multifield"
				 (declare (salience 4))
				 (Stage Analysis $?)
				 ?fct <- (Analyze ?target for load ?t0)
				 (object (is-a LoadInstruction) (ID ?t0) (Parent ?p))
				 (object (is-a GetElementPointerInstruction) (ID ?target) (SourceRegisters ?a $?))
				 (object (is-a AllocaInstruction) (ID ?a))
				 =>
				 (retract ?fct)
				 (assert (instruction ?t0 memory target ?a)
								 (block ?p reads from ?a)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithReadFrom-GetElementPointer-Constant
				 "Does a check to see if a given LoadInstruction referring to a
				 GetElementPointerInstruction refers to an AllocaInstruction or Constant. If it
				 does then mark it in the ReadsFrom multifield"
				 (declare (salience 4))
				 (Stage Analysis $?)
				 ?fct <- (Analyze ?target for load ?t0)
				 (object (is-a LoadInstruction) (ID ?t0) (Parent ?p))
				 (object (is-a GetElementPointerInstruction) (ID ?target) (SourceRegisters ?a $?))
				 (object (is-a Constant) (ID ?a))
				 =>
				 (retract ?fct)
				 (assert (instruction ?t0 memory target ?a)
								 (block ?p reads from ?a)))
;------------------------------------------------------------------------------
(defrule IdentifyGeneralLoadBarrier
				 "Creates a load memory barrier hint if it turns out that the load instruction
				 in question refers to a register that isn't an AllocaInstruction,
				 GetElementPointerInstruction, or Constant."
				 (declare (salience 3))
				 (Stage Analysis $?)
				 ?fct <- (Analyze ?target for load ?t0)
				 (object (is-a LoadInstruction) (ID ?t0) (Parent ?p))
				 (object (is-a BasicBlock) (ID ?p) (Parent ?r))
				 =>
				 (retract ?fct)
				 (assert (instruction ?t0 memory target UNKNOWN)
								 (block ?p reads from UNKNOWN)
								 (Block ?p has a MemoryBarrier)
								 (Region ?r has a MemoryBarrier)))
;------------------------------------------------------------------------------
(defrule IdentifyGetElementPointerStoreBarrier
				 "Creates a load memory barrier hint if it turns out that the load instruction
				 refers to a getelementptr instruction but that getelementptr doesn't refer to
				 a alloca instruction or constant."
				 (declare (salience 4))
				 (Stage Analysis $?)
				 ?fct <- (Analyze ?target for store ?t0)
				 (object (is-a StoreInstruction) (Parent ?p) (ID ?t0))
				 (object (is-a GetElementPointerInstruction) (ID ?target) 
								 (SourceRegisters ?a $?))
				 (object (is-a ~AllocaInstruction&~Constant) (ID ?a))
				 (object (is-a BasicBlock) (ID ?p) (Parent ?r))
				 =>
				 (retract ?fct)
				 (assert (instruction ?t0 memory target UNKNOWN)
								 (block ?p writes to UNKNOWN)
								 (Block ?p has a MemoryBarrier)
								 (Region ?r has a MemoryBarrier)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithWriteTo-Alloca
				 "Does a check to see if the load instruction refers directly to an
				 AllocaInstruction or Constant. If it does then mark it as though the block
				 reads from it"
				 (declare (salience 4))
				 (Stage Analysis $?)
				 ?fct <- (Analyze ?target for store ?t0)
				 (object (is-a StoreInstruction) (ID ?t0) (Parent ?p))
				 (object (is-a AllocaInstruction) (ID ?target))
				 =>
				 ;(printout t ?t0 " has target " ?target crlf)
				 ;(printout t "(assert (instruction " ?t0 " memory target " ?a "))"
				 ; crlf)
				 (retract ?fct)
				 (assert (instruction ?t0 memory target ?target)
								 (block ?p writes to ?target)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithWriteTo-Constant
				 "Does a check to see if the load instruction refers directly to an
				 AllocaInstruction or Constant. If it does then mark it as though the block
				 reads from it"
				 (declare (salience 4))
				 (Stage Analysis $?)
				 ?fct <- (Analyze ?target for store ?t0)
				 (object (is-a StoreInstruction) (ID ?t0) (Parent ?p))
				 (object (is-a Constant) (ID ?target))
				 =>
				 ;(printout t ?t0 " has target " ?target crlf)
				 (retract ?fct)
				 ;(printout t "(assert (instruction " ?t0 " memory target " ?a "))"
				 ; crlf)
				 (assert (instruction ?t0 memory target ?target)
								 (block ?p writes to ?target)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithWriteTo-Single-Alloca
				 "Does a check to see if the load instruction refers directly to an
				 AllocaInstruction or Constant. If it does then mark it as though the block
				 reads from it"
				 (declare (salience 4))
				 (Stage Analysis $?)
				 ?fct <- (Analyze ?target for store ?t0)
				 (object (is-a StoreInstruction) (ID ?t0) (Parent ?p))
				 (object (is-a AllocaInstruction) (ID ?target))
				 =>
				 ; (printout t ?t0 " has target " ?target crlf)
				 (retract ?fct)
				 (assert (instruction ?t0 memory target ?target)
								 (block ?p writes to ?target)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithWriteTo-Single-Constant
				 "Does a check to see if the load instruction refers directly to an
				 AllocaInstruction or Constant. If it does then mark it as though the block
				 reads from it"
				 (declare (salience 4))
				 (Stage Analysis $?)
				 ?fct <- (Analyze ?target for store ?t0)
				 (object (is-a StoreInstruction) (ID ?t0) (Parent ?p))
				 (object (is-a Constant) (ID ?target))
				 =>
				 ;(printout t ?t0 " has target " ?target crlf)
				 (retract ?fct)
				 (assert (instruction ?t0 memory target ?target)
								 (block ?p writes to ?target)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithWriteTo-GetElementPointer-Alloca
				 "Does a check to see if a given StoreInstruction referring to a
				 GetElementPointerInstruction refers to an AllocaInstruction or Constant. If it
				 does then mark it in the ReadsFrom multifield"
				 (declare (salience 4))
				 (Stage Analysis $?)
				 ?fct <- (Analyze ?target for store ?t0)
				 (object (is-a StoreInstruction) (ID ?t0) (Parent ?p))
				 (object (is-a GetElementPointerInstruction) (ID ?target) 
								 (SourceRegisters ?a $?))
				 (object (is-a AllocaInstruction) (ID ?a))
				 =>
				 ;(printout t ?t0 " has target " ?target crlf)
				 (retract ?fct)
				 (assert (instruction ?t0 memory target ?a)
								 (block ?p writes to ?a)))
;------------------------------------------------------------------------------
(defrule PopulateBasicBlockWithWriteTo-GetElementPointer-Constant
				 "Does a check to see if a given StoreInstruction referring to a
				 GetElementPointerInstruction refers to an AllocaInstruction or Constant. If it
				 does then mark it in the ReadsFrom multifield"
				 (declare (salience 4))
				 (Stage Analysis $?)
				 ?fct <- (Analyze ?target for store ?t0)
				 (object (is-a StoreInstruction) (ID ?t0) (Parent ?p))
				 (object (is-a GetElementPointerInstruction) (ID ?target) 
								 (SourceRegisters ?a $?))
				 (object (is-a Constant) (ID ?a))
				 =>
				 ;(printout t ?t0 " has target " ?target crlf)
				 (retract ?fct)
				 (assert (instruction ?t0 memory target ?a)
								 (block ?p writes to ?a)))
;------------------------------------------------------------------------------
(defrule IdentifyGeneralStoreBarrier
				 "Creates a load memory barrier hint if it turns out that the load instruction
				 in question refers to a register that isn't an AllocaInstruction,
				 GetElementPointerInstruction, or Constant."
				 (declare (salience 3))
				 (Stage Analysis $?)
				 ?fct <- (Analyze ?target for store ?t0)
				 (object (is-a StoreInstruction) (ID ?t0) (Parent ?p))
				 (object (is-a BasicBlock) (ID ?p) (Parent ?r))
				 =>
				 (retract ?fct)
				 (assert (block ?p writes to UNKNOWN)
								 (instruction ?t0 memory target UNKNOWN)
								 (Block ?p has a MemoryBarrier)
								 (Region ?r has a MemoryBarrier)))
;------------------------------------------------------------------------------
(defrule InsertIntoBlockReadsFrom-ParentDoesntExist
				 "Puts the target value into the target basic block's ReadsFrom multifield"
				 (declare (salience -9))
				 (Stage Analysis $?)
				 ?fct <- (block ?p reads from ?t)
				 ?bb <- (object (is-a BasicBlock) (ID ?p) (Parent ?q))
				 (not (exists (object (is-a Region) (ID ?q))))
				 =>
				 (retract ?fct)
				 (slot-insert$ ?bb ReadsFrom 1 ?t))
;------------------------------------------------------------------------------
(defrule InsertIntoBlockReadsFrom
				 "Puts the target value into the target basic block's ReadsFrom multifield"
				 (declare (salience -9))
				 (Stage Analysis $?)
				 ?fct <- (block ?p reads from ?t)
				 ?bb <- (object (is-a BasicBlock) (ID ?p) (Parent ?q))
				 (exists (object (is-a Region) (ID ?q)))
				 =>
				 (retract ?fct)
				 (assert (Region ?q reads from ?t))
				 (slot-insert$ ?bb ReadsFrom 1 ?t))
;------------------------------------------------------------------------------
(defrule InsertIntoBlockWritesTo-ParentDoesntExist
				 "Puts the target value into the target basic block's ReadsFrom multifield"
				 (declare (salience -9))
				 (Stage Analysis $?)
				 ?fct <- (block ?p writes to ?t)
				 ?bb <- (object (is-a BasicBlock) (ID ?p) (Parent ?q))
				 (not (exists (object (is-a Region) (ID ?q))))
				 =>
				 (retract ?fct)
				 (slot-insert$ ?bb WritesTo 1 ?t))
;------------------------------------------------------------------------------
(defrule InsertIntoBlockWritesTo
				 "Puts the target value into the target basic block's ReadsFrom multifield"
				 (declare (salience -9))
				 (Stage Analysis $?)
				 ?fct <- (block ?p writes to ?t)
				 ?bb <- (object (is-a BasicBlock) (ID ?p) (Parent ?q))
				 (exists (object (is-a Region) (ID ?q)))
				 =>
				 (retract ?fct)
				 (assert (Region ?q writes to ?t))
				 (slot-insert$ ?bb WritesTo 1 ?t))
;------------------------------------------------------------------------------
(defrule InsertIntoRegionReadsFrom-ParentDoesntExist
				 "Puts the target value into the target basic block's ReadsFrom multifield"
				 (declare (salience -9))
				 (Stage Analysis $?)
				 ?fct <- (Region ?p reads from ?t)
				 ?bb <- (object (is-a Region) (ID ?p) (Parent ?q))
				 (not (exists (object (is-a Region) (ID ?q))))
				 =>
				 (retract ?fct)
				 (slot-insert$ ?bb ReadsFrom 1 ?t))
;------------------------------------------------------------------------------
(defrule InsertIntoRegionReadsFrom
				 "Puts the target value into the target basic block's ReadsFrom multifield"
				 (declare (salience -9))
				 (Stage Analysis $?)
				 ?fct <- (Region ?p reads from ?t)
				 ?bb <- (object (is-a Region) (ID ?p) (Parent ?q))
				 (exists (object (is-a Region) (ID ?q)))
				 =>
				 (retract ?fct)
				 (assert (Region ?q reads from ?t))
				 (slot-insert$ ?bb ReadsFrom 1 ?t))
;------------------------------------------------------------------------------
(defrule InsertIntoRegionWritesTo-ParentDoesntExist
				 "Puts the target value into the target basic block's ReadsFrom multifield"
				 (declare (salience -9))
				 (Stage Analysis $?)
				 ?fct <- (Region ?p writes to ?t)
				 ?bb <- (object (is-a Region) (ID ?p) (Parent ?q))
				 (not (exists (object (is-a Region) (ID ?q))))
				 =>
				 (retract ?fct)
				 (slot-insert$ ?bb WritesTo 1 ?t))
;------------------------------------------------------------------------------
(defrule InsertIntoRegionWritesTo
				 "Puts the target value into the target basic block's ReadsFrom multifield"
				 (declare (salience -9))
				 (Stage Analysis $?)
				 ?fct <- (Region ?p writes to ?t)
				 ?bb <- (object (is-a Region) (ID ?p) (Parent ?q))
				 (exists (object (is-a Region) (ID ?q)))
				 =>
				 (retract ?fct)
				 (assert (Region ?q writes to ?t))
				 (slot-insert$ ?bb WritesTo 1 ?t))
;------------------------------------------------------------------------------
(defrule UpdateBlockHasMemoryBarrier
				 (declare (salience -10))
				 (Stage Analysis $?)
				 ?fct <- (Block ?b has a MemoryBarrier)
				 ?obj <- (object (is-a BasicBlock) (ID ?b) (HasMemoryBarrier FALSE) (Parent ?p))
				 (exists (object (is-a Region) (ID ?p)))
				 =>
				 (retract ?fct)
				 (assert (Region ?p has a MemoryBarrier))
				 (modify-instance ?obj (HasMemoryBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule RetractBlockHasMemoryBarrier
				 (declare (salience -10))
				 (Stage Analysis $?)
				 ?fct <- (Block ?b has a MemoryBarrier)
				 ?obj <- (object (is-a BasicBlock) (ID ?b) (HasMemoryBarrier TRUE) (Parent ?p))
				 (exists (object (is-a Region) (ID ?p)))
				 =>
				 (assert (Region ?p has a MemoryBarrier))
				 (retract ?fct))
;------------------------------------------------------------------------------
(defrule UpdateBlockHasMemoryBarrier-ParentIsntObject
				 (declare (salience -10))
				 (Stage Analysis $?)
				 ?fct <- (Block ?b has a MemoryBarrier)
				 ?obj <- (object (is-a BasicBlock) (ID ?b) (HasMemoryBarrier FALSE) 
												 (Parent ?p))
				 (not (exists (object (is-a Region) (ID ?p))))
				 =>
				 (retract ?fct)
				 (modify-instance ?obj (HasMemoryBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule RetractBlockHasMemoryBarrier-ParentIsntObject
				 (declare (salience -10))
				 (Stage Analysis $?)
				 ?fct <- (Block ?b has a MemoryBarrier)
				 ?obj <- (object (is-a BasicBlock) (ID ?b) (HasMemoryBarrier TRUE) (Parent ?p))
				 (not (exists (object (is-a Region) (ID ?p))))
				 =>
				 (retract ?fct))
;------------------------------------------------------------------------------
(defrule UpdateRegionHasMemoryBarrier
				 (declare (salience -10))
				 (Stage Analysis $?)
				 ?fct <- (Region ?b has a MemoryBarrier)
				 ?obj <- (object (is-a Region) (ID ?b) (HasMemoryBarrier FALSE) (Parent ?p))
				 (exists (object (is-a Region) (ID ?p)))
				 =>
				 (retract ?fct)
				 (assert (Region ?p has a MemoryBarrier))
				 (modify-instance ?obj (HasMemoryBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule RetractRegionHasMemoryBarrier
				 (declare (salience -10))
				 (Stage Analysis $?)
				 ?fct <- (Region ?b has a MemoryBarrier)
				 ?obj <- (object (is-a Region) (ID ?b) (HasMemoryBarrier TRUE) (Parent ?p))
				 (exists (object (is-a Region) (ID ?p)))
				 =>
				 (assert (Region ?p has a MemoryBarrier))
				 (retract ?fct))
;------------------------------------------------------------------------------
(defrule UpdateRegionHasMemoryBarrier-ParentIsntObject
				 (declare (salience -10))
				 (Stage Analysis $?)
				 ?fct <- (Region ?b has a MemoryBarrier)
				 ?obj <- (object (is-a Region) (ID ?b) (HasMemoryBarrier FALSE) (Parent ?p))
				 (not (exists (object (is-a Region) (ID ?p))))
				 =>
				 (retract ?fct)
				 (modify-instance ?obj (HasMemoryBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule RetractRegionHasMemoryBarrier-ParentIsntObject
				 (declare (salience -10))
				 (Stage Analysis $?)
				 ?fct <- (Region ?b has a MemoryBarrier)
				 ?obj <- (object (is-a Region) (ID ?b) (HasMemoryBarrier TRUE) (Parent ?p))
				 (not (exists (object (is-a Region) (ID ?p))))
				 =>
				 (retract ?fct))
;------------------------------------------------------------------------------
(defrule SetMemoryTargetForInstruction
				 (declare (salience -10))
				 (Stage Analysis $?)
				 ?fct <- (instruction ?t0 memory target ?target)
				 ?obj <- (object (is-a Instruction) (ID ?t0))
				 =>
				 (retract ?fct)
				 (modify-instance ?obj (MemoryTarget ?target)))
;------------------------------------------------------------------------------

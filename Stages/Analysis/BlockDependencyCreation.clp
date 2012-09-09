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
; BlockDependencyCreation.clp - Contains rules pertaining to the creation of
; data dependencies between different instructions inside of a basic block
; Written by Joshua Scoggins (7/1/2012)
;------------------------------------------------------------------------------
(defrule MarkLocalDependency 
         (Stage Analysis $?)
         ?i0 <- (object (is-a Instruction) (Parent ?p) (ID ?t0) 
           (Operands $? ?o $?))
         (object (is-a Instruction) (ID ?o) (Parent ?p))
         =>
         (assert (Instruction ?o produces ?t0)
                 (Instruction ?t0 consumes ?o)))
;------------------------------------------------------------------------------
(defrule MarkInstructionsThatHappenBeforeCall-WritesToMemory
 (Stage Analysis $?)
 (object (is-a BasicBlock) (ID ?v) (Contents $?before ?n0 $?))
 (object (is-a CallInstruction) (ID ?n0) (Parent ?v) (MayWriteToMemory TRUE))
 =>
 (foreach ?n1 ?before
  (assert (Instruction ?n0 consumes ?n1)
          (Instruction ?n1 produces ?n0))))
;------------------------------------------------------------------------------
(defrule MarkInstructionsThatHappenBeforeCall-HasSideEffects
         (Stage Analysis $?)
         (object (is-a BasicBlock) (ID ?p) (Contents $?a ?n0 $?))
         (object (is-a CallInstruction) (ID ?n0) (Parent ?p)
                 (MayHaveSideEffects TRUE))
         =>
         (foreach ?n1 ?a
         (assert (Instruction ?n0 consumes ?n1)
                 (Instruction ?n1 produces ?n0))))
;------------------------------------------------------------------------------
(defrule MarkCallInstructionDependency-ModifiesMemory
         "Creates a series of dependencies for all instructions following a call
         instruction if it turns out that the call could modify memory."
         (Stage Analysis $?)
         (object (is-a BasicBlock) (ID ?p) (Contents $? ?name $?rest))
         (object (is-a CallInstruction) (ID ?name) (Parent ?p)
          (MayWriteToMemory TRUE))
         =>
         (assert (Block ?p has a CallBarrier))
         (foreach ?following ?rest
                  (assert (Instruction ?following has a CallDependency)
                          ;(Instruction ?following consumes ?name)
                          (Instruction ?name produces ?following))))
;------------------------------------------------------------------------------
(defrule MarkCallInstructionDependency-InlineAsm
         "Creates a series of dependencies for all instructions following a call
         instruction if it turns out that the call is inline asm."
         (Stage Analysis $?)
         (object (is-a BasicBlock) (ID ?p) (Contents $? ?name $?rest))
         (object (is-a CallInstruction) (ID ?name) (Parent ?p) (IsInlineAsm TRUE))
         =>
         (assert (Block ?p has a CallBarrier))
         (foreach ?following ?rest
                  (assert (Instruction ?following has a CallDependency)
                          ;(Instruction ?following consumes ?name)
                          (Instruction ?name produces ?following))))
;------------------------------------------------------------------------------
(defrule MarkCallInstructionDependency-SideEffects
         "Creates a series of dependencies for all instructions following a call
         instruction if it turns out that the call is inline asm."
         (Stage Analysis $?)
         (object (is-a CallInstruction) (ID ?name) (Parent ?p)
                 (MayHaveSideEffects TRUE)) 
         (object (is-a BasicBlock) (ID ?p) (Contents $? ?name $?rest))
         =>
         (assert (Block ?p has a CallBarrier))
         (foreach ?following ?rest
                  (assert (Instruction ?following has a CallDependency)
                          ;(Instruction ?following consumes ?name)
                          (Instruction ?name produces ?following))))
;------------------------------------------------------------------------------
(defrule MergeConsumers
				 (declare (salience -2))
				 (Stage Analysis $?)
				 ?f0 <- (Instruction ?a consumes ?id)
				 ?f1 <- (Instruction ?b consumes ?id)
				 (test (neq ?f0 ?f1))
				 =>
				 (retract ?f0 ?f1)
				 (assert (Instruction ?id is consumed by ?a ?b)))

(defrule MergeProducers
				 (declare (salience -2))
				 (Stage Analysis $?)
				 ?f0 <- (Instruction ?a produces ?id)
				 ?f1 <- (Instruction ?b produces ?id)
				 (test (neq ?f0 ?f1))
				 =>
				 (retract ?f0 ?f1)
				 (assert (Instruction ?id is produced by ?a ?b)))

(defrule MergeConsumers-Multi
				 (declare (salience -2))
				 (Stage Analysis $?)
				 ?f0 <- (Instruction ?id is consumed by $?a)
				 ?f1 <- (Instruction ?id is consumed by $?b)
				 (test (neq ?f0 ?f1))
				 =>
				 (retract ?f0 ?f1)
				 (assert (Instruction ?id is consumed by $?a $?b)))

(defrule MergeProducers-Multi
				 (declare (salience -2))
				 (Stage Analysis $?)
				 ?f0 <- (Instruction ?id is produced by $?a)
				 ?f1 <- (Instruction ?id is produced by $?b)
				 (test (neq ?f0 ?f1))
				 =>
				 (retract ?f0 ?f1)
				 (assert (Instruction ?id is produced by $?a $?b)))

(defrule MergeConsumers-Only
				 (declare (salience -3))
				 (Stage Analysis $?)
				 ?f0 <- (Instruction ?a consumes ?b)
				 =>
				 (retract ?f0)
				 (assert (Instruction ?b is consumed by ?a)))

(defrule MergeProducers-Only
				 (declare (salience -3))
				 (Stage Analysis $?)
				 ?f0 <- (Instruction ?a produces ?b)
				 =>
				 (retract ?f0)
				 (assert (Instruction ?b is produced by ?a)))

;------------------------------------------------------------------------------
(defrule InjectConsumers
				 "Adds a given consumer to the target instruction"
				 (declare (salience -6))
				 (Stage Analysis $?)
				 ?fct <- (Instruction ?id is consumed by $?insts)
				 ?inst <- (object (is-a Instruction) (ID ?id))
				 =>
				 (retract ?fct)
				 (slot-insert$ ?inst Consumers 1 ?insts))
;------------------------------------------------------------------------------
(defrule InjectProducers
				 "Adds a given producer to the target instruction"
				 (declare (salience -6))
				 (Stage Analysis $?)
				 ?fct <- (Instruction ?id is produced by $?insts)
				 ?inst <- (object (is-a Instruction) (ID ?id))
				 =>
				 (retract ?fct)
				 (slot-insert$ ?inst LocalDependencies 1 ?insts)
				 (slot-insert$ ?inst Producers 1 ?insts))
;------------------------------------------------------------------------------
(defrule FlagCallBarrierForRegion-ImbueParent
				 "Marks the given region has having a call barrier"
				 (declare (salience -10))
				 (Stage Analysis $?)
				 ?fct <- (Region ?r has a CallBarrier)
				 ?region <- (object (is-a Region) (ID ?r) (Parent ?p))
				 (exists (object (is-a Region) (ID ?p)))
				 =>
				 (retract ?fct)
				 (assert (Region ?p has a CallBarrier))
				 (modify-instance ?region (HasCallBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule FlagCallBarrierForRegion
				 "Marks the given region has having a call barrier"
				 (declare (salience -10))
				 (Stage Analysis $?)
				 ?fct <- (Region ?r has a CallBarrier)
				 ?region <- (object (is-a Region) (ID ?r) (Parent ?p))
				 (not (exists (object (is-a Region) (ID ?p))))
				 =>
				 (retract ?fct)
				 (modify-instance ?region (HasCallBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule FlagCallBarrierForLoop
				 "Marks the given region has having a call barrier"
				 (declare (salience -10))
				 (Stage Analysis $?)
				 ?fct <- (Region ?r has a CallBarrier)
				 ?region <- (object (is-a Loop) (ID ?r) (Parent ?p))
				 (not (exists (object (is-a Region) (Parent ?p))))
				 =>
				 (retract ?fct)
				 (modify-instance ?region (HasCallBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule FlagCallBarrierForLoop-ImbueParent
				 "Marks the given region has having a call barrier"
				 (declare (salience -10))
				 (Stage Analysis $?)
				 ?fct <- (Region ?r has a CallBarrier)
				 ?region <- (object (is-a Loop) (ID ?r) (Parent ?p))
				 (exists (object (is-a Region) (ID ?p)))
				 =>
				 (retract ?fct)
				 (assert (Region ?p has a CallBarrier))
				 (modify-instance ?region (HasCallBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule FlagCallBarrierForBasicBlock
				 "Marks the given region has having a call barrier"
				 (declare (salience -10))
				 (Stage Analysis $?)
				 ?fct <- (Block ?r has a CallBarrier)
				 ?block <- (object (is-a BasicBlock) (ID ?r) (Parent ?p))
				 =>
				 (retract ?fct)
				 (assert (Region ?p has a CallBarrier))
				 (modify-instance ?block (HasCallBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule MarkHasACallDependency
				 (Stage Analysis $?)
				 ?fct <- (Instruction ?target has a CallDependency)
				 ?inst <- (object (is-a Instruction) (ID ?target))
				 =>
				 (retract ?fct)
				 (if (not (send ?inst get-HasCallDependency)) then
					 (modify-instance ?inst (HasCallDependency TRUE))))
;------------------------------------------------------------------------------
(defrule ExtendedInjectConsumers
				 "Adds a given consumer to the target instruction"
				 (declare (salience -5))
				 (Stage ExtendedMemoryAnalysis $?)
				 ?fct <- (Instruction ?id is consumed by $?targets)
				 ?inst <- (object (is-a Instruction) (ID ?id))
				 =>
				 (retract ?fct)
				 (slot-insert$ ?inst Consumers 1 $?targets))
;------------------------------------------------------------------------------
(defrule ExtendedInjectProducers
				 "Adds a given producer to the target instruction"
				 (declare (salience -5))
				 (Stage ExtendedMemoryAnalysis $?)
				 ?fct <- (Instruction ?id is produced by $?targets)
				 ?inst <- (object (is-a Instruction) (ID ?id))
				 =>
				 (retract ?fct)
				 (slot-insert$ ?inst LocalDependencies 1 ?targets)
				 (slot-insert$ ?inst Producers 1 ?targets))
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
(defrule MergeConsumers-Extended
				 (declare (salience -2))
				 (Stage ExtendedMemoryAnalysis $?)
				 ?f0 <- (Instruction ?a consumes ?id)
				 ?f1 <- (Instruction ?b consumes ?id)
				 (test (neq ?f0 ?f1))
				 =>
				 (retract ?f0 ?f1)
				 (assert (Instruction ?id is consumed by ?a ?b)))

(defrule MergeProducers-Extended
				 (declare (salience -2))
				 (Stage ExtendedMemoryAnalysis $?)
				 ?f0 <- (Instruction ?a produces ?id)
				 ?f1 <- (Instruction ?b produces ?id)
				 (test (neq ?f0 ?f1))
				 =>
				 (retract ?f0 ?f1)
				 (assert (Instruction ?id is produced by ?a ?b)))

(defrule MergeConsumers-Multi-Extended
				 (declare (salience -2))
				 (Stage ExtendedMemoryAnalysis $?)
				 ?f0 <- (Instruction ?id is consumed by $?a)
				 ?f1 <- (Instruction ?id is consumed by $?b)
				 (test (neq ?f0 ?f1))
				 =>
				 (retract ?f0 ?f1)
				 (assert (Instruction ?id is consumed by $?a $?b)))

(defrule MergeProducers-Multi-Extended
				 (declare (salience -2))
				 (Stage ExtendedMemoryAnalysis $?)
				 ?f0 <- (Instruction ?id is produced by $?a)
				 ?f1 <- (Instruction ?id is produced by $?b)
				 (test (neq ?f0 ?f1))
				 =>
				 (retract ?f0 ?f1)
				 (assert (Instruction ?id is produced by $?a $?b)))

(defrule MergeConsumers-Only-Extended
				 (declare (salience -3))
				 (Stage ExtendedMemoryAnalysis $?)
				 ?f0 <- (Instruction ?a consumes ?b)
				 =>
				 (retract ?f0)
				 (assert (Instruction ?b is consumed by ?a)))

(defrule MergeProducers-Only-Extended
				 (declare (salience -3))
				 (Stage ExtendedMemoryAnalysis $?)
				 ?f0 <- (Instruction ?a produces ?b)
				 =>
				 (retract ?f0)
				 (assert (Instruction ?b is produced by ?a)))

(defrule SetifyInstructionProducers-Extended
				 (declare (salience -11))
				 (Stage ExtendedMemoryAnalysis $?)
				 ?inst <- (object (is-a Instruction) (Producers $?a ?b $?c ?b $?d))
				 =>
				 (modify-instance ?inst (Producers $?a ?b $?c $?d)))
;------------------------------------------------------------------------------

(defrule SetifyInstructionConsumers-Extended
				 (declare (salience -11))
				 (Stage ExtendedMemoryAnalysis $?)
				 ?inst <- (object (is-a Instruction) (Consumers $?a ?b $?c ?b $?d))
				 =>
				 (modify-instance ?inst (Consumers $?a ?b $?c $?d)))

;------------------------------------------------------------------------------
(defrule SetifyLocalDependencies-Extended
				 (declare (salience -11))
				 (Stage ExtendedMemoryAnalysis $?)
				 ?inst <- (object (is-a Instruction) (LocalDependencies $?a ?b $?c ?b $?d))
				 =>
				 (modify-instance ?inst (LocalDependencies $?a ?b $?c $?d)))

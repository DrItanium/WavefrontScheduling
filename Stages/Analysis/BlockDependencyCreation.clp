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
         ;mark as a local dependency here
         (slot-insert$ ?i0 LocalDependencies 1 ?o)
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
(defrule ExtendedInjectConsumers
         "Adds a given consumer to the target instruction"
         (Stage ExtendedMemoryAnalysis-Inject $?)
         ?fct <- (Instruction ?id is consumed by $?targets)
         ?inst <- (object (is-a Instruction) (ID ?id) (Consumers $?cs))
         =>
         (retract ?fct)
         (bind ?cons $?cs)
         (progn$ (?target ?targets)
                 (if (not (member$ ?target ?cons)) then
                   (bind ?cons (insert$ ?cons 1 ?target))))
         (modify-instance ?inst (Consumers ?cons)))
;------------------------------------------------------------------------------
(defrule ExtendedInjectProducers
         "Adds a given producer to the target instruction"
         (Stage ExtendedMemoryAnalysis-Inject $?)
         ?fct <- (Instruction ?id is produced by $?targets)
         ?inst <- (object (is-a Instruction) (ID ?id) (Producers $?ps))
         =>
         (retract ?fct)
         (bind ?prods $?ps)
         (progn$ (?target ?targets)
                 (if (not (member$ ?target ?prods)) then
                   (bind ?prods (insert$ ?prods 1 ?target))))
         (modify-instance ?inst (Producers ?prods)))
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
         ;(declare (salience -2))
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Instruction ?a consumes ?id)
         ?f1 <- (Instruction ?b consumes ?id)
         (test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (Instruction ?id is consumed by ?a ?b)))
;------------------------------------------------------------------------------
(defrule MergeProducers-Extended
         ;(declare (salience -2))
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Instruction ?a produces ?id)
         ?f1 <- (Instruction ?b produces ?id)
         (test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (Instruction ?id is produced by ?a ?b)))
;------------------------------------------------------------------------------
(defrule MergeConsumers-Multi-Extended
         ;(declare (salience -2))
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Instruction ?id is consumed by $?a)
         ?f1 <- (Instruction ?id is consumed by $?b)
         (test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (Instruction ?id is consumed by $?a $?b)))
;------------------------------------------------------------------------------

(defrule MergeProducers-Multi-Extended
         ;(declare (salience -2))
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Instruction ?id is produced by $?a)
         ?f1 <- (Instruction ?id is produced by $?b)
         (test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (Instruction ?id is produced by $?a $?b)))
;------------------------------------------------------------------------------
(defrule MergeConsumers-Only-Extended
         (declare (salience -1))
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Instruction ?a consumes ?b)
         =>
         (retract ?f0)
         (assert (Instruction ?b is consumed by ?a)))
;------------------------------------------------------------------------------
(defrule MergeProducers-Only-Extended
         (declare (salience -1))
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Instruction ?a produces ?b)
         =>
         (retract ?f0)
         (assert (Instruction ?b is produced by ?a)))
;------------------------------------------------------------------------------
(defrule SetifyInstructionProducers-Extended
         (declare (salience -11))
         (Stage ExtendedMemoryAnalysis-MakeSet $?)
         ?inst <- (object (is-a Instruction) (Producers $?a ?b $?c ?b $?d))
         =>
         (modify-instance ?inst (Producers $?a ?b $?c $?d)))
;------------------------------------------------------------------------------
(defrule SetifyInstructionConsumers-Extended
         (declare (salience -11))
         (Stage ExtendedMemoryAnalysis-MakeSet $?)
         ?inst <- (object (is-a Instruction) (Consumers $?a ?b $?c ?b $?d))
         =>
         (modify-instance ?inst (Consumers $?a ?b $?c $?d)))
;------------------------------------------------------------------------------
(defrule SetifyLocalDependencies-Extended
         (declare (salience -11))
         (Stage ExtendedMemoryAnalysis-MakeSet $?)
         ?inst <- (object (is-a Instruction) 
                          (LocalDependencies $?a ?b $?c ?b $?d))
         =>
         (modify-instance ?inst (LocalDependencies $?a ?b $?c $?d)))
;------------------------------------------------------------------------------
(defrule SetifyNonLocalDependencies-Extended
         (declare (salience -11))
         (Stage ExtendedMemoryAnalysis-MakeSet $?)
         ?inst <- (object (is-a Instruction) 
                          (NonLocalDependencies $?a ?b $?c ?b $?d))
         =>
         (modify-instance ?inst (NonLocalDependencies $?a ?b $?c $?d)))
;------------------------------------------------------------------------------

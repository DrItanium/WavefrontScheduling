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
; MergeRules.clp - Contains all of the merge rules used in the analysis stages
; Written by Joshua Scoggins (11/18/2012)
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
(defrule MergeLocalDependencies-Single
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Add local dependency ?a to ?c)
         ?f1 <- (Add local dependency ?b to ?c)
         (test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (Into ?c add local dependency ?a ?b)))
;------------------------------------------------------------------------------
(defrule MergeLocalDependencies-Multi
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Into ?a add local dependency $?b)
         ?f1 <- (Into ?a add local dependency $?c)
         (test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (Into ?a add local dependency $?b $?c)))
;------------------------------------------------------------------------------
(defrule MergeLocalDependencies-Only
         (declare (salience -1))
         (Stage ExtendedMemoryAnalysis-Merge $?)
         ?f0 <- (Add local dependency ?a to ?c)
         =>
         (retract ?f0)
         (assert (Into ?c add local dependency ?a)))
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
(defrule InjectLocalDependencies
         "Adds a local dependency based on a given fact"
         (Stage ExtendedMemoryAnalysis-Inject $?)
         ?fct <- (Into ?a add local dependency $?targets)
         ;?fct <- (Add local dependency ?a to ?b)
         ?i <- (object (is-a Instruction) (ID ?a) (LocalDependencies $?ld))
         =>
         (retract ?fct)
         (bind ?result $?ld)
         (progn$ (?target ?targets)
          (if (not (member$ ?target ?result)) then
           (bind ?result (insert$ ?result 1 ?target))))
         (modify-instance ?i (LocalDependencies ?result)))
;------------------------------------------------------------------------------

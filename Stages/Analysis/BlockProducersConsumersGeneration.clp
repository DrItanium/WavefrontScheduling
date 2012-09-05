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
; BlockProducersConsumersGeneration.clp - Contains rules associated with the 
; creation of basic block producers and consumers
; Written by Joshua Scoggins (6/20/2012)
;------------------------------------------------------------------------------
(defrule AssertBasicBlockConsumers
 (declare (salience 10))
 (Stage Analysis $?)
 (object (is-a Region) (ID ?h) (CanWavefrontSchedule TRUE))
 (object (is-a BasicBlock) (ID ?name) (Parent ?h) (Contents $? ?inst $?))
 (object (is-a Instruction) (ID ?inst) (SourceRegisters $?insts))
 =>
 ;A really easy way to improve performance is to not use indirect fact
 ; assertions. Although doing things this way is really elegant :D 
 (assert (block ?name consumes ?insts)))

(defrule ConvertListOfBasicBlockElementsIntoSet
 (declare (salience 9))
 (Stage Analysis $?)
 ?f0 <- (block ?name consumes $?a ?b $?c ?b $?d)
 =>
 (retract ?f0)
 (assert (block ?name consumes $?a ?b $?c $?d)))

(defrule MergeBasicBlockConsumers
 (declare (salience 5))
 (Stage Analysis $?)
 ?f0 <- (block ?name consumes $?i0)
 ?f1 <- (block ?name consumes $?i1)
 (test (neq ?f0 ?f1))
 =>
 (retract ?f0 ?f1)
 (assert (block ?name consumes ?i0 ?i1)))

(defrule RemoveDuplicatesBasicBlockConsumers
 "Removes duplicate elements from a given merged set of facts"
 (declare (salience 1))
 ?f0 <- (block ?name consumes $?a ?b $?c ?b $?d)
 =>
 (retract ?f0)
 (assert (block ?name consumes $?a ?b $?c $?d)))

(defrule ModifyBasicBlockConsumesList-Parent
 (Stage Analysis $?)
 ?fct <- (block ?n consumes $?i)
 ?bb <- (object (is-a BasicBlock) (ID ?n) (Parent ?r))
 (exists (object (is-a Region) (ID ?r)))
 =>
 (retract ?fct)
 (assert (region ?r consumes $?i))
 (slot-insert$ ?bb Consumes 1 $?i))

(defrule ModifyBasicBlockConsumesList-NoParent
 (Stage Analysis $?)
 ?fct <- (block ?n consumes $?i)
 ?bb <- (object (is-a BasicBlock) (ID ?n) (Parent ?r))
 (not (exists (object (is-a Region) (ID ?r))))
 =>
 (retract ?fct)
 (slot-insert$ ?bb Consumes 1 $?i))

;------------------------------------------------------------------------------
(defrule MergeRegionConsumers
 (declare (salience 5))
 (Stage Analysis $?)
 ?f0 <- (region ?name consumes $?i0)
 ?f1 <- (region ?name consumes $?i1)
 (test (neq ?f0 ?f1))
 =>
 (retract ?f0 ?f1)
 (assert (region ?name consumes ?i0 ?i1)))

(defrule RemoveDuplicatesRegionConsumers
 "Removes duplicate elements from a given merged set of facts"
 (declare (salience 1))
 ?f0 <- (region ?name consumes $?a ?b $?c ?b $?d)
 =>
 (retract ?f0)
 (assert (region ?name consumes $?a ?b $?c $?d)))

(defrule ModifyRegionConsumesList-Parent
 (Stage Analysis $?)
 ?fct <- (region ?n consumes $?i)
 ?bb <- (object (is-a Region) (ID ?n) (Parent ?r))
 (exists (object (is-a Region) (ID ?r)))
 =>
 (retract ?fct)
 (assert (region ?r consumes $?i))
 (slot-insert$ ?bb Consumes 1 $?i))

(defrule ModifyRegionConsumesList-NoParent
 (Stage Analysis $?)
 ?fct <- (region ?n consumes $?i)
 ?bb <- (object (is-a Region) (ID ?n) (Parent ?r))
 (not (exists (object (is-a Region) (ID ?r))))
 =>
 (retract ?fct)
 (slot-insert$ ?bb Consumes 1 $?i))

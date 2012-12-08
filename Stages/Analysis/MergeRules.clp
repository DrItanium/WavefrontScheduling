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
(defrule MergeDeclarations-Produces
         (Stage ExtendedMemoryAnalysis-Merge $?)
			?f0 <- ({ action: dependency-announce
						 type: produces 
						 target: ?a
						 other: ?id })
			?f1 <- ({ action: dependency-announce
						 type: produces 
						 target: ?b&~?a
						 other: ?id })
			=>
			(retract ?f0 ?f1)
			(assert (action: dependency-set
						  type: produces 
						  target: ?id
						  set: { ?a ?b })))
;------------------------------------------------------------------------------
(defrule MergeDeclarations-Consumes
         (Stage ExtendedMemoryAnalysis-Merge $?)
			?f0 <- ({ action: dependency-announce
						 type: consumes 
						 target: ?a
						 other: ?id })
			?f1 <- ({ action: dependency-announce
						 type: consumes 
						 target: ?b&~?a
						 other: ?id })
			=>
			(retract ?f0 ?f1)
			(assert (action: dependency-set
						  type: consumes 
						  target: ?id
						  set: { ?a ?b })))
;------------------------------------------------------------------------------
(defrule MergeDependencySets-Produces
         (Stage ExtendedMemoryAnalysis-Merge $?)
			?f0 <- (action: dependency-set
						 type: produces
						 target: ?id
						 set: { $?s0 })
			?f1 <- (action: dependency-set
						 type: produces
						 target: ?id
						 set: { $?s1 })
			(test (neq ?f0 ?f1))
			=>
			(retract ?f0 ?f1)
			(assert (action: dependency-set
						  type: produces
						  target: ?id
						  set: { $?s0 $?s1 })))
;------------------------------------------------------------------------------
(defrule MergeDependencySets-Consumes
         (Stage ExtendedMemoryAnalysis-Merge $?)
			?f0 <- (action: dependency-set
						 type: consumes
						 target: ?id
						 set: { $?s0 })
			?f1 <- (action: dependency-set
						 type: consumes
						 target: ?id
						 set: { $?s1 })
			(test (neq ?f0 ?f1))
			=>
			(retract ?f0 ?f1)
			(assert (action: dependency-set
						  type: consumes
						  target: ?id
						  set: { $?s0 $?s1 })))
;------------------------------------------------------------------------------
(defrule MergeSingleDeclaration-Produces
         (declare (salience -1))
         (Stage ExtendedMemoryAnalysis-Merge $?)
			?f0 <- ({ action: dependency-announce
						 type: produces
						 target: ?a
						 other: ?id })
			=>
			(retract ?f0)
			(assert (action: dependency-set
						  type: produces
						  target: ?id
						  set: { ?a })))
;------------------------------------------------------------------------------
(defrule MergeSingleDeclaration-Consumes
         (declare (salience -1))
         (Stage ExtendedMemoryAnalysis-Merge $?)
			?f0 <- ({ action: dependency-announce
						 type: consumes
						 target: ?a
						 other: ?id })
			=>
			(retract ?f0)
			(assert (action: dependency-set
						  type: consumes
						  target: ?id
						  set: { ?a })))
;------------------------------------------------------------------------------
(defrule InjectConsumers-Producers-And-LocalDependencies
         "Performs the actions of InjectConsumers and
         InjectProducersAndLocalDependencies in a single rule fire."
         (declare (salience 1))
         (Stage ExtendedMemoryAnalysis-Inject $?)
			?f0 <- (action: dependency-set
					  type: consumes
					  target: ?id
					  set: { $?t0 })
			?f1 <- (action: dependency-set
					  type: produces 
					  target: ?id
					  set: { $?t1 })
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
						(bind ?cs (create$ ?cs ?target))))
         (progn$ (?target ?t1)
                 (if (not (member$ ?target ?lds)) then
						(bind ?lds (create$ ?lds ?target)))
                 (if (not (member$ ?target ?ps)) then
						 (bind ?ps (create$ ?ps ?target))))
         (modify-instance ?inst (Consumers ?cs) (Producers ?ps) 
                          (LocalDependencies ?lds))))
;------------------------------------------------------------------------------
(defrule InjectConsumers
         "Adds a given consumer to the target instruction"
         (Stage ExtendedMemoryAnalysis-Inject $?)
			?fct <- (action: dependency-set
						  type: consumes
						  target: ?id
						  set: { $?targets })
         ?inst <- (object (is-a Instruction) (ID ?id) (Consumers $?cs))
         =>
         (retract ?fct)
         (object-pattern-match-delay
			(if (= (length$ ?cs) 0) then
			    (modify-instance ?inst (Consumers $?targets))
				 else
             (bind ?cons $?cs)
         (progn$ (?target ?targets)
                 (if (not (member$ ?target ?cons)) then
						   (bind ?cons (create$ ?cons ?target))))
         (modify-instance ?inst (Consumers ?cons)))))
;------------------------------------------------------------------------------
(defrule InjectProducersAndLocalDependencies
         "Adds a given producer to the target instruction."
         (Stage ExtendedMemoryAnalysis-Inject $?)
			?fct <- (action: dependency-set
						  type: produces 
						  target: ?id
						  set: { $?targets })
         ?inst <- (object (is-a Instruction) (ID ?id) (Producers $?ps)
                          (LocalDependencies $?ld))
         =>
         (retract ?fct)
         (bind ?prods $?ps)
         (bind ?lds $?ld)
         (object-pattern-match-delay
         (progn$ (?target ?targets)
                 (if (not (member$ ?target ?lds)) then
						 (bind ?lds (create$ ?lds ?target)))
                 (if (not (member$ ?target ?prods)) then
						 (bind ?prods (create$ ?prods ?target))))
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

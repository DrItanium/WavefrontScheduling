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
(defrule ConstructDeterminantForRegion
			(Stage DeterminantConstruction $?)
			(object (is-a Region) (ID ?r))
			(not (exists (object (is-a OwnershipDeterminant) (Parent ?r))))
			=>
			(make-instance of OwnershipDeterminant (Parent ?r)))
;------------------------------------------------------------------------------
(defrule ConstructDeterminantForBasicBlock
			(Stage DeterminantConstruction $?)
			(object (is-a BasicBlock) (ID ?b))
			(not (exists (object (is-a OwnershipDeterminant) (Parent ?b))))
			=>
			(make-instance of OwnershipDeterminant (Parent ?b)))
;------------------------------------------------------------------------------
(defrule PopulateDeterminant
			(Stage DeterminantPopulation $?)
			?fct <- (claim ?a owns ?b)
			?obj <- (object (is-a OwnershipDeterminant) (Parent ?b))
			?obj2 <- (object (is-a OwnershipDeterminant) (Parent ?a))
			=>
			(retract ?fct)
      (object-pattern-match-delay 
			(slot-insert$ ?obj2 PotentialChildren 1 ?b)
			(slot-insert$ ?obj Claims 1 ?a)))
;------------------------------------------------------------------------------
(defrule DetermineIndirectClaim
			(Stage DeterminantResolution $?)
			?t0 <- (object (is-a OwnershipDeterminant) (Parent ?b) 
								(Claims $?v ?a $?x) (IndirectClaims $?ic))
			(object (is-a OwnershipDeterminant) (Parent ~?b) 
					  (PotentialChildren $? ?b $?) (Claims $? ?a $?))
			?t1 <- (object (is-a OwnershipDeterminant) (Parent ?a) 
								(PotentialChildren $?t ?b $?r))
			=>
			;let's see if this is faster
      (object-pattern-match-delay 
      (modify-instance ?t0 (IndirectClaims ?ic ?a) (Claims ?v ?x))
      (modify-instance ?t1 (PotentialChildren ?t ?r))))
;------------------------------------------------------------------------------
(defrule DetermineIndirectIndirectClaim
			(Stage DeterminantIndirectResolution $?)
			?t0 <- (object (is-a OwnershipDeterminant) (Parent ?b) 
								(Claims $?l ?a $?x) (IndirectClaims $?ic))
			(object (is-a OwnershipDeterminant) (Parent ~?b&~?a) 
					  (IndirectClaims $? ?a $?) (PotentialChildren $? ?b $?))
			?t1 <- (object (is-a OwnershipDeterminant) (Parent ?a)
								(PotentialChildren $?z ?b $?q))
			=>
      (object-pattern-match-delay 
       (modify-instance ?t0 (IndirectClaims ?ic ?a) (Claims ?l ?x))
       (modify-instance ?t1 (PotentialChildren ?z ?q))))
;------------------------------------------------------------------------------
(defrule DeleteNonExistentReferences
			(Stage Fixup $?)
			?region <- (object (is-a Region) (Contents $? ?b $?))
			(not (exists (object (ID ?b))))
			=>
      (object-pattern-match-delay 
			(bind ?ind0 (member$ ?b (send ?region get-Contents)))
			(slot-delete$ ?region Contents ?ind0 ?ind0)))
;------------------------------------------------------------------------------
(defrule UpdateOwnerOfTargetRegion
			(Stage FixupUpdate $?)
			(object (is-a OwnershipDeterminant) (Parent ?p) (Claims ?a))
			?obj <- (object (is-a Region) (ID ?p))
			=>
			(modify-instance ?obj (Parent ?a)))
;------------------------------------------------------------------------------
(defrule UpdateOwnerOfTargetBasicBlock
			(Stage FixupUpdate $?)
			(object (is-a OwnershipDeterminant) (Parent ?p) 
					  (Claims ?a))
			?obj <- (object (is-a BasicBlock) (ID ?p))
			=>
			(modify-instance ?obj (Parent ?a)))
;------------------------------------------------------------------------------
(defrule AddNewChildToTargetRegion
			(Stage FixupUpdate $?)
			(object (is-a OwnershipDeterminant) (Parent ?p)
					  (PotentialChildren $? ?a $?))
			?region <- (object (is-a Region) (ID ?p) (Contents $?c))
      (test (not (member$ ?a ?c)))
			=>
			(slot-insert$ ?region Contents 1 ?a))
;------------------------------------------------------------------------------
(defrule CleanupOwnershipDeterminants
			"Deletes all of the OwnershipDeterminant objects in a single rule 
			fire"
			(Stage CleanUp-Merger $?)
			=>
			(progn$ (?obj (find-all-instances ((?list OwnershipDeterminant)) 
														 TRUE))
					  (unmake-instance ?obj)))
;------------------------------------------------------------------------------
(defrule RemoveUnownedElements
			"Now that we have figured out and updated ownership claims it is 
			necessary to remove leftover entries in other regions"
			(Stage FixupRename $?)
			?r <- (object (is-a Region) (ID ?t) (Contents $?a ?b $?c))
			(object (is-a TaggedObject) (ID ?b) (Parent ~?t))
			=>
			(modify-instance ?r (Contents $?a $?c)))
;------------------------------------------------------------------------------
(defrule FAILURE-TooManyClaimsOfOwnership
			(Stage Fixup $?)
			(object (is-a OwnershipDeterminant) (Parent ?a) 
					  (Claims $?z&:(> (length$ ?z) 1))
					  (ID ?name))
			=>
			(printout t "ERROR: " ?name " has more than one claim of ownership on"
						 " it!" crlf "The claims are " ?z crlf)
			(exit))
;------------------------------------------------------------------------------
(defrule FAILURE-NoRemainingClaimsForRegion
			(Stage Fixup $?)
			(object (is-a OwnershipDeterminant) (Parent ?a) (Claims)
					  (PotentialChildren $?pc) (IndirectClaims $?ic))
			(object (is-a Region) (ID ?a) (IsTopLevelRegion FALSE))
			=>
			(printout t "ERROR: " ?a " has no remaining claims!" crlf 
						 ?a " has " $?pc " as it's potential children." crlf
						 ?a " has " $?ic " as it's indirect claims." crlf)
			(exit))
;------------------------------------------------------------------------------
(defrule FAILURE-NoRemainingClaimsForBasicBlock
			(Stage Fixup $?)
			(object (is-a OwnershipDeterminant) (Parent ?a) (Claims)
					  (PotentialChildren $?pc) (IndirectClaims $?ic))
			(object (is-a BasicBlock) (ID ?a)) 
			=>
			(printout t "ERROR: BasicBlock " ?a " has no remaining claims!" crlf 
						 ?a " has " $?pc " as it's potential children." crlf
						 ?a " has " $?ic " as it's indirect claims." crlf)
			(exit))
;------------------------------------------------------------------------------

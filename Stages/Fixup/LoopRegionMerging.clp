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
; LoopRegionMerging.clp - Contains rules that merge loops and regions together
; Written by Joshua Scoggins (6/26/2012)
;------------------------------------------------------------------------------
(defrule DeclareOriginality
				 (declare (salience 1000))
				 (Stage OriginalityAssertion $?)
				 (object (is-a Region) (ID ?i) (Parent ?p))
				 =>
				 (assert (Region ?i is originally owned by ?p)))
(defrule ReplaceRegionWithLoop
				 "Replaces a region with a loop if it turns out that the region is a container
				 over a given loop (it's the only element in the region). The loop takes the
				 place of the region in the grand scheme of things"
				 (declare (salience -10))
				 (Stage Fixup $?)
				 ?r <- (object (is-a Region) (Class Region) (ID ?name) (Parent ?p) (Contents ?loop))
				 ?l <- (object (is-a Loop) (ID ?loop) (Parent ?lp)) ;we don't care what the parent is
				 ?parent <- (object (is-a Region) (ID ?p) (Contents $?start ?name $?rest))
				 =>
				 ;(printout t "Replacing " ?name " with " ?loop " because " ?name 
				 ;					 " only contains " ?loop crlf)
				 ; (printout t "Parent of " ?loop " was " ?lp " originally" crlf)
				 (modify-instance ?l (Parent ?p))
				 (modify-instance ?parent (Contents $?start ?loop $?rest))
				 (unmake-instance ?r))
;------------------------------------------------------------------------------
(defrule ConvertControlModification
				 "Breaks apart the controlmodification template into two facts to perform
				 different actions"
				 (Stage Fixup $?)
				 ?fct <- (ControlModification (ModificationType Relinquish) (From ?l) (To ?r)
																			(Subject $?elements))
				 =>
				 (retract ?fct)
				 (assert (Put into ?r elements $?elements)))

(defrule InjectElementsIntoNewBlock
				 (Stage Fixup $?)
				 ?fct <- (Put into ?r elements ?element $?elements)
				 ?region <- (object (is-a Region) (ID ?r))
				 ?block <- (object (is-a BasicBlock) (ID ?element))
				 =>
				 (assert (Put into ?r elements $?elements))
				 (modify-instance ?block (Parent ?r))
				 (slot-insert$ ?region Contents 1 ?element)
				 (retract ?fct))
(defrule InjectElementsIntoNewBlock-Retract
				 ?fct <- (Put into ?r elements)
				 =>
				 (retract ?fct))
;------------------------------------------------------------------------------
(defrule StripoutUncontrolledElements
				 (declare (salience -2))
				 (Stage FixupUpdate $?)
				 (object (is-a Region) (ID ?r) (Contents $? ?e $?))
				 (object (is-a TaggedObject) (ID ?e) (Parent ?z&~?r))
				 =>
				 ;(printout t "element " ?e " in " ?r " is owned by " ?z "!" crlf)
				 (assert (Parent of ?e is now ?r)
								 (Rename: In ?z put ?r in place of ?e)))

(defrule RetractImpossibleReplaceStatements
				 (Stage FixupRename $?)
				 ?f0 <- (Rename: In ?r put ?t in place of $?q)
				 (not (exists (object (ID ?r))))
				 =>
				 (retract ?f0))

(defrule MergePutStatements
				 (declare (salience 1))
				 (Stage FixupRename $?)
				 ?f0 <- (Rename: In ?r put ?t in place of $?e0)
				 ?f1 <- (Rename: In ?r put ?t in place of $?e1)
				 (test (neq ?f0 ?f1))
				 =>
				 (retract ?f0 ?f1)
				 (assert (Rename: In ?r put ?t in place of $?e0 $?e1)))


(defrule ReplaceSubsets
				 (Stage FixupUpdate $?)
				 ?region <- (object (is-a Region) (ID ?r) (Contents $?a))
				 ?loop <- (object (is-a Loop) (ID ?l&~?r) (Contents $?b))
				 (test (subsetp ?a ?b))
				 =>
				 ;(printout t "Replacing " ?a " with " ?r " in " ?l crlf)
				 (assert (In ?l put ?r in place of $?a)))

(defrule MergeElementsFromLoop
				 (Stage FixupUpdate $?)
				 ?fct <- (In ?l put ?r in place of ?first $?rest)
				 ?loop <- (object (is-a Loop) (ID ?l) (Contents $?a ?first $?b))
				 =>
				 (retract ?fct)
				 (assert (In ?l put ?r in place of $?rest))
				 (modify-instance ?loop (Contents $?a $?b)))

(defrule MergeRegionInPlaceOfElementsToLoop
				 (Stage FixupUpdate $?)
				 ?fct <- (In ?l put ?r in place of)
				 ?loop <- (object (is-a Loop) (ID ?l))
				 (test (eq FALSE (member$ ?r (send ?loop get-Contents))))
				 =>
				 (retract ?fct)
				 (slot-insert$ ?loop Contents 1 ?r))

(defrule MergeRegionInPlaceOfElementsToLoop-NoDuplicate
				 (Stage FixupUpdate $?)
				 ?fct <- (In ?l put ?r in place of)
				 ?loop <- (object (is-a Loop) (ID ?l))
				 (test (neq FALSE (member$ ?r (send ?loop get-Contents))))
				 =>
				 (retract ?fct))

(defrule RevokeOwnershipOfIllegalElements
				 (Stage FixupRename $?)
				 ?fct <- (Rename: In ?r put ?t in place of ?first $?rest)
				 ?region <- (object (is-a Region) (ID ?r) (Contents $?before ?first $?after))
				 =>
				 (retract ?fct)
				 (assert (Rename: In ?r put ?t in place of $?rest))
				 (modify-instance ?region (Contents $?before $?after)))

(defrule ReplaceOwnershipOfIllegalElements-Final-InsertAndRetract
				 (Stage FixupRename $?)
				 ?fct <- (Rename: In ?r put ?t in place of)
				 ?region <- (object (is-a Region) (ID ?r))
				 (test (eq FALSE (member$ ?t (send ?region get-Contents))))
				 =>
				 (retract ?fct)
				 (assert (Added ?t to ?r as part of replacement strategy))
				 (slot-insert$ ?region Contents 1 ?t))

(defrule ReplaceOwnershipOfIllegalElements-Final-JustRetract
				 (Stage FixupRename $?)
				 ?fct <- (Rename: In ?r put ?t in place of)
				 ?region <- (object (is-a Region) (ID ?r))
				 (test (neq FALSE (member$ ?t (send ?region get-Contents))))
				 =>
				 (assert (Added ?t to ?r as part of replacement strategy))
				 (retract ?fct))

(defrule ReplaceParentOfGivenItem
				 (Stage FixupRename $?)
				 ?fct <- (Parent of ?t is now ?r)
				 ?o0 <- (object (ID ?t))
				 =>
				 (retract ?fct)
				 ;(printout t ?r " is now the parent of " ?t crlf)
				 (modify-instance ?o0 (Parent ?r)))
;(defrule FixupRegions-Printout
; (declare (salience 100))
; (Stage FixupRegions $?)
; =>
; (facts))
(defrule FixupRegions-ParentExists
				 (declare (salience 1))
				 (Stage FixupRegions $?)
				 ?f0 <- (Region ?r is originally owned by ?t)
				 ?f1 <- (Added ?r to ?s as part of replacement strategy)
				 ?oldParent <- (object (is-a Region) (ID ?t) (Contents $?a ?r $?b))
				 ?region <- (object (is-a Region) (Class Region) (ID ?r) (Parent ?t))
				 =>
				 (retract ?f0 ?f1)
				 ;(printout t ?s " is now the parent of " ?r " instead of " ?t crlf)
				 (send ?region put-Parent ?s)
				 (modify-instance ?oldParent (Contents $?a $?b)))

(defrule FixupRegions-ParentDoesntExist
				 (declare (salience 1))
				 (Stage FixupRegions $?)
				 ?f0 <- (Region ?r is originally owned by ?t)
				 ?f1 <- (Added ?r to ?s as part of replacement strategy)
				 (not (exists (object (ID ?t))))
				 =>
				 (retract ?f0 ?f1))


(defrule FixupRegions-NoChange
				 (Stage FixupRegions $?)
				 ?f0 <- (Region ?r is originally owned by ?)
				 (not (exists (Added ?r to ? as part of replacement strategy)))
				 =>
				 (retract ?f0))


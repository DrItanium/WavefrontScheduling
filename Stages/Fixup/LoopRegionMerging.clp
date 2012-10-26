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
;
; Major Rewrite started on 10/22/2012 to reflect changes made to 
; LibExpertSystem
;------------------------------------------------------------------------------
; The first thing to understand is that LibExpertSystem will no longer be
; lifting a finger to assist us in merging loops and regions. I did a thought
; experiment and I realized that it will be easier this way to ensure proper
; merging and (by proxy) ordering. 
;------------------------------------------------------------------------------
; My current idea is to have loops and regions make claims based off of a list
; defined by LLVM during knowledge construction. 
;------------------------------------------------------------------------------
(defrule ConstructFlatListForRegion
 "Creates a flat representation of the contents of the given region"
 (Stage BuildFlatList $?)
 (object (is-a Region) (ID ?id) (Contents $?z))
 (not (exists (object (is-a Hint) (Type FlatList) (Parent ?id))))
 =>
 (make-instance of Hint (Type FlatList) (Parent ?id)) 
 (assert (Populate FlatList of ?id with $?z)))

(defrule PopulateFlatList-BasicBlock
 (Stage BuildFlatList $?)
 ?f <- (Populate FlatList of ?id with ?first $?rest)
 ?o <- (object (is-a Hint) (Type FlatList) (Parent ?id))
 (object (is-a BasicBlock) (ID ?first))
 =>
 (slot-insert$ ?o Contents 1 ?first)
 (retract ?f)
 (assert (Populate FlatList of ?id with $?rest)))

(defrule PopulateFlatList-Region
 (Stage BuildFlatList $?)
 ?f <- (Populate FlatList of ?id with ?first $?rest)
 ?o <- (object (is-a Hint) (Type FlatList) (Parent ?id))
 (object (is-a Region) (ID ?first))
 (object (is-a Hint) (Type FlatList) (Parent ?first) (ID ?name))
 =>
 ;Add the reference to FlatList for the time being until we have
 ;finished constructing an entire flat list
 (slot-insert$ ?o Contents 1 ?name)
 (retract ?f)
 (assert (Populate FlatList of ?id with $?rest)))

(defrule RetractFlatListConstruction
 (Stage BuildFlatList $?)
 ?f <- (Populate FlatList of ? with)
 =>
 (retract ?f))

(defrule ExpandFlatListEntry
 "Takes a flat list and expands one of the elements of the contents if it turns
 out that element is another flat list"
 (Stage ExpandFlatList $?)
 ?id <- (object (is-a Hint) (Type FlatList) (Contents $?a ?b $?c))
 (object (is-a Hint) (Type FlatList) (ID ?b) (Contents $?j))
 =>
 (modify-instance ?id (Contents $?a $?j $?c)))

(defrule ClaimOwnership
 "Asserts that a region owns another through a subset check. The first flat
 list is checked to see if it is a _proper_ subset of the second"
 (Stage ClaimOwnership $?)
 ?f0 <- (object (is-a Hint) (Type FlatList) (ID ?i0) (Contents $?c0) 
                (Parent ?p0))
 ?f1 <- (object (is-a Hint) (Type FlatList) (ID ?i1&~?i0) (Contents $?c1)
                (Parent ?p1))
 (test (and (subsetp ?c0 ?c1) (> (length$ ?c1) (length$ ?c0))))
 =>
 (assert (claim ?p1 owns ?p0)))

(defrule ClaimEquivalence
 "Asserts that two regions are equivalent if one flat list contains the same
 elements as a second one."
 (Stage ClaimOwnership $?)
 ?f0 <- (object (is-a Hint) (Type FlatList) (ID ?i0) (Contents $?c0)
                (Parent ?p0))
 ?f1 <- (object (is-a Hint) (Type FlatList) (ID ?i1&~?i0) (Contents $?c1)
                (Parent ?p1))
 (test (and (subsetp ?c0 ?c1) (= (length$ ?c1) (length$ ?c0))))
 =>
 (assert (claim ?p1 equivalent ?p0)))


(defrule MergeClaimsOfEquivalence
 "It is possible for two facts of equivalence to actually be the same fact"
 (declare (salience -1))
 (Stage ClaimOwnership $?)
 ?f0 <- (claim ?a equivalent ?b)
 ?f1 <- (claim ?b equivalent ?a)
 =>
 (retract ?f0 ?f1)
 (assert (claim ?a equivalent ?b)))

(defrule EliminateEquivalences-LoopFirst
 "If we find an equivalence then it means that a loop and a region contain the
 same elements. Therefore the loop persists and the region dies. The loop is
 the first entry."
 (declare (salience 1))
 (Stage Arbitrate $?)
 ?f0 <- (claim ?a equivalent ?b)
 (object (is-a Loop) (ID ?a))
 (object (is-a Region&~Loop) (ID ?b))
 =>
 (retract ?f0)
 (assert (delete region ?b)
         (replace ?b with ?a)))

(defrule EliminateEquivalences-LoopSecond
 "If we find an equivalence then it means that a loop and a region contain the
 same elements. Therefore the loop persists and the region dies. The loop is
 the second entry."
 (declare (salience 1))
 (Stage Arbitrate $?)
 ?f0 <- (claim ?b equivalent ?a)
 (object (is-a Loop) (ID ?a))
 (object (is-a Region&~Loop) (ID ?b))
 =>
 (retract ?f0)
 (assert (delete region ?b)
         (replace ?b with ?a)))

(defrule RetractSuperownership
 "Removes claims of ownership that are retained by a child"
 (Stage Arbitrate $?)
 ?f0 <- (claim ?a owns ?b)
 ?f1 <- (claim ?c owns ?b)
 ?f2 <- (claim ?a owns ?c)
 =>
 (retract ?f0 ?f1 ?f2)
 ;(printout t 
 ; "==============================================================" crlf 
 ; ?a " owns " ?b " , " ?c " owns " ?b " , and " ?a " owns " ?c crlf 
 ; "Therefore, " ?a " owns " ?b " indirectly" crlf)
 (assert (claim ?a owns ?c)
         (claim ?c owns ?b)))

(defrule PrintoutFacts
 (Stage Fixup $?)
 =>
 (facts))
(defrule PrintoutResults
 (Silence)
 (Stage Fixup $?)
 ?id <- (object (is-a Hint) (Type FlatList))
 =>
 (printout t "==================" crlf)
 (send ?id print))

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
(defrule ConstructFlatListForRegion
			"Creates a flat representation of the contents of the given region"
			(Stage BuildFlatList $?)
			(object (is-a Region) (ID ?id) (Contents $?z))
			(not (exists (object (is-a FlatList) (Parent ?id))))
			=>
			(make-instance of FlatList (Parent ?id)) 
			(assert (Populate FlatList of ?id with $?z)))
;------------------------------------------------------------------------------
(defrule PopulateFlatList-BasicBlock
			(Stage BuildFlatList $?)
			?f <- (Populate FlatList of ?id with ?first $?rest)
			?o <- (object (is-a FlatList) (Parent ?id))
			(object (is-a BasicBlock) (ID ?first))
			=>
			(slot-insert$ ?o Contents 1 ?first)
			(retract ?f)
			(assert (Populate FlatList of ?id with $?rest)))
;------------------------------------------------------------------------------
(defrule PopulateFlatList-Region
			(Stage BuildFlatList $?)
			?f <- (Populate FlatList of ?id with ?first $?rest)
			?o <- (object (is-a FlatList) (Parent ?id))
			(object (is-a Region) (ID ?first))
			(object (is-a FlatList) (Parent ?first) (ID ?name))
			=>
			;Add the reference to FlatList for the time being until we have
			;finished constructing an entire flat list
			(slot-insert$ ?o Contents 1 ?name)
			(retract ?f)
			(assert (Populate FlatList of ?id with $?rest)))
;------------------------------------------------------------------------------
(defrule RetractFlatListConstruction
			(Stage BuildFlatList $?)
			?f <- (Populate FlatList of ? with)
			=>
			(retract ?f))
;------------------------------------------------------------------------------
(defrule ExpandFlatListEntry
			"Takes a flat list and expands one of the elements of the contents if 
			it turns out that element is another flat list"
			(Stage ExpandFlatList $?)
			?id <- (object (is-a FlatList) (Contents $?a ?b $?c))
			(object (is-a FlatList) (ID ?b) (Contents $?j))
			=>
			(modify-instance ?id (Contents $?a $?j $?c)))
;------------------------------------------------------------------------------
(defrule ClaimOwnership
			"Asserts that a region owns another through a subset check. The first 
			flat list is checked to see if it is a _proper_ subset of the second"
			(Stage ClaimOwnership $?)
			?f0 <- (object (is-a FlatList) (ID ?i0) (Contents $?c0) (Parent ?p0))
			?f1 <- (object (is-a FlatList) (ID ?i1&~?i0) (Contents $?c1) 
								(Parent ?p1))
			(test (and (subsetp ?c0 ?c1) (> (length$ ?c1) (length$ ?c0))))
			=>
			(assert (claim ?p1 owns ?p0)))
;------------------------------------------------------------------------------
(defrule ClaimOwnershipOfBlocks
			"This rule is used to assert ownership claims on basic blocks"
			(Stage ClaimOwnership $?)
			?f0 <- (object (is-a FlatList) (Parent ?p) (Contents $? ?b $?))
			(object (is-a BasicBlock) (ID ?b))
			=>
			(assert (claim ?p owns ?b)))
;------------------------------------------------------------------------------
(defrule ClaimEquivalence
			"Asserts that two regions are equivalent if one flat list contains the
			same elements as a second one."
			(Stage ClaimOwnership $?)
			?f0 <- (object (is-a FlatList) (ID ?i0) (Contents $?c0) (Parent ?p0))
			?f1 <- (object (is-a FlatList) (ID ?i1&~?i0) (Contents $?c1) 
								(Parent ?p1))
			(test (and (subsetp ?c0 ?c1) (= (length$ ?c1) (length$ ?c0))))
			=>
			(assert (claim ?p1 equivalent ?p0)))
;------------------------------------------------------------------------------
(defrule MergeClaimsOfEquivalence
			"It is possible for two facts of equivalence to actually be the same 
			fact"
			(declare (salience -1))
			(Stage ClaimOwnership $?)
			?f0 <- (claim ?a equivalent ?b)
			?f1 <- (claim ?b equivalent ?a)
			=>
			(retract ?f0 ?f1)
			(assert (claim ?a equivalent ?b)))
;------------------------------------------------------------------------------
(defrule EliminateEquivalences-LoopFirst
			"If we find an equivalence then it means that a loop and a region 
			contain the same elements. Therefore the loop persists and the region 
			dies. The loop is the first entry."
			(declare (salience 1))
			(Stage Arbitrate $?)
			?f0 <- (claim ?a equivalent ?b)
			(object (is-a Loop) (ID ?a))
			(object (is-a Region&~Loop) (ID ?b))
			=>
			(retract ?f0)
			(assert (delete region ?b)
					  (replace ?b with ?a)))
;------------------------------------------------------------------------------
(defrule EliminateEquivalences-LoopSecond
			"If we find an equivalence then it means that a loop and a region 
			contain the same elements. Therefore the loop persists and the region
			dies. The loop is the second entry."
			(declare (salience 1))
			(Stage Arbitrate $?)
			?f0 <- (claim ?b equivalent ?a)
			(object (is-a Loop) (ID ?a))
			(object (is-a Region&~Loop) (ID ?b))
			=>
			(retract ?f0)
			(assert (delete region ?b)
					  (replace ?b with ?a)))
;------------------------------------------------------------------------------
; Now that we have asserted delete and replacement claims it's necessary to
; carry those claims out. First, we need to do the replacement actions
; We need to apply these changes to the flat lists associated with these
; objects to ensure that we do the proper replacement thing. 
; What we do is we use those replacement facts to retract the ownership claims
;
; Then we go through and perform partial replacement on the flat lists 
;------------------------------------------------------------------------------
(defrule RemoveStaleClaims-DeletionTargetClaimsAnother
			"We target claims of ownership that deal with a given region that has 
			to be replaced by another due to equivalence"
			(declare (salience 1))
			(Stage ResolveClaims $?)
			?f0 <- (replace ?old with ?new)
			?f1 <- (claim ?old owns ?other)
			=>
			(retract ?f0 ?f1)
			(assert (claim ?new owns ?other)
					  (replace ?old with ?new)))
;------------------------------------------------------------------------------
(defrule RemoveStaleClaims-AnotherClaimsDeletionTarget
			(declare (salience 1))
			(Stage ResolveClaims $?)
			?f0 <- (replace ?old with ?new)
			?f1 <- (claim ?other owns ?old)
			=>
			(retract ?f0 ?f1)
			(assert (claim ?other owns ?new)
					  (replace ?old with ?new)))
;------------------------------------------------------------------------------
(defrule RemoveStaleClaims-NoMoreConvergence
			"Retract replacement facts because there are no more claims to worry 
			about"
			(Stage ResolveClaims $?)
			?f0 <- (replace ?old with ?new)
			=>
			(retract ?f0))
;------------------------------------------------------------------------------
(defrule DeleteTargetRegion
			"Deletes the target region slated for deletion"
			(Stage ResolveClaims $?)
			?f0 <- (delete region ?r0)
			?region <- (object (is-a Region) (ID ?r0))
			=>
			(retract ?f0)
			(unmake-instance ?region))
;------------------------------------------------------------------------------
(defrule DeleteFlatLists 
			"Deletes all of the flat lists in a single rule fire"
			(Stage CleanUp-Merger $?)
			=>
			(progn$ (?fl (find-all-instances ((?list FlatList)) TRUE))
					  (unmake-instance ?fl)))
;------------------------------------------------------------------------------

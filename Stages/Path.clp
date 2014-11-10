;------------------------------------------------------------------------------
;Copyright (c) 2012-2014, Joshua Scoggins 
;All rights reserved.
;
;Redistribution and use in source and binary forms, with or without
;modification, are permitted provided that the following conditions are met:
;    * Redistributions of source code must retain the above copyright
;      notice, this list of conditions and the following disclaimer.
;    * Redistributions in binary form must reproduce the above copyright
;      notice, this list of conditions and the following disclaimer in the
;      documentation and/or other materials provided with the distribution.
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
; Rules devoted to starting the construction of ; a given path through a given 
; region.
;------------------------------------------------------------------------------
(defrule StartPathConstruction-NestedEntrance
			(declare (salience 3))
			(Stage Path $?)
			?r0 <- (object (is-a Region) (CanWavefrontSchedule TRUE) 
								(Entrances $? ?a $?) (ID ?n) (Contents $? ?z $?))
			(object (is-a Region) (ID ?z) (Parent ?n) (Entrances $? ?a $?))
			(object (is-a BasicBlock) (ID ?a) (Parent ~?n))
			=>
			(make-instance of Path (Parent ?n) (Contents ?z)))
;------------------------------------------------------------------------------
(defrule StartPathConstruction-BasicBlock
			(declare (salience 3))
			(Stage Path $?)
			?r0 <- (object (is-a Region) (CanWavefrontSchedule TRUE) 
								(Entrances $? ?a $?) (ID ?n))
			(object (is-a BasicBlock) (ID ?a) (Parent ?n))
			=>
			(make-instance of Path (Parent ?n) (Contents ?a)))
;------------------------------------------------------------------------------
; Contains rules that add paths that a given block is a part of 
; (path update rules)
;------------------------------------------------------------------------------
(defrule FAIL-UNFINISHED-PATHS 
			(Stage PathUpdate $?)
			(test (> (length$ 
						  (find-all-instances ((?path Path))
													 (neq TRUE ?path:Closed))) 0))
			=>
			(printout t "ERROR: Not all paths were closed!" crlf)
			(bind ?instances (find-all-instances ((?path Path))
															 (neq TRUE ?path:Closed))) 
			(foreach ?inst ?instances
						(send ?inst print))
			(facts)
			(exit))

(defrule AddPathToDiplomat
			"Adds the given path name to the target diplomat"
			(declare (salience 1))
			(Stage Path $?)
			(object (is-a Path) (Closed TRUE) (ID ?i) (Contents $? ?b $?))
			?d <- (object (is-a Diplomat) (ID ?b))
			(test (not (member$ ?i (send ?d get-Paths))))
			=>
			(slot-insert$ ?d Paths 1 ?i))

(defrule TraversePathForElementInjection
			(Stage PathUpdate $?)
			(object (is-a Path) (Closed TRUE) (ID ?p) (Contents $? ?a ?b $?))
			?o0 <- (object (is-a Diplomat) (ID ?a))
			?o1 <- (object (is-a Diplomat) (ID ?b))
			=>
			(if (not (member$ ?a (send ?o1 get-PreviousPathElements))) then
			  (slot-insert$ ?o1 PreviousPathElements 1 ?a))
			(if (not (member$ ?b (send ?o0 get-NextPathElements))) then
			  (slot-insert$ ?o0 NextPathElements 1 ?b)))
;------------------------------------------------------------------------------
; Debug rules (display output)
;------------------------------------------------------------------------------
(defrule PrintoutPaths
				 (declare (salience -100))
				 (Stage Path $?)
				 (Debug)
				 (Paths)
				 (object (is-a Hint) (Type Path) 
								 (Closed TRUE) 
								 (ID ?name) 
								 (Contents $?c)
								 (ExitBlock ?eb))
				 =>
				 (printout t "Path: " ?name " with contents " ?c " with exit block " ?eb crlf))
;------------------------------------------------------------------------------
; PathBuilding - Rules that build up the paths through the given region 
;------------------------------------------------------------------------------
(defrule AddToPath-Copy
			"Makes a copy of the current path object and concatenates the symbol 
			in question to the end of the list. This rule is fired when the 
			reference count of the given path object is greater than one."
			(declare (salience 1))
			(Stage Path $?)
			?fct <- (Add ?next to ?id)
			?hint <- (object (is-a Path) (Closed FALSE) (ID ?id) (Parent ?p) 
								  (ReferenceCount ?rc&:(> ?rc 1)))
			=>
			(send ?hint .DecrementReferenceCount)
			(retract ?fct)
			(make-instance of Path 
								(Parent ?p) 
								(Contents (send ?hint get-Contents) ?next)))
;------------------------------------------------------------------------------
(defrule AddToPath-Concat
			"Concatenates the next element of the path directly to the original 
			path object. This rule fires when the reference count of the path is 
			equal to one"
			(declare (salience 1))
			(Stage Path $?)
			?fct <- (Add ?next to ?id)
			?hint <- (object (is-a Path) (Closed FALSE) (ID ?id) 
								  (ReferenceCount 1))
			=>
			(retract ?fct)
			(modify-instance ?hint 
								  (ReferenceCount 0) 
								  (Contents (send ?hint get-Contents) ?next)))
;------------------------------------------------------------------------------
(defrule ClosePath-Update
			"Closes a path via an in-place update"
			(declare (salience 1))
			(Stage Path $?)
			?fct <- (Close ?id with ?bb)
			?hint <- (object (is-a Path) (Closed FALSE) (ID ?id) 
								  (ReferenceCount 1))
			=>
			(retract ?fct)
			(modify-instance ?hint 
								  (ReferenceCount 0) 
								  (Closed TRUE) 
								  (ExitBlock ?bb)))
;------------------------------------------------------------------------------
(defrule ClosePath-Copy
			"Closes a path by making a copy of the target path"
			(declare (salience 1))
			(Stage Path $?)
			?fct <- (Close ?id with ?bb)
			?hint <- (object (is-a Path) (Closed FALSE) (ID ?id) (Parent ?p)
								  (ReferenceCount ?rc&:(> ?rc 1)))
			=>
			(send ?hint .DecrementReferenceCount)
			(retract ?fct)
			(make-instance of Path 
								(Closed TRUE) 
								(ExitBlock ?bb) 
								(Contents (send ?hint get-Contents))))
;------------------------------------------------------------------------------
; PathTraversal - Rules that handle the act of traversing the region during 
; path construction 
;------------------------------------------------------------------------------
(defrule PathConstruction-BasicBlockToBasicBlock
			(declare (salience 2))
			(Stage Path $?)
			?path <- (object (is-a Path) (Parent ?p) (ID ?id) 
								  (Contents $?before ?curr) 
								  (Closed FALSE))
			(object (is-a BasicBlock) (ID ?curr) (Parent ?p) 
					  (Successors $? ?next $?))
			(object (is-a BasicBlock) (ID ?next) (Parent ?p))
			(test (not (member$ ?next (create$ $?before ?curr))))
			=>
			(send ?path .IncrementReferenceCount)
			(assert (Add ?next to ?id)))
;------------------------------------------------------------------------------
(defrule PathConstruction-RegionToBasicBlock
			(declare (salience 2))
			(Stage Path $?)
			?path <- (object (is-a Path) (Closed FALSE) (Parent ?p) (ID ?id)
								  (Contents $?before ?curr))
			(object (is-a Region) (ID ?curr) (Parent ?p) (Exits $? ?next $?))
			(object (is-a BasicBlock) (ID ?next) (Parent ?p))
			(test (not (member$ ?next (create$ $?before ?curr))))
			=>
			(send ?path .IncrementReferenceCount)
			(assert (Add ?next to ?id)))
;------------------------------------------------------------------------------
(defrule PathConstruction-BasicBlockToRegion
			(declare (salience 2))
			(Stage Path $?)
			?path <- (object (is-a Path) (Closed FALSE) (Parent ?p) (ID ?id) 
								  (Contents $?before ?curr))
			(object (is-a BasicBlock) (ID ?curr) (Parent ?p) 
					  (Successors $? ?s $?))
			(object (is-a Region) (Entrances $? ?s $?) (ID ?next) (Parent ?p))
			(test (not (member$ ?next (create$ $?before ?curr))))
			=>
			(send ?path .IncrementReferenceCount)
			(assert (Add ?next to ?id)))
;------------------------------------------------------------------------------
(defrule PathConstruction-RegionToRegion
			(declare (salience 2))
			(Stage Path $?)
			?path <- (object (is-a Path) (Closed FALSE) (Parent ?p) (ID ?id) 
								  (Contents $?before ?curr))
			(object (is-a Region) (ID ?curr) (Parent ?p) (Exits $? ?e $?))
			(object (is-a Region) (ID ?next) (Parent ?p) (Entrances $? ?e $?)) 
			(test (not (member$ ?next (create$ $?before ?curr))))
			; even if the entrance is part of a nested region...we really don't 
			; care it will still be accurate thanks to the way llvm does things
			=>
			(send ?path .IncrementReferenceCount)
			(assert (Add ?next to ?id)))
;------------------------------------------------------------------------------
(defrule PathConstruction-RegionNoExit
			"We are at a region that doesn't have an exit...Not sure if LLVM 
			allows this but let's handle it."
			(declare (salience 2))
			(Stage Path $?)
			?path <- (object (is-a Path) (Parent ?p) (ID ?i) (Closed FALSE) 
								  (Contents $? ?a))
			(object (is-a Region) (ID ?a) (Parent ?p) (Exits))
			=>
			(send ?path .IncrementReferenceCount)
			(assert (Close ?i with nil)))
;------------------------------------------------------------------------------
(defrule PathConstruction-BlockNoExit
			"We are at a basic block that has no successors...usually the end of a
			function"
			(declare (salience 2))
			(Stage Path $?)
			?path <- (object (is-a Path) (Parent ?p) (ID ?i) (Closed FALSE) 
								  (Contents $? ?a))
			(object (is-a BasicBlock) (ID ?a) (Parent ?p) (Successors))
			=>
			(send ?path .IncrementReferenceCount)
			(assert (Close ?i with nil)))
;------------------------------------------------------------------------------
(defrule PathConstruction-BasicBlockToBasicBlock-Cycle
			(declare (salience 2))
			(Stage Path $?)
			?path <- (object (is-a Path) (Parent ?p) (ID ?id) 
								  (Contents $?before ?curr) (Closed FALSE))
			(object (is-a BasicBlock) (ID ?curr) (Parent ?p) 
					  (Successors $? ?next $?))
			(object (is-a BasicBlock) (ID ?next) (Parent ?p))
			(test (member$ ?next (create$ $?before ?curr)))
			=>
			(send ?path .IncrementReferenceCount)
			(assert (Close ?id with ?next)))
;------------------------------------------------------------------------------
(defrule PathConstruction-RegionToBasicBlock-Cycle
			(declare (salience 2))
			(Stage Path $?)
			?path <- (object (is-a Path) (Closed FALSE) (Parent ?p) (ID ?id)
								  (Contents $?before ?curr))
			(object (is-a Region) (ID ?curr) (Parent ?p) (Exits $? ?next $?))
			(object (is-a BasicBlock) (ID ?next) (Parent ?p))
			(test (member$ ?next (create$ $?before ?curr)))
			=>
			(send ?path .IncrementReferenceCount)
			(assert (Close ?id with ?next)))
;------------------------------------------------------------------------------
(defrule PathConstruction-BasicBlockToRegion-Cycle
			(declare (salience 2))
			(Stage Path $?)
			?path <- (object (is-a Path) (Closed FALSE) (Parent ?p) (ID ?id) 
								  (Contents $?before ?curr))
			(object (is-a BasicBlock) (ID ?curr) (Parent ?p) (Successors $? ?s $?))
			(object (is-a Region) (ID ?next) (Parent ?p) (Entrances $? ?s $?))
			(test (member$ ?next (create$ $?before ?curr)))
			=>
			(send ?path .IncrementReferenceCount)
			(assert (Close ?id with ?next)))
;------------------------------------------------------------------------------
(defrule PathConstruction-RegionToRegion-Cycle
			(declare (salience 2))
			(Stage Path $?)
			?path <- (object (is-a Path) (Closed FALSE) (Parent ?p) (ID ?id) 
								  (Contents $?before ?curr))
			(object (is-a Region) (ID ?curr) (Parent ?p) (Exits $? ?e $?))
			(object (is-a Region) (ID ?next) (Parent ?p) (Entrances $? ?e $?)) 
			(test (member$ ?next (create$ $?before ?curr)))
			=>
			(send ?path .IncrementReferenceCount)
			(assert (Close ?next with ?id)))
;------------------------------------------------------------------------------
(defrule PathConstruction-BasicBlockToExit
			"Marks the current path as finished because we've reached an exit to 
			the current region"
			(declare (salience 2))
			(Stage Path $?)
			?path <- (object (is-a Path) (Parent ?p) (ID ?id) (Contents $? ?curr) 
								  (Closed FALSE))
			(object (is-a BasicBlock) (ID ?curr) (Parent ?p) (Successors $? ?e $?))
			(object (is-a Region) (ID ?p) (Exits $? ?e $?))
			;since the current block has an exit for this region we mark it
			=>
			(send ?path .IncrementReferenceCount)
			(assert (Close ?id with ?e)))
;------------------------------------------------------------------------------
(defrule PathConstruction-RegionToExit
			(declare (salience 2))
			(Stage Path $?)
			?path <- (object (is-a Path) (Closed FALSE) (Parent ?p) (ID ?id) 
								  (Contents $? ?c))
			(object (is-a Region) (ID ?c) (Parent ?p) (Exits $? ?e $?))
			(object (is-a Region) (ID ?p) (Exits $? ?e $?))
			; both the inner and outer regions have the same exit...thus the
			; curent nested region is a terminator for one path
			=>
			(send ?path .IncrementReferenceCount)
			(assert (Close ?id with ?e)))
;------------------------------------------------------------------------------

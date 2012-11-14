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
; PathTraversal.clp - Contains rules that handle the act of traversing the
; region during path construction 
; Written by Joshua Scoggins (6/20/2012)
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
			(test (not (member$ ?next (create$? before ?curr))))
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
			(test (not (member$ ?next (create$ $?before ?curr))))
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
			(test (not (member$ ?next (create$ $?before ?curr))))
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
			(test (not (member$ ?next (create$ $?before ?curr))))
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
			(test (not (member$ ?next (create$ $?before ?curr))))
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

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
;------------------------------------------------------------------------------
; BlockUpdates.clp - Contains rules that add paths that a given block is a part
; of
; Written by Joshua Scoggins (6/7/2012)
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

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
(defrule AssertIdentifySpansInitial
			(declare (salience 100))
			(Stage WavefrontSchedule $?)
			(Substage Identify $?)
			(object (is-a Hint) (Type Wavefront) (Parent ?r) (Contents $? ?e $?))
			;select only BasicBlocks
			(object (is-a BasicBlock) (ID ?e))
			=>
			(assert (Picked ?e for ?r)))
;------------------------------------------------------------------------------
(defrule IdentifySpanSkips-SplitBlock
			(declare (salience 50))
			(Stage WavefrontSchedule $?)
			(Substage Identify $?)
			?fct <- (Picked ?e for ?r)
			?bb <- (object (is-a BasicBlock) (ID ?e))
			(test (send ?bb .IsSplitBlock))
			=>
			(retract ?fct)
			(assert (Schedule ?e for ?r)))
;------------------------------------------------------------------------------
(defrule IdentifySpans
			(declare (salience 50))
			(Stage WavefrontSchedule $?)
			(Substage Identify $?)
			?fct <- (Picked ?e for ?r)
			?bb <- (object (is-a BasicBlock) (ID ?e) (Paths $?paths))
			(test (not (send ?bb .IsSplitBlock)))
			=>
			(retract ?fct)
			(modify-instance ?bb (IsOpen TRUE))
			(assert (Build paths for ?e from $?paths)))
;------------------------------------------------------------------------------
(defrule BuildUpPaths
			(declare (salience 25))
			(Stage WavefrontSchedule $?)
			(Substage Identify $?)
			?fct <- (Build paths for ?e from ?path $?paths)
			=>
			(retract ?fct)
			(assert (Build paths for ?e from $?paths)
					  (Check path ?path for block ?e)))
;------------------------------------------------------------------------------
(defrule RetractPathBuildUp
			(Stage WavefrontSchedule $?)
			(Substage Identify $?)
			?fct <- (Build paths for ? from)
			=>
			(retract ?fct))
;------------------------------------------------------------------------------
(defrule GetFactsBeforePathing
			(declare (salience 10000))
			(Debug)
			(Facts)
			(Stage WavefrontSchedule $?)
			(Substage Pathing $?)
			=>
			(printout t "BEFORE: Wavefront Pathing " crlf crlf)
			(facts)
			(printout t crlf crlf))
;------------------------------------------------------------------------------
(defrule DispatchDivideBlock
			(declare (salience 200))
			(Stage WavefrontSchedule $?)
			(Substage Pathing $?)
			?fct <- (Check path ?p for block ?e)
			(object (is-a Path) (ID ?p) (Contents $? ?e $?rest))
			(object (is-a BasicBlock) (ID ?e))
			=>
			(retract ?fct)
			(assert (Scan path ?p for block ?e with contents $?rest)))
;------------------------------------------------------------------------------
(defrule AnalyzePathElements
			(Stage WavefrontSchedule $?)
			(Substage Pathing $?)
			?fct <- (Scan path ?p for block ?e with contents ?curr $?rest)
			?bb <- (object (is-a BasicBlock) (ID ?curr))
			=>
			(retract ?fct)
			(if (= 0 (length$ (send ?bb get-Successors))) then
			  (assert (CompletelyInvalid blocks for ?e are ?curr))
			  (return))
			(if (send ?bb .IsSplitBlock) then
			  (assert (CompletelyInvalid blocks for ?e are $?rest)
						 (PotentiallyValid blocks for ?e are ?curr))
			  (return))
			(if (send ?bb get-HasCallBarrier) then
			  (assert (CompletelyInvalid blocks for ?e are $?rest)
						 (PotentiallyValid blocks for ?e are ?curr))
			  (return))
			(if (send ?bb get-HasMemoryBarrier) then
			  (assert (Element ?curr has a MemoryBarrier for ?e)))
			(assert (PotentiallyValid blocks for ?e are ?curr)
					  (Scan path ?p for block ?e with contents $?rest)))
;------------------------------------------------------------------------------
(defrule AnalyzePathElements-Region
			(Stage WavefrontSchedule $?)
			(Substage Pathing $?)
			?fct <- (Scan path ?p for block ?e with contents ?curr $?rest)
			?bb <- (object (is-a Region) (ID ?curr))
			=>
			(retract ?fct)
			(if (send ?bb get-HasCallBarrier) then
			  (assert (CompletelyInvalid blocks for ?e are $?rest)
						 (PotentiallyValid blocks for ?e are ?curr))
			  (return))
			(if (send ?bb get-HasMemoryBarrier) then
			  (assert (Element ?curr has a MemoryBarrier for ?e)))
			(assert (PotentiallyValid blocks for ?e are ?curr)
					  (Scan path ?p for block ?e with contents $?rest)))
;------------------------------------------------------------------------------
(defrule RetractCompletedFact
			(Stage WavefrontSchedule $?)
			(Substage Strip $?)
			?fct <- (Scan path ? for block ? with contents)
			=>
			(retract ?fct))
;------------------------------------------------------------------------------
(defrule PrintoutCompletedFacts 
			(declare (salience -999))
			(Debug)
			(Facts)
			(Stage WavefrontSchedule $?)
			(Substage Pathing $?)
			=>
			(printout t "AFTER: Wavefront Pathing" crlf crlf)
			(facts)
			(printout t crlf crlf))
;------------------------------------------------------------------------------
(defrule FAIL-PATHS-EXIST
			(declare (salience -2500))
			(Stage WavefrontSchedule $?)
			(Substage Strip $?)
			(Check path ?p for block ?e)
			=>
			(printout t "ERROR: DIDN'T RETRACT COMPLETED FACT: (Check path " ?p 
						 " for block " ?e ")" crlf)
			(facts)
			(exit))
;------------------------------------------------------------------------------

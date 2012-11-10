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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defrule InitializeWavefrontSchedulingFacts
			(declare (salience 1001))
			(Stage WavefrontSchedule $?)
			=>
			(assert (Substage Init 
									Identify 
									PhiIdentify
									PhiNode 
									PhiNodeUpdate
									Pathing 
									Strip 
									Inject 
									Acquire 
									Slice 
									AnalyzeInit 
                  GenerateAnalyze0
                  GenerateAnalyze
									Analyze 
									SliceAnalyze
									MergeInit 
									Merge 
									MergeUpdate 
									ReopenBlocks
									Ponder
									Rename 
									DependencyAnalysis 
									ScheduleObjectCreation 
									ScheduleObjectUsage
									ResetScheduling
									InitLLVMUpdate
									LLVMUpdate 
									AdvanceInit
									AdvanceIdentify
									Advance
									AdvanceEnd
									Update)))

(defrule NextWavefrontSchedulingSubstage
			(declare (salience -1000))
			(Stage WavefrontSchedule $?)
			?fct <- (Substage ? $?rest)
			=>
			(retract ?fct)
			(assert (Substage $?rest)))

(defrule RetractSubstageCompletely
			(declare (salience -1001))
			(Stage WavefrontSchedule $?)
			?fct <- (Substage)
			=>
			(retract ?fct))

(defrule InitializeWavefrontSchedulingForARegion-SelectBlockDirectly
			(declare (salience 2))
			(Stage WavefrontInit $?)
			(object (is-a Region) (CanWavefrontSchedule TRUE) (ID ?r) 
			 (Entrances $? ?e $?))
			(object (is-a BasicBlock) (ID ?e) (Parent ?r))
			=>
			(assert (Add ?e to wavefront for ?r)))

(defrule InitializeWavefrontSchedulingForARegion-AssertRegionInstead
			(declare (salience 2))
			(Stage WavefrontInit $?)
			(object (is-a Region) (CanWavefrontSchedule TRUE) (ID ?r) (Entrances $? ?e $?))
			(object (is-a BasicBlock) (ID ?e) (Parent ~?r))
			(object (is-a Region) (Parent ?r) (Entrances $? ?e $?) (ID ?q))
			=>
			(assert (Add ?q to wavefront for ?r)))

(defrule MergeWavefrontCreationContents-Convert-SingleSingle
			(declare (salience 1))
			(Stage WavefrontInit $?)
			?f0 <- (Add ?v0 to wavefront for ?r)
			?f1 <- (Add ?v1 to wavefront for ?r)
			(test (neq ?f0 ?f1))
			=>
			(retract ?f0 ?f1)
			(assert (Create wavefront for ?r containing ?v0 ?v1)))

(defrule MergeWavefrontCreationContents-Convert-MultiSingle
			(declare (salience 1))
			(Stage WavefrontInit $?)
			?f0 <- (Add ?v0 to wavefront for ?r)
			?f1 <- (Create wavefront for ?r containing $?g0)

			=>
			(retract ?f0 ?f1)
			(assert (Create wavefront for ?r containing $?g0 ?v0)))

(defrule MergeWavefrontCreationContents-Convert-MultiMulti
			(declare (salience 1))
			(Stage WavefrontInit $?)
			?f0 <- (Create wavefront for ?r containing $?g0)
			?f1 <- (Create wavefront for ?r containing $?g1)
			(test (neq ?f0 ?f1))
			=>
			(retract ?f0 ?f1)
			(assert (Create wavefront for ?r containing $?g0 $?g1)))

(defrule ConvertWavefrontCreationFact
			(declare (salience 1))
			(Stage WavefrontInit $?)
			?f0 <- (Add ?v0 to wavefront for ?r)
			=>
			(retract ?f0)
			(assert (Create wavefront for ?r containing ?v0)))

(defrule ConstructInitialWavefront
			(Stage WavefrontInit $?)
			?f0 <- (Create wavefront for ?r containing $?w)
			=>
			(retract ?f0)
			(make-instance (gensym*) of Wavefront (Parent ?r) (Contents ?w)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule ConstructPathAggregateForBlock 
			(declare (salience 100))
			(Stage WavefrontSchedule $?)
			(Substage Init $?)
			(object (is-a Hint) (Type Wavefront) (Parent ?r) (Contents $? ?e $?))
			?bb <- (object (is-a BasicBlock) (ID ?e)) 
			=>
			(assert (Propagate aggregates of ?e))
			(make-instance (gensym*) of PathAggregate (Parent ?e)
								(OriginalStopIndex (- (length$ (send ?bb get-Contents)) 1))))

(defrule ConstructPathAggregateForRegion
			(declare (salience 100))
			(Stage WavefrontSchedule $?)
			(Substage Init $?)
			(object (is-a Hint) (Type Wavefront) (Parent ?r) (Contents $? ?e $?))
			?bb <- (object (is-a Region) (ID ?e)) 
			=>
			(assert (Propagate aggregates of ?e))
			(make-instance (gensym*) of PathAggregate (Parent ?e)))

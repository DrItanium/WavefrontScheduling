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
; Wavefront Scheduling initialization rules
;------------------------------------------------------------------------------
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
									;ScheduleObjectCreation 
									;ScheduleObjectUsage
									;ResetScheduling
									;InitLLVMUpdate
									;LLVMUpdate 
									AdvanceInit
									AdvanceIdentify
									Advance
									AdvanceEnd
									Update)))
;------------------------------------------------------------------------------
(defrule NextWavefrontSchedulingSubstage
			(declare (salience -1000))
			(Stage WavefrontSchedule $?)
			?fct <- (Substage ? $?rest)
			=>
			(retract ?fct)
			(assert (Substage $?rest)))
;------------------------------------------------------------------------------
(defrule RetractSubstageCompletely
			(declare (salience -1001))
			(Stage WavefrontSchedule $?)
			?fct <- (Substage)
			=>
			(retract ?fct))
;------------------------------------------------------------------------------
(defrule InitializeWavefrontSchedulingForARegion-SelectBlockDirectly
			(declare (salience 2))
			(Stage WavefrontInit $?)
			(object (is-a Region) (CanWavefrontSchedule TRUE) (ID ?r) 
					  (Entrances $? ?e $?))
			(object (is-a BasicBlock) (ID ?e) (Parent ?r))
			=>
			(assert (Add ?e to wavefront for ?r)))
;------------------------------------------------------------------------------
(defrule InitializeWavefrontSchedulingForARegion-AssertRegionInstead
			(declare (salience 2))
			(Stage WavefrontInit $?)
			(object (is-a Region) (CanWavefrontSchedule TRUE) (ID ?r) 
					  (Entrances $? ?e $?))
			(object (is-a BasicBlock) (ID ?e) (Parent ~?r))
			(object (is-a Region) (Parent ?r) (Entrances $? ?e $?) (ID ?q))
			=>
			(assert (Add ?q to wavefront for ?r)))
;------------------------------------------------------------------------------
(defrule MergeWavefrontCreationContents-Convert-SingleSingle
			(declare (salience 1))
			(Stage WavefrontInit $?)
			?f0 <- (Add ?v0 to wavefront for ?r)
			?f1 <- (Add ?v1 to wavefront for ?r)
			(test (neq ?f0 ?f1))
			=>
			(retract ?f0 ?f1)
			(assert (Create wavefront for ?r containing ?v0 ?v1)))
;------------------------------------------------------------------------------
(defrule MergeWavefrontCreationContents-Convert-MultiSingle
			(declare (salience 1))
			(Stage WavefrontInit $?)
			?f0 <- (Add ?v0 to wavefront for ?r)
			?f1 <- (Create wavefront for ?r containing $?g0)

			=>
			(retract ?f0 ?f1)
			(assert (Create wavefront for ?r containing $?g0 ?v0)))
;------------------------------------------------------------------------------
(defrule MergeWavefrontCreationContents-Convert-MultiMulti
			(declare (salience 1))
			(Stage WavefrontInit $?)
			?f0 <- (Create wavefront for ?r containing $?g0)
			?f1 <- (Create wavefront for ?r containing $?g1)
			(test (neq ?f0 ?f1))
			=>
			(retract ?f0 ?f1)
			(assert (Create wavefront for ?r containing $?g0 $?g1)))
;------------------------------------------------------------------------------
(defrule ConvertWavefrontCreationFact
			(declare (salience 1))
			(Stage WavefrontInit $?)
			?f0 <- (Add ?v0 to wavefront for ?r)
			=>
			(retract ?f0)
			(assert (Create wavefront for ?r containing ?v0)))
;------------------------------------------------------------------------------
(defrule ConstructInitialWavefront
			(Stage WavefrontInit $?)
			?f0 <- (Create wavefront for ?r containing $?w)
			=>
			(retract ?f0)
			(make-instance of Wavefront (Parent ?r) (Contents ?w)))
;------------------------------------------------------------------------------
(defrule ConstructPathAggregateForBlock 
			(declare (salience 100))
			(Stage WavefrontSchedule $?)
			(Substage Init $?)
			(object (is-a Hint) (Type Wavefront) (Parent ?r) (Contents $? ?e $?))
			?bb <- (object (is-a BasicBlock) (ID ?e) (Contents $?c)) 
			=>
			(assert (Propagate aggregates of ?e))
			(make-instance of PathAggregate (Parent ?e) (OriginalStopIndex 
																		(- (length$ $?c) 1))))
;------------------------------------------------------------------------------
(defrule ConstructPathAggregateForRegion
			(declare (salience 100))
			(Stage WavefrontSchedule $?)
			(Substage Init $?)
			(object (is-a Hint) (Type Wavefront) (Parent ?r) (Contents $? ?e $?))
			?bb <- (object (is-a Region) (ID ?e)) 
			=>
			(assert (Propagate aggregates of ?e))
			(make-instance of PathAggregate (Parent ?e)))
;------------------------------------------------------------------------------
; Rules to select valid basic blocks for wavefront scheduling within a given 
; region
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
; Bulk fo the wavefront scheduling rules
;
;
;
; The idea for wavefront scheduling is that we pull a region, construct
; schedules for all of the blocks within the region, identify blocks that can
; relinquish control over instructions and move them up and out of the given
; block and into blocks on the wavefront.
;------------------------------------------------------------------------------
(defrule MergePotentiallyValidBlocks
         (declare (salience 2))
         (Stage WavefrontSchedule $?)
         (Substage Strip $?)
         ?pv0 <- (PotentiallyValid blocks for ?e are $?t)
         ?pv1 <- (PotentiallyValid blocks for ?e are $?q)
         (test (and (neq ?pv0 ?pv1) (subsetp ?t ?q)))
         =>
         (retract ?pv0 ?pv1)
         ;make sure that we get matches again!
         (assert (PotentiallyValid blocks for ?e are $?q)))
;------------------------------------------------------------------------------
(defrule MergeMemoryPotentiallyValidBlocks
         (Stage WavefrontSchedule $?)
         (Substage Strip $?)
         ?pv0 <- (MemoryPotentiallyValid blocks for ?e are $?t)
         ?pv1 <- (MemoryPotentiallyValid blocks for ?e are $?q)
         (test (and (neq ?pv0 ?pv1) (subsetp ?t ?q)))
         =>
         (retract ?pv0 ?pv1)
         ;make sure that we get matches again!
         (assert (MemoryPotentiallyValid blocks for ?e are $?q)))
;------------------------------------------------------------------------------
(defrule MergeCompletelyInvalid
         (declare (salience 1))
         (Stage WavefrontSchedule $?)
         (Substage Strip $?)
         ?pv0 <- (CompletelyInvalid blocks for ?e are $?t)
         ?pv1 <- (CompletelyInvalid blocks for ?e are $?q)
         (test (and (neq ?pv0 ?pv1) (subsetp ?t ?q)))
         =>
         (retract ?pv0 ?pv1)
         (assert (CompletelyInvalid blocks for ?e are $?q)))
;------------------------------------------------------------------------------
(defrule RetractPotentiallyValidBlocksThatAreCompletelyEnclosed
         (Stage WavefrontSchedule $?)
         (Substage Strip $?)
         (CompletelyInvalid blocks for ?e are $?t)
         ?pv1 <- (PotentiallyValid blocks for ?e are $?q)
         (test (subsetp ?q ?t))
         =>
         (retract ?pv1))
;------------------------------------------------------------------------------
(defrule StripoutIndividualElementsFromPotentiallyValid
         (declare (salience -1))
         (Stage WavefrontSchedule $?)
         (Substage Strip $?)
         ?f0 <- (PotentiallyValid blocks for ?e are $?before ?car $?rest)
         (CompletelyInvalid blocks for ?e are $? ?car $?)
         =>
         (retract ?f0)
         (assert (PotentiallyValid blocks for ?e are $?before $?rest)))
;------------------------------------------------------------------------------
(defrule RetractEmptyPotentiallyValid
         (declare (salience -100))
         (Stage WavefrontSchedule $?)
         (Substage Strip $?)
         ?f0 <- (PotentiallyValid blocks for ? are)
         =>
         (retract ?f0))
;------------------------------------------------------------------------------
(defrule InjectPotentiallyValidBlocks-Complete
         (Stage WavefrontSchedule $?)
         (Substage Inject $?)
         ?fct <- (PotentiallyValid blocks for ?e are $?blocks)
         ?pa <- (object (is-a PathAggregate) (Parent ?e) 
                        (PotentiallyValid $?pv))
         =>
         (retract ?fct)
         (bind ?pvs $?pv)
         (bind ?newIndex (+ (length$ ?pv) 1))
         (progn$ (?block ?blocks)
                 (if (not (member$ ?block ?pvs)) then 
                   (bind ?pvs (insert$ ?pvs ?newIndex ?block))
                   (bind ?newIndex (+ ?newIndex 1))))
         (modify-instance ?pa (PotentiallyValid ?pvs)))
;------------------------------------------------------------------------------
(defrule InjectCompletelyInvalidBlocks-Complete
         (Stage WavefrontSchedule $?)
         (Substage Inject $?)
         ?fct <- (CompletelyInvalid blocks for ?e are $?blocks)
         ?pa <- (object (is-a PathAggregate) (Parent ?e) 
                        (CompletelyInvalid $?ci))
         =>
         (retract ?fct)
         (bind ?cis $?ci)
         (bind ?newIndex (+ 1 (length$ ?ci)))
         (progn$ (?block ?blocks)
                 (if (not (member$ ?block ?cis)) then 
                   (bind ?cis (insert$ ?cis ?newIndex ?block))
                   (bind ?newIndex (+ 1 ?newIndex))))
         (modify-instance ?pa (CompletelyInvalid ?cis)))
;------------------------------------------------------------------------------
(defrule InterleavedInjectCompletelyInvalid-AndPotentiallyInvalidBlocks
         (declare (salience 1))
         (Stage WavefrontSchedule $?)
         (Substage Inject $?)
         ?f0 <- (CompletelyInvalid blocks for ?e are $?b0)
         ?f1 <- (PotentiallyValid blocks for ?e are $?b1)
         ?pa <- (object (is-a PathAggregate) (Parent ?e)
                        (CompletelyInvalid $?ci)
                        (PotentiallyValid $?pv))
         =>
         (retract ?f0 ?f1)
         (bind ?cis $?ci)
         (bind ?pvs $?pv)
         (bind ?i0 (+ 1 (length$ ?ci)))
         (bind ?i1 (+ 1 (length$ ?pv)))
         (progn$ (?b ?b0)
                 (if (not (member$ ?b ?cis)) then
                   (bind ?cis (insert$ ?cis ?i0 ?b))
                   (bind ?i0 (+ ?i0 1))))
         (progn$ (?b ?b1)
                 (if (not (member$ ?b ?pvs)) then
                   (bind ?pvs (insert$ ?pvs ?i1 ?b))
                   (bind ?i1 (+ ?i1 1))))
         (modify-instance ?pa (CompletelyInvalid ?cis) 
                          (PotentiallyValid ?pvs)))
;------------------------------------------------------------------------------
(defrule InjectMemoryBarrierBlocks 
         (Stage WavefrontSchedule $?)
         (Substage Inject $?)
         ;get the Mrs. Hitler birth certificate
         ?fct <- (Element ?t has a MemoryBarrier for ?e)
         ?pa <- (object (is-a PathAggregate) (Parent ?e))
         =>
         (retract ?fct)
         (if (not (member$ ?t (send ?pa get-MemoryBarriers))) then
           (slot-insert$ ?pa MemoryBarriers 1 ?t)))
;------------------------------------------------------------------------------
(defrule InjectCallBarrierBlocks 
         (Stage WavefrontSchedule $?)
         (Substage Inject $?)
         ;get the Mrs. Hitler birth certificate
         ?fct <- (Element ?t has a CallBarrier for ?e)
         ?pa <- (object (is-a PathAggregate) (Parent ?e))
         =>
         (retract ?fct)
         (if (not (member$ ?t (send ?pa get-CallBarriers))) then
           (slot-insert$ ?pa CallBarriers 1 ?t)))
;------------------------------------------------------------------------------
; now that we have a path aggregate we need to get the list of instruction
; CPV's that represent valid movable instructions for the given block on the
; wavefront. 
;------------------------------------------------------------------------------
(defrule SelectValidCPVs 
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         (object (is-a Wavefront) (Parent ?r) (Contents $? ?e $?))
         (object (is-a BasicBlock) (ID ?e) (IsOpen TRUE))
         ?pa <- (object (is-a PathAggregate) (ID ?ag) (Parent ?e)
                        (PotentiallyValid $?pv))
         =>
         (assert (For ?e find CPVs for $?pv)))
;------------------------------------------------------------------------------
(defrule FindValidCPVsForBlock
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (For ?e find CPVs for ?pv $?pvs)
         (object (is-a BasicBlock) (ID ?pv) (Contents $?instructions))
         =>
         (retract ?fct)
         (assert (For ?e find CPVs for $?pvs)
                 (Get CPVs out of ?pv for ?e using $?instructions)))
;------------------------------------------------------------------------------
(defrule SkipRegionsForFindingValidCPVsForBlock
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (For ?e find CPVs for ?pv $?pvs)
         (object (is-a Region) (ID ?pv)) 
         =>
         (retract ?fct)
         (assert (For ?e find CPVs for $?pvs)))
;------------------------------------------------------------------------------
(defrule RetractValidCPVsForBlock
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (For ? find CPVs for)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule IgnorePHIInstructions
         (declare (salience 1))
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using ?inst $?insts)
         (object (is-a PhiNode) (ID ?inst))
         =>
         (retract ?fct)
         (assert (Get CPVs out of ?pv for ?e using $?insts)))
;------------------------------------------------------------------------------
(defrule IgnoreCallInstructions
         (declare (salience 1))
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using ?inst $?insts)
         (object (is-a CallInstruction) (ID ?inst))
         =>
         (retract ?fct)
         (assert (Get CPVs out of ?pv for ?e using $?insts)))
;------------------------------------------------------------------------------
(defrule IgnoreTerminatorInstructions
         (declare (salience 1))
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using ?inst $?insts)
         (object (is-a TerminatorInstruction) (ID ?inst))
         =>
         (retract ?fct)
         (assert (Get CPVs out of ?pv for ?e using $?insts)))
;------------------------------------------------------------------------------
(defrule DisableInstructionsDependentOnDestinationPhis
         (declare (salience 2))
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using ?inst $?insts)
         ;make sure that the parent block is the same
         (object (is-a Instruction) (ID ?inst) (Parent ?p) 
                 (DestinationRegisters $? ?reg $?))
         (object (is-a PhiNode) (ID ?reg) (Parent ?p))
         =>
         (retract ?fct)
         (assert (Get CPVs out of ?pv for ?e using $?insts)))
;------------------------------------------------------------------------------
(defrule DisableInstructionsDependentOnLocalPhis
         (declare (salience 2))
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using ?inst $?insts)
         ;make sure that the parent block is the same 
         (object (is-a Instruction) (ID ?inst) (LocalDependencies $? ?reg $?))
         (object (is-a PhiNode) (ID ?reg))
         =>
         (retract ?fct)
         (assert (Get CPVs out of ?pv for ?e using $?insts)))
;------------------------------------------------------------------------------
(defrule TagValidCPVs
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using ?inst $?insts)
         ?i <- (object (is-a Instruction) (ID ?inst) (IsTerminator FALSE) 
                       (HasCallDependency FALSE))
         =>
         (retract ?fct)
         (assert (Get CPVs out of ?pv for ?e using $?insts)
                 (Marked ?inst as valid for block ?e)))
;------------------------------------------------------------------------------
(defrule RetractDrainedGetCPVFacts
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule ReloadCPVIntoNewAggregate
         "Put the CPV that has already been created into the target path 
         aggregate"
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Marked ?inst as valid for block ?e)
         (object (is-a CompensationPathVector) (Parent ?inst) (ID ?cpvID))
         ?agObj <- (object (is-a PathAggregate) (ID ?ag) (Parent ?e))
         (object (is-a Instruction) (ID ?inst) (NonLocalDependencies $?nlds)
                 (DestinationRegisters ?reg) (Class ?class))
         (test (not (member$ ?cpvID 
                             (send ?agObj 
                                   get-ImpossibleCompensationPathVectors))))
         =>
         (retract ?fct)
         (if (not (member$ ?inst (send ?agObj get-InstructionList))) then 
           (slot-insert$ ?agObj InstructionList 1 ?inst))
         (if (not (member$ ?reg (send ?agObj get-InstructionList))) then
           (slot-insert$ ?agObj InstructionList 1 ?reg))
         (progn$ (?nld ?nlds)
                 (if (not (member$ ?nld 
                                   (send ?agObj 
                                         get-ScheduledInstructions))) then
                   (slot-insert$ ?agObj ScheduledInstructions 1 ?nld)))
         (slot-insert$ ?agObj CompensationPathVectors 1 ?cpvID))
;------------------------------------------------------------------------------
(defrule CPVIsImpossible
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Marked ?inst as valid for block ?e)
         (object (is-a CompensationPathVector) (Parent ?inst) (ID ?cpvID))
         ?agObj <- (object (is-a PathAggregate) (ID ?ag) (Parent ?e))
         (object (is-a Instruction) (ID ?inst) (NonLocalDependencies $?nlds)
                 (DestinationRegisters ?reg) (Class ?class))
         (test (member$ ?cpvID (send ?agObj 
                                     get-ImpossibleCompensationPathVectors)))
         =>
         ;add the non-local dependencies
         (progn$ (?nld ?nlds)
                 (if (not (member$ ?nld (send ?agObj 
                                              get-ScheduledInstructions))) then
                   (slot-insert$ ?agObj ScheduledInstructions 1 ?nld)))
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule MakeCPV 
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Marked ?inst as valid for block ?e)
         (not (exists (object (is-a CompensationPathVector) (Parent ?inst))))
         (object (is-a Instruction) (Class ?class) (ID ?inst) (Parent ?pv) 
                 (DestinationRegisters ?reg) (NonLocalDependencies $?nlds))
         (object (is-a BasicBlock) (ID ?pv) (Paths $?paths))
         ?pa <- (object (is-a PathAggregate) (ID ?ag) (Parent ?e))
         =>
         ; We need to disable the stores from moving when their dependencies
         ; 
         ; YOU DON'T EVEN WANT TO KNOW WHAT I'M GOING TO DO TO YOU
         (retract ?fct)
         (bind ?name (gensym*))
         (slot-insert$ ?pa CompensationPathVectors 1 ?name)
         (make-instance ?name of CompensationPathVector (Parent ?inst) 
                        (Paths $?paths) (OriginalBlock ?pv))
         (if (not (member$ ?inst (send ?pa get-InstructionList))) then 
           (slot-insert$ ?pa InstructionList 1 ?inst))
         (if (not (member$ ?reg (send ?pa get-InstructionList))) then
           (slot-insert$ ?pa InstructionList 1 ?reg))
         (progn$ (?nld ?nlds)
                 (if (not (member$ ?nld (send ?pa get-ScheduledInstructions))) 
                   then (slot-insert$ ?pa ScheduledInstructions 1 ?nld))))
;------------------------------------------------------------------------------
; Now we go through and attempt to schedule the instruction represented by 
; each CPV into the block on the wavefront. I call this stage merge. I had some
; far raunchier names but this is my thesis. Some of the potential names were
; OneeChanTheresNoWayThatCanFit, ImAMexiCan, Copulation, and many more.
; 
; I guess the biggest question would be why? And my answer would be why not?
; These terms just popped into my head.
;------------------------------------------------------------------------------
(defrule SetifyInstructionList
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?pa <- (object (is-a PathAggregate) (InstructionList $?a ?b $?c ?b $?d))
         =>
         (modify-instance ?pa (InstructionList $?a ?b $?c $?d)))
;------------------------------------------------------------------------------
(defrule GenerateInitialSliceFactsForElementsOnTheWavefront 
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         (object (is-a Wavefront) (Parent ?r) (Contents $? ?e $?))
         (object (is-a BasicBlock) (ID ?e) (IsOpen TRUE))
         (object (is-a PathAggregate) (Parent ?e) 
                 (CompensationPathVectors $?cpv))
         (test (> (length$ ?cpv) 0))
         =>
         (assert (Generate slices for block ?e in ?r using $?cpv)))
;------------------------------------------------------------------------------
(defrule GenerateFactForSlicesFromCPV
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slices for block ?e in ?r using ?cpv $?cpvs)
         (object (is-a CompensationPathVector) (ID ?cpv) (Parent ?i)
                 (Paths $?paths))
         (object (is-a Instruction) (ID ?i) (Parent ?b))
         =>
         (retract ?fct)
         (assert (Generate slices for block ?e in ?r using $?cpvs)
                 (Generate slices for block ?e in ?r with cpv ?cpv with stop 
                           block ?b using paths $?paths)))
;------------------------------------------------------------------------------
(defrule RetractEmptySlicesCreationFact
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slices for block ? in ? using)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule QueryCanCreateSliceForPath
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slices for block ?e in ?r with cpv ?cpv with stop 
                           block ?b using paths ?path $?paths)
         (object (is-a Path) (ID ?path) (Contents $? ?e $?))
         ;(test (member$ ?e ?z))
         =>
         (retract ?fct)
         (assert (Generate slice for block ?e in ?r with cpv ?cpv with stop 
                           block ?b using path ?path)
                 (Generate slices for block ?e in ?r with cpv ?cpv with stop 
                           block ?b using paths $?paths)))
;------------------------------------------------------------------------------
(defrule QueryCantCreateSliceForPath
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slices for block ?e in ?r with cpv ?cpv with stop 
                           block ?b using paths ?path $?paths)
         (object (is-a Path) (ID ?path) (Contents $?z))
         (test (not (member$ ?e ?z)))
         =>
         (retract ?fct)
         (assert (Generate slices for block ?e in ?r with cpv ?cpv with stop 
                           block ?b using paths $?paths)))
;------------------------------------------------------------------------------
(defrule TryConstructNewSlice
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slice for block ?e in ?r with cpv ?cpv with stop 
                           block ?b using path ?path)
         (not (exists (object (is-a Slice) (Parent ?b) (TargetPath ?path) 
                              (TargetBlock ?e))))
         (object (is-a Path) (ID ?path) (Contents $? ?e $?slice ?b $?))
         =>
         (retract ?fct)
         (make-instance (gensym*) of Slice (Parent ?b) (TargetPath ?path)
                        (TargetBlock ?e) (Contents $?slice)))
;------------------------------------------------------------------------------
(defrule SliceAlreadyExists
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slice for block ?e in ?r with cpv ?cpv with stop 
                           block ?b using path ?path)
         (exists (object (is-a Slice) (Parent ?b) (TargetPath ?path) 
                         (TargetBlock ?e)))
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule RemoveSliceAnalysisFact
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slices for block ? in ? with cpv ? with stop block ? 
                           using paths)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
;only construct slices as we see fit as we can just reference them again.
;------------------------------------------------------------------------------
; Now that we have slices constructed it's time to run through the
; analyze-merge cycle. First up, analyze. In this phase we need to see if it
; is possible to schedule into the block. Actually, I can see that we already
; did the hard work as any regions that would have prevented code from moving
; up would have already prevented the block from being selected. Thus we should
; just check to see if we have a local dependency
;------------------------------------------------------------------------------
(defrule InitialCPVSetupForPathAggregate
         "Load all of the compensation path vectors for the given path 
         aggregate into the aggregates TargetCompensationPathVectors 
         multifield"
         (Stage WavefrontSchedule $?)
         (Substage AnalyzeInit $?)
         (object (is-a Wavefront) (Contents $? ?blkID $?))
         ?agObj <- (object (is-a PathAggregate) (Parent ?blkID) 
                           (CompensationPathVectors $?cpvIDs))
         (test (> (length$ ?cpvIDs) 0))
         =>
         (modify-instance ?agObj (TargetCompensationPathVectors $?cpvIDs)))
;------------------------------------------------------------------------------
(defrule SetifyTargetCompensationPathVectors
         (Stage WavefrontSchedule $?)
         (Substage AnalyzeInit $?)
         ?pa <- (object (is-a PathAggregate) 
                        (TargetCompensationPathVectors $?a ?b $?c ?b $?d))
         =>
         (modify-instance ?pa (TargetCompensationPathVectors $?a ?b $?c $?d)))
;------------------------------------------------------------------------------
(defrule SelectCPVForAnalysis
         (Stage WavefrontSchedule $?)
         (Substage GenerateAnalyze0 $?)
         (object (is-a Wavefront) (Parent ?r) (Contents $? ?e $?))
         ?bb <- (object (is-a BasicBlock) (ID ?e) (IsOpen TRUE))
         ;(not (exists (Schedule ?e for ?r)))
         ?agObj <- (object (is-a PathAggregate) (Parent ?e) 
                           (TargetCompensationPathVectors $?cpvs))
         (test (> (length$ ?cpvs) 0))
         =>
         ;clear out the cpvs
         (modify-instance ?agObj (TargetCompensationPathVectors))
         (bind ?result (create$))
         (progn$ (?cpv $?cpvs)
                 (bind ?det FALSE)
                 (progn$ (?p (send (symbol-to-instance-name ?cpv) get-Paths))
                         (if ?det then 
                           (break)
                           else 
                           (bind ?o2 (symbol-to-instance-name ?p))
                           (bind ?det 
                                 (or ?det 
                                     (member$ ?e 
                                              (send ?o2 get-Contents))))))
                 (if ?det then 
                   (bind ?result (create$ ?result ?cpv))))
         (assert (Analyze block ?e for ?r using cpvs $?result)))
;------------------------------------------------------------------------------
(defrule SegmentCPVsApart
         (Stage WavefrontSchedule $?)
         (Substage GenerateAnalyze $?)
         ?fct <- (Analyze block ?e for ?r using cpvs ?cpv $?cpvs)
         (object (is-a BasicBlock) (ID ?e))
         (object (is-a CompensationPathVector) (ID ?cpv) (Parent ?i))
         =>
         ;(printout t "Analyze instruction " ?i " { associated cpv " ?cpv 
         ; " } for " ?e crlf)
         (retract ?fct)
         (assert (Analyze block ?e for ?r using cpvs $?cpvs)
                 (Analyze instruction ?i { associated cpv ?cpv } for ?e)))
;------------------------------------------------------------------------------
(defrule RetractCPVSegmentationFact
         (Stage WavefrontSchedule $?)
         (Substage GenerateAnalyze $?)
         ?fct <- (Analyze block ? for ? using cpvs)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule TargetInstructionDoesNotHaveACorrespondingCPV
         "Sometimes it turns out that sometimes store instructions will add 
         certain instructions to the instruction list even though they don't 
         have a valid CPV.  This rule removes those elements from the path 
         aggregate"
         (Stage WavefrontSchedule $?)
         (Substage GenerateAnalyze $?)
         ?pa <- (object (is-a PathAggregate) (Parent ?e) 
                        (InstructionList $?b ?a $?c))
         (not (exists (object (is-a CompensationPathVector) (Parent ?a))))
         =>
         ;(printout t "NOTE: Removed " ?a " from the path aggregate of " ?e 
         ;            " because a CPV wasn't tied to the instruction" crlf)
         (modify-instance ?pa (InstructionList $?b $?c)))
;------------------------------------------------------------------------------
(defrule TargetInstructionIsNotRegisteredWithTheTargetPathAggregate
         "Sometimes it turns out that sometimes store instructions will add 
         certain instructions to the instruction list even though they don't 
         have a valid CPV registered with the path aggregate. This rule removes 
         those elements from the path aggregate"
         (Stage WavefrontSchedule $?)
         (Substage GenerateAnalyze $?)
         ?pa <- (object (is-a PathAggregate) (Parent ?e) 
                        (InstructionList $?b ?a $?c)
                        (CompensationPathVectors $?cpvs))
         (object (is-a CompensationPathVector) (Parent ?a) (ID ?id))
         (test (not (member$ ?id $?cpvs)))
         =>
         ;(printout t "NOTE: Removed " ?a " from the path aggregate of " ?e 
         ;" because the corresponding CPV wasn't registered with the path"
         ;" aggregate" crlf)
         (modify-instance ?pa (InstructionList $?b $?c)))
;------------------------------------------------------------------------------
(defrule TargetCPVIsImpossibleToScheduleIntoTargetBlock
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Analyze instruction ?i { associated cpv ?cpv } for ?e)
         ?agObj <- (object (is-a PathAggregate) (Parent ?e) 
                           (InstructionList $?il)
                           (ScheduledInstructions $?sched))
         (object (is-a Instruction) (ID ?i) (LocalDependencies $?ld)
                 (NonLocalDependencies $?nld))
         (test (not (and (subsetp ?ld ?il)
                         (subsetp ?nld ?sched))))
         =>
         ;(printout t ?i " is impossible to schedule into " ?e crlf)
         ;(printout t "Local Dependencies = " ?ld crlf)
         ;(printout t "Non Local Dependencies = " ?nld crlf)
         ;(printout t "Instruction List = " ?il crlf)
         ;(printout t "Schedule = " ?sched crlf)
         (retract ?fct)
         (bind ?ind (member$ ?i ?il))
         (if ?ind then
           (slot-delete$ ?agObj InstructionList ?ind ?ind))
         (assert (Cant schedule ?cpv for ?e ever)))
;------------------------------------------------------------------------------

(defrule TargetCPVCantBeScheduledIntoTargetBlockYet
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Analyze instruction ?i { associated cpv ?cpv } for ?e)
         ?paObj <- (object (is-a PathAggregate) (Parent ?e) 
                           (InstructionList $?il)
                           (ScheduledInstructions $?sched)
                           (CompensationPathVectors $?cpvs))
         (object (is-a Instruction) (ID ?i) (LocalDependencies $?ld) 
                 (NonLocalDependencies $?nld) (Parent ?parent))
         (test (and (not (subsetp ?ld ?sched))
                    (subsetp ?ld ?il)
                    (subsetp ?nld ?sched)))
         =>
         ;(printout t "Can't schedule " ?i " into " ?e " right now!" crlf)
         ;(printout t "Non Local Dependencies = " ?nld crlf)
         ;(printout t "Local Dependencies = " ?ld crlf)
         ;(printout t "Scheduled = " ?sched crlf)
         ;(printout t "Instruction List = " ?il crlf)
         ;(printout t "From = " ?parent crlf)
         ;(printout t "CPVS = " ?cpvs crlf)
         ;(facts)
         (retract ?fct)
         (assert (Cant schedule ?cpv for ?e now)))
;------------------------------------------------------------------------------
(defrule TargetCPVNeedsToBeSliceAnalyzed
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Analyze instruction ?i { associated cpv ?cpv } for ?e)
         (object (is-a PathAggregate) (Parent ?e) 
                 (ScheduledInstructions $?sched))
         (object (is-a Instruction) (ID ?i) (Parent ?b) 
                 (LocalDependencies $?ld))
         (test (subsetp ?ld ?sched))
         (object (is-a CompensationPathVector) (ID ?cpv) (Paths $?paths))
         =>
         (retract ?fct)
         (bind ?validPaths (create$))
         (foreach ?z ?paths
                  (bind ?obj (instance-name (symbol-to-instance-name ?z)))
                  (if (member$ ?e (send ?obj get-Contents)) then
                    (bind ?validPaths (create$ ?validPaths ?z))))
         (if (> (length$ ?validPaths) 0) then
           (assert (Pull slices for range ?e to ?b for instruction ?i { 
                         associated cpv ?cpv } using paths $?validPaths))))
;------------------------------------------------------------------------------
(defrule CreateSliceSegments
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Pull slices for range ?e to ?b for instruction ?i {
                       associated cpv ?cpv } using paths ?path $?paths)
         (object (is-a Slice) (Parent ?b) (TargetBlock ?e) (TargetPath ?path)
                 (ID ?s))
         =>
         (retract ?fct)
         (assert (Pull slices for range ?e to ?b for instruction ?i {
                       associated cpv ?cpv } using paths $?paths)
                 (Analyze slice ?s for ?e and cpv ?cpv)))
;------------------------------------------------------------------------------
(defrule RetractSliceSegmenterFact
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Pull slices for range ? to ? for instruction ? {
                       associated cpv ? } using paths)
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule FAILURE-MISSING-SLICE 
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Pull slices for range ?e to ?b for instruction ?i {
                       associated cpv ?cpv } using paths ?path $?paths)
         (not (exists (object (is-a Slice) (Parent ?b) (TargetBlock ?e)
                              (TargetPath ?path))))
         =>
         (facts)
         (printout t "ERROR: Couldn't find an associated slice for " crlf
                   "TargetBlock = " ?e crlf
                   "Parent = " ?b crlf
                   "TargetPath = " ?path crlf
                   "TargetPath contents = " (send (symbol-to-instance-name
                                                    ?path) get-Contents) crlf
                   "Rest of paths are = " $?paths crlf)
         (exit))

;------------------------------------------------------------------------------
(defrule MergeSliceAnalysisFacts-SingleSingle
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?f0 <- (Analyze slice ?s0 for ?e and cpv ?cpv)
         ?f1 <- (Analyze slice ?s1&~?s0 for ?e and cpv ?cpv)
         ;(test (neq ?f0 ?f1))
         =>
         (retract ?f0 ?f1)
         (assert (Analyze in ?e using cpv ?cpv and slices ?s0 ?s1)))
;------------------------------------------------------------------------------
(defrule ConvertSingleSliceRule
         (declare (salience -3))
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?f0 <- (Analyze slice ?s0 for ?e and cpv ?cpv)
         =>
         (retract ?f0)
         (assert (Analyze in ?e using cpv ?cpv and slices ?s0)))
;------------------------------------------------------------------------------
(defrule MergeSliceAnalysisFacts-MultiMulti
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?f0 <- (Analyze in ?e using cpv ?cpv and slices $?q)
         ?f1 <- (Analyze in ?e using cpv ?cpv and slices $?z)
         (test (neq ?f0 ?f1)) 
         =>
         (retract ?f0 ?f1)
         (assert (Analyze in ?e using cpv ?cpv and slices $?z $?q)))
;------------------------------------------------------------------------------
(defrule SetifyAnalyzeSlicesFact
         (declare (salience -1))
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices $?a ?b $?c ?b $?d)
         =>
         (retract ?fct)
         (assert (Analyze in ?e using cpv ?cpv and slices $?a ?b $?c $?d)))
;------------------------------------------------------------------------------
(defrule ERROR-ANALYSIS-FAILURE
         (declare (salience -900))
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         (Analyze instruction ?i for ?blkID)
         ?inst <- (object (is-a Instruction) (ID ?i))
         (object (is-a PathAggregate) (Parent ?blkID) 
                 (ScheduledInstructions $?si))
         ?cpv <- (object (is-a CompensationPathVector) (Parent ?i))
         =>
         (printout t "ERROR: ANALYZE INSTRUCTION " ?i " WASN'T MATCHED!!!" crlf
                   "SCHEDULED INSTRUCTIONS: " $?si crlf)
         (send ?inst print)
         (printout t crlf)
         (send ?cpv print)
         (exit))
;------------------------------------------------------------------------------
; now that we have a list of slices to look at it's time to check and see if
; the given cpv can be moved up based on the slice. If it can't then assert 
; a fact that says as much
;------------------------------------------------------------------------------
(defrule RetractSliceAnalysis
         "Retract all slice analysis if it turns out there is a failure fact"
         (Stage WavefrontSchedule $?)
         (Substage SliceAnalyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices $?)
         (exists (Cant schedule ?cpv for ?e ?))
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule AnalyzeSliceContentsForFailure-ProducerLowerThanTargetBlock
         "Does a check to make sure that non local dependencies prevent an 
         instruction from being moved upward into the target block"
         (Stage WavefrontSchedule $?)
         (Substage SliceAnalyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices ?s $?ss)
         (object (is-a Slice) (ID ?s) (TargetBlock ?e) (Parent ?b)
                 (Contents $? ?element $?))
         (object (ID ?element) (Produces $? ?nld $?))
         (object (is-a CompensationPathVector) (ID ?cpv) (Parent ?i))
         (object (is-a Instruction) (ID ?i) (DestinationRegisters ?dr)
                 (NonLocalDependencies $? ?nld $?))
         ?agObj <- (object (is-a PathAggregate) (Parent ?e))
         =>
         ; (printout t "Failed Instruction " ?i " because producer is lower "
         ;             "than block " ?e " on the wavefront" crlf)
         (retract ?fct)
         (bind ?ind (member ?i (send ?agObj get-InstructionList)))
         (if (neq FALSE ?ind) then
           (slot-delete$ ?agObj InstructionList ?ind ?ind))
         (assert (Cant schedule ?cpv for ?e ever)))
;------------------------------------------------------------------------------
(defrule AnalyzeSliceContentsForFailure-CallBarrier
         (Stage WavefrontSchedule $?)
         (Substage SliceAnalyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices ?s $?ss)
         (object (is-a Slice) (ID ?s) (TargetBlock ?e) (Parent ?b)
                 (Contents $? ?element $?))
         (object (ID ?element) (HasCallBarrier TRUE))
         (object (is-a CompensationPathVector) (ID ?cpv) (Parent ?i))
         (object (is-a Instruction) (ID ?i) (DestinationRegisters ?dr))
         ?agObj <- (object (is-a PathAggregate) (Parent ?e))
         =>
         (retract ?fct)
         ;(printout t "Removed " ?i " from being scheduled - "
         ;            "Call Barrier" crlf)
         (bind ?ind (member$ ?i (send ?agObj get-InstructionList)))
         (if (neq FALSE ?ind) then 
           (slot-delete$ ?agObj InstructionList ?ind ?ind))
         (assert (Cant schedule ?cpv for ?e ever)))
;------------------------------------------------------------------------------
(defrule SliceTargetHasMemoryBarrier
         "The given slice has an element that contains a memory barrier. 
         A memory barrier is only created when analysis has failed to ascertain
         what is being read from or written to in memory."
         (Stage WavefrontSchedule $?)
         (Substage SliceAnalyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices ?s $?ss)
         (object (is-a Slice) (ID ?s) (TargetBlock ?e) 
                 (Parent ?b) (Contents $? ?element $?))
         (object (is-a CompensationPathVector) (ID ?cpv) (Parent ?i))
         (object (is-a LoadInstruction|StoreInstruction) (ID ?i)
                 (DestinationRegisters ?dr))
         (object (ID ?element) (HasMemoryBarrier TRUE))
         ?agObj <- (object (is-a PathAggregate) (Parent ?e))
         =>
         (retract ?fct)
         ;(printout t "Removed " ?i " from being scheduled into " ?e 
         ;            " - MemoryBarrier" crlf)
         (bind ?ind (member$ ?i (send ?agObj get-InstructionList)))
         (if (neq FALSE ?ind) then 
           (slot-delete$ ?agObj InstructionList ?ind ?ind))
         (assert (Cant schedule ?cpv for ?e ever)))
;------------------------------------------------------------------------------
(defrule SliceTargetDoesntHaveMemoryBarrier-ModifiesSameMemory
         "The given slice has an element that contains a entry in the WritesTo 
         list that is the same thing as the given load or store instruction"
         (Stage WavefrontSchedule $?)
         (Substage SliceAnalyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices ?s $?ss)
         (object (is-a Slice) (ID ?s) (TargetBlock ?e) 
                 (Parent ?b) (Contents $? ?element $?))
         (object (is-a CompensationPathVector) (ID ?cpv) (Parent ?i))
         ?instruction <- (object (is-a LoadInstruction|StoreInstruction) 
                                 (ID ?i)
                                 (MemoryTarget ?mt) 
                                 (DestinationRegisters ?dr))
         (object (ID ?element) (HasMemoryBarrier FALSE) (HasCallBarrier FALSE)
                 (WritesTo $? ?mt $?))
         ?agObj <- (object (is-a PathAggregate) (Parent ?e))
         =>
         (retract ?fct)
         (bind ?ind (member$ ?i (send ?agObj get-InstructionList)))
         (if (neq FALSE ?ind) then 
           (slot-delete$ ?agObj InstructionList ?ind ?ind))
         ;(printout t "Removed " ?i " from being scheduled into " 
         ;					 ?e " because " ?element " - ModifiesSameMemory" crlf)
         (assert (Cant schedule ?cpv for ?e ever)))
;------------------------------------------------------------------------------
(defrule SliceTargetDoesntHaveMemoryBarrier-HasUnknownReference
         "Does now allow loads or stores to be moved above the given element
         regardless of if a memory barrier exists or not. This is because there
         is an unknown loader element"
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices ?s $?ss)
         (object (is-a Slice) (ID ?s) (TargetBlock ?e) 
                 (Parent ?cpv) (Contents $? ?element $?))
         (object (is-a CompensationPathVector) (ID ?cpv) (Parent ?i))
         (object (is-a LoadInstruction|StoreInstruction) (ID ?i) 
                 (Parent ?q) (DestinationRegisters ?dr))
         (object (ID ?element) (WritesTo $? UNKNOWN $?))
         ?agObj <- (object (is-a PathAggregate) (Parent ?e))
         =>
         (retract ?fct)
         ;(printout t "Removed " ?i " from being scheduled from block " ?q 
         ;					 " unknown reference" crlf)
         (bind ?ind (member$ ?i (send ?agObj get-InstructionList)))
         (if (neq FALSE ?ind) then 
           (slot-delete$ ?agObj InstructionList ?ind ?ind))
         (assert (Cant schedule ?cpv for ?e ever)))
;------------------------------------------------------------------------------
(defrule CanScheduleIntoBlockOnSlice
         (declare (salience -2))
         (Stage WavefrontSchedule $?)
         (Substage SliceAnalyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices ?s $?ss)
         =>
         (retract ?fct)
         (assert (Analyze in ?e using cpv ?cpv and slices $?ss)))
;------------------------------------------------------------------------------
(defrule CanScheduleInstructionThisIteration
         (declare (salience -3))
         (Stage WavefrontSchedule $?)
         (Substage SliceAnalyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices)
         =>
         (retract ?fct)
         (assert (Can schedule ?cpv for ?e)))
;------------------------------------------------------------------------------
(defrule AddCPVToSuccessList
         (Stage WavefrontSchedule $?)
         (Substage MergeInit $?)
         ?fct <- (Can schedule ?cpvID for ?blkID)
         ?agObj <- (object (is-a PathAggregate) (Parent ?blkID))
         =>
         (retract ?fct)
         (slot-insert$ ?agObj MovableCompensationPathVectors 1 ?cpvID))
;------------------------------------------------------------------------------
(defrule FailCPVForNow
         (Stage WavefrontSchedule $?)
         (Substage MergeInit $?)
         ?fct <- (Cant schedule ?cpvID for ?blkID now)
         ?agObj <- (object (is-a PathAggregate) (Parent ?blkID))
         =>
         (retract ?fct)
         (slot-insert$ ?agObj StalledCompensationPathVectors 1 ?cpvID))
;------------------------------------------------------------------------------
(defrule RemoveCPVFromService
         (Stage WavefrontSchedule $?)
         (Substage MergeInit $?)
         ?fct <- (Cant schedule ?cpvID for ?blkID ever)
         ?agObj <- (object (is-a PathAggregate) (Parent ?blkID))
         ?cpvObj <- (object (is-a CompensationPathVector) (ID ?cpvID) 
                            (Parent ?i))
         =>
         (retract ?fct)
         (slot-insert$ ?cpvObj Failures 1 ?blkID)
         (slot-insert$ ?agObj ImpossibleCompensationPathVectors 1 ?cpvID))
;------------------------------------------------------------------------------
(defrule PonderMovementIteration
         (declare (salience 100))
         (Stage WavefrontSchedule $?)
         (Substage Ponder $?)
         (object (is-a Wavefront) (ID ?r) (Contents $? ?e $?))
         ?ag <- (object (is-a PathAggregate) (Parent ?e) (ID ?pa)
                        (StalledCompensationPathVectors $?scpv))
         (test (> (length$ $?scpv) 0))
         =>
         (assert (Another Movement Required))
         (modify-instance ?ag (StalledCompensationPathVectors)
                          (TargetCompensationPathVectors $?scpv)))
;------------------------------------------------------------------------------
(defrule AnotherMovementIsRequired
         (Stage WavefrontSchedule $?)
         ?ponder <- (Substage Ponder $?rest)
         ?f <- (Another Movement Required)
         =>
         ;this returns a tuple
         (retract ?ponder ?f)
         (assert (Substage GenerateAnalyze0 
                           GenerateAnalyze 
                           Analyze 
                           SliceAnalyze 
                           MergeInit 
                           Merge 
                           MergeUpdate
                           ReopenBlocks 
                           Ponder 
                           $?rest)))
;------------------------------------------------------------------------------
(defrule FinishSchedulingIntoBlock
         (declare (salience -1))
         (Stage WavefrontSchedule $?)
         (Substage Ponder $?rest)
         =>
         (progn$ (?instance (find-all-instances ((?wave Wavefront)) TRUE))
                 (progn$ (?child (send ?instance get-Contents))
                         (modify-instance 
                           (symbol-to-instance-name ?child)
                           (IsOpen FALSE)))))
;------------------------------------------------------------------------------
; LLVM Schedule Construction rules - these rules interface with LLVM
;------------------------------------------------------------------------------
(defrule ConstructScheduleObjectForBlock-HasPhis
			(declare (salience 10))
			(Stage WavefrontSchedule $?)
			(Substage ScheduleObjectCreation $?)
			?fct <- (Schedule ?e for ?r)
			(object (is-a TerminatorInstruction) (Parent ?e) (ID ?last))
			(object (is-a BasicBlock) (ID ?e) (Parent ?r)
					  (Contents $? ?lastPhi ?firstNonPhi $?instructions ?last $?))
			(object (is-a PhiNode) (ID ?lastPhi))
			(object (is-a Instruction&~PhiNode&~TerminatorInstruction) 
					  (ID ?firstNonPhi))
			=>
			;strange that ?last is being incorporated into $?q
			(retract ?fct)
			(assert (Update style for ?e is ?lastPhi))
			(make-instance of Schedule (Parent ?e) 
								(Contents ?firstNonPhi ?instructions)))
;------------------------------------------------------------------------------
(defrule ConstructScheduleObjectForBlock-DoesntHavePhis
			(declare (salience 10))
			(Stage WavefrontSchedule $?)
			(Substage ScheduleObjectCreation $?)
			?fct <- (Schedule ?e for ?r)
			(object (is-a BasicBlock) (ID ?e) (Parent ?r)
					  (Contents ?firstNonPhi $?instructions ?last $?))
			(object (is-a Instruction&~PhiNode&~TerminatorInstruction) 
					  (ID ?firstNonPhi))
			(object (is-a TerminatorInstruction) (Parent ?e) (ID ?last))
			=>
			(retract ?fct)
			(assert (Update style for ?e is))
			(make-instance of Schedule (Parent ?e) 
								(Contents ?firstNonPhi ?instructions)))
;------------------------------------------------------------------------------
(defrule ConstructScheduleObjectForBlock-TerminatorOnly
			(declare (salience 10))
			(Stage WavefrontSchedule $?)
			(Substage ScheduleObjectCreation $?)
			?fct <- (Schedule ?e for ?r)
			(object (is-a BasicBlock) (ID ?e) (Parent ?r)
					  (Contents ?last))
			(object (is-a TerminatorInstruction) (Parent ?e) (ID ?last))
			=>
			;mark the block as closed
			(retract ?fct))
;------------------------------------------------------------------------------
(defrule ConstructScheduleObjectForBlock-TerminatorAndPhisOnly
			(declare (salience 10))
			(Stage WavefrontSchedule $?)
			(Substage ScheduleObjectCreation $?)
			?fct <- (Schedule ?e for ?r)
			(object (is-a BasicBlock) (ID ?e) (Parent ?r)
					  (Contents $? ?lastPhi ?last $?))
			(object (is-a TerminatorInstruction) (Parent ?e) (ID ?last))
			(object (is-a PhiNode) (ID ?lastPhi))
			=>
			;mark the block as closed
			(retract ?fct))
;------------------------------------------------------------------------------
(defrule Failout-Strange-ScheduleFact
			(declare (salience 10))
			(Stage WavefrontSchedule $?)
			(Substage ScheduleObjectCreation $?)
			?fct <- (Schedule ?e for ?r)
			(object (is-a TaggedObject&~BasicBlock) (ID ?e) (Class ?c))
			(object (is-a TaggedObject&~Region) (ID ?r) (Class ?c2))
			=>
			(printout t "ERROR: Asserted a really wierd schedule fact: " crlf
						 "What should be a block is a " ?c " named " ?e crlf
						 "What should be a region is a " ?c2 " named " ?r crlf)
			(exit))
;------------------------------------------------------------------------------
(defrule PreschedulePhiNodes
			"Adds all phi nodes into the list of scheduled instructions.
			We can always assume they are ready to go too!"
			(Stage WavefrontSchedule $?)
			(Substage ScheduleObjectCreation $?)
			?schedObj <- (object (is-a Schedule) (ID ?n) (Parent ?p) 
				(Scheduled $?s))
			(object (is-a BasicBlock) (ID ?p) (Contents $? ?c $?))
			(object (is-a PhiNode) (ID ?c))
			(test (not (member$ ?c ?s)))
			=>
			(modify-instance ?schedObj (Scheduled $?s ?c)))
;------------------------------------------------------------------------------
(defrule PrescheduleNonLocals
			"Marks all non local instructions as already scheduled. With the way 
			that the dependency analysis goes only instructions that are actually 
			valid will be scheduled first."
			(Stage WavefrontSchedule $?)
			(Substage ScheduleObjectCreation $?)
			?schedObj <- (object (is-a Schedule) (ID ?n) (Parent ?p) 
										(Contents $? ?c $?) (Scheduled $?s))
			?inst <- (object (is-a Instruction) (ID ?c) (Parent ?p)
								  (NonLocalDependencies $? ?d $?))
			(test (not (member$ ?d ?s)))
			=>
			(modify-instance ?schedObj (Scheduled $?s ?d)))
;------------------------------------------------------------------------------
(defrule AssertPerformScheduling
 (declare (salience -1))
 (Stage WavefrontSchedule $?)
 (Substage ScheduleObjectCreation $?)
 (object (is-a Schedule) (ID ?q) (Parent ?b))
 =>
 (assert (Perform Schedule ?q for ?b)))
;------------------------------------------------------------------------------
(defrule PrintoutSchedules
			(declare (salience -10))
			(Stage WavefrontSchedule $?)
			(Substage ScheduleObjectCreation $?)
			(Debug)
			(Schedule)
			?schedule <- (object (is-a Schedule) (ID ?q))
			=>
			(send ?schedule print))
;------------------------------------------------------------------------------
(defrule FAIL-SCHEDULE-FACT-STILL-EXISTS
			(declare (salience -200))
			(Stage WavefrontSchedule $?)
			(Substage ScheduleObjectCreation $?)
			(Schedule ?e for ?r)
			=>
			(printout t "ERROR: (Schedule " ?e " for " ?r ") still exists!" crlf)
			(printout t "EXITING PROGRAM!" crlf)
			(facts)

			(exit))
;------------------------------------------------------------------------------
(defrule CanScheduleInstructionNow
			(declare (salience 344))
			(Stage WavefrontSchedule $?)
			(Substage ScheduleObjectUsage $?)
			(Perform Schedule ?n for ?b)
			?sched <- (object (is-a Schedule) (ID ?n) (Contents ?curr $?rest) 
									(Scheduled $?s) (Success $?succ))
			(object (is-a Instruction) (ID ?curr) 
			 (LocalDependencies $?p&:(subsetp $?p $?s)))
			=>
		 (modify-instance ?sched (Contents $?rest) (Success $?succ ?curr)))
;------------------------------------------------------------------------------
(defrule MustStallInstructionForSchedule
			(declare (salience 343))
			(Stage WavefrontSchedule $?)
			(Substage ScheduleObjectUsage $?)
			(Perform Schedule ?n for ?b)
			?sched <- (object (is-a Schedule) (ID ?n) (Contents ?curr $?rest) 
									(Scheduled $?s) (Failure $?fails))
			(object (is-a Instruction) (ID ?curr) 
			 (LocalDependencies $?p&:(not (subsetp $?p $?s))))
			=>
		 (modify-instance ?sched (Contents $?rest) (Failure $?fails ?curr)))
;------------------------------------------------------------------------------
(defrule EndInstructionScheduleAttempt
			(Stage WavefrontSchedule $?)
			(Substage ResetScheduling $?)
			?fct <- (Perform Schedule ?n for ?b)
			?sched <- (object (is-a Schedule) (ID ?n)
									(Contents))
			=>
			(retract ?fct))
;------------------------------------------------------------------------------
(defrule PutSuccessfulInstructionIntoInstructionStream
			(declare (salience 270))
			(Stage WavefrontSchedule $?)
			(Substage ResetScheduling $?)
			?sched <- (object (is-a Schedule) (ID ?n) (Parent ?p)
									(Success ?targ $?rest) (Scheduled $?s)
									(InstructionStream $?is))
			(object (is-a Instruction) (ID ?targ))
			=>
			(object-pattern-match-delay
			 (modify-instance ?sched (Success $?rest) (Scheduled $?s ?targ)
			  (InstructionStream $?is ?targ))))
;------------------------------------------------------------------------------
(defrule PutSuccessfulStoreInstructionIntoInstructionStream
			(declare (salience 271))
			(Stage WavefrontSchedule $?)
			(Substage ResetScheduling $?)
			?sched <- (object (is-a Schedule) (ID ?n) (Parent ?p)
									(Success ?targ $?rest) (Scheduled $?s)
									(InstructionStream $?stream))
			(object (is-a StoreInstruction) (ID ?targ) (DestinationRegisters ?reg))
			=>
			(object-pattern-match-delay 
			 (modify-instance ?sched (Success $?rest) (Scheduled $?s ?targ ?reg)
			  (InstructionStream $?stream ?targ))))
;------------------------------------------------------------------------------
(defrule FinishedPopulatingInstructionGroup-AssertReset
			(declare (salience 200))
			(Stage WavefrontSchedule $?)
			(Substage ResetScheduling $?)
			(object (is-a Schedule) (ID ?n) (Contents) (Success) 
					  (Failure $?elements))
			(test (> (length$ ?elements) 0))
			=>
			(assert (Reset schedule ?n)))
;------------------------------------------------------------------------------
(defrule FinishedPopulatingInstructionGroup-AssertFinished
			(declare (salience 200))
			(Stage WavefrontSchedule $?)
			(Substage ResetScheduling $?)
			(object (is-a Schedule) (ID ?n)
					  (Parent ?p) (Contents) (Success) (Failure))
			=>
			(assert (Schedule ?p in llvm)))
;------------------------------------------------------------------------------
(defrule ResetTargetScheduleForAnotherGo
			(declare (salience 180))
			(Stage WavefrontSchedule $?)
			(Substage ResetScheduling $?)
			?fct <- (Reset schedule ?n)
			?sched <- (object (is-a Schedule) (ID ?n) (Parent ?p) (Contents) 
									(Failure $?elements))
			=>
			(object-pattern-match-delay
			(retract ?fct)
			(assert (Perform Schedule ?n for ?p)
			        (Reset scheduling process))
			(modify-instance ?sched (Contents ?elements) (Failure))))
;------------------------------------------------------------------------------
(defrule ResetSchedulingProcess
			(declare (salience -10))
			(Stage WavefrontSchedule $?)
			(Substage ResetScheduling $?)
			?f0 <- (Substage ResetScheduling $?rest)
			?f1 <- (Reset scheduling process)
			=>
			(retract ?f0 ?f1)
			(assert (Substage ScheduleObjectUsage ResetScheduling $?rest)))
;------------------------------------------------------------------------------
(defrule FinishLLVMEncoding-HasPhi
			(declare (salience -12))
			(Stage WavefrontSchedule $?)
			(Substage LLVMUpdate $?)
			?f1 <- (Schedule ?p in llvm)
			?f2 <- (Update style for ?p is ?lastPhi)
			(object (is-a Schedule) (Parent ?p) (InstructionStream $?stream))
			?bb <- (object (is-a BasicBlock) (ID ?p) 
								(Contents $?before ?lastPhi $?instructions ?last 
											 $?rest))
			(object (is-a TerminatorInstruction) (ID ?last) (Pointer ?tPtr))
			=>
			(object-pattern-match-delay
			(modify-instance ?bb 
								  (Contents $?before ?lastPhi ?stream ?last $?rest))
			(llvm-schedule-block ?tPtr (symbol-to-pointer-list ?stream))
			(retract ?f1 ?f2)))
;------------------------------------------------------------------------------
(defrule FinishLLVMEncoding-NoPhi
			(declare (salience -12))
			(Stage WavefrontSchedule $?)
			(Substage LLVMUpdate $?)
			?f1 <- (Schedule ?p in llvm)
			?f2 <- (Update style for ?p is)
			?bb <- (object (is-a BasicBlock) (ID ?p))
			(object (is-a Schedule) (Parent ?p) (InstructionStream $?stream))
			(object (is-a TerminatorInstruction) (Parent ?p) (ID ?last) 
					  (Pointer ?tPtr))
			=>
			(object-pattern-match-delay
			(modify-instance ?bb (Contents ?stream ?last))
			(llvm-schedule-block ?tPtr (symbol-to-pointer-list ?stream))
			(retract ?f1 ?f2)))
;------------------------------------------------------------------------------
(defrule RetractUpdateStyleHint
			(declare (salience -26))
			(Stage WavefrontSchedule $?)
			(Substage LLVMUpdate $?)
			?fct <- (Update style for ?t is $?lasers)
			=>
			(retract ?fct))
;------------------------------------------------------------------------------
; Wavefront propagation rules (TODO: refresh self with these rules)
;------------------------------------------------------------------------------
(defrule PropagateAggregateInformation
			"Pulls instruction propagation information from all elements on paths 
			that immediately precede this element on the wavefront and merges it 
			into the path aggregate itself"
			(Stage WavefrontSchedule $?)
			(Substage Identify $?)
			(Propagate aggregates of ?e)
			;if this element is on the wavefront then we can be certain that all 
			;of it's predecessors are above it. That is the definition of being on
			;the wavefront
			?pa <- (object (is-a PathAggregate) (Parent ?e) (ID ?pp))
			(object (is-a Diplomat) (ID ?e) (PreviousPathElements $? ?z $?))
			(object (is-a PathAggregate) (Parent ?z) 
					  (InstructionPropagation $? ?targ ?alias ? ! $?))
			=>
			;replace parent blocks of previous path elements with the name of the
			;element this was acquired from
			;(printout t "Put (" ?targ " " ?alias " " ?z "! ) into " ?pp crlf)
			(slot-insert$ ?pa InstructionPropagation 1 ?targ ?alias ?z !))
;------------------------------------------------------------------------------
(defrule RetractAggregationInformation
			(declare (salience -50))
			(Stage WavefrontSchedule $?)
			(Substage Identify $?)
			?fct <- (Propagate aggregates of ?)
			=>
			(retract ?fct))
;------------------------------------------------------------------------------
(defrule AssertPhiNodePropagationPredicateIsBlock
			(declare (salience 1))
			(Stage WavefrontSchedule $?)
			(Substage PhiIdentify $?)
			(object (is-a Wavefront) (Parent ?r) (Contents $? ?e $?))
			?pa <- (object (is-a PathAggregate) (Parent ?e) 
								(InstructionPropagation ?targ ?alias ?pred ! $?rest))
			=>
			(modify-instance ?pa (InstructionPropagation $?rest))
			(assert (Propagation target ?targ with alias ?alias
										from block ?pred for block ?e)))
;------------------------------------------------------------------------------
(defrule RemoveDuplicateElements 
			(Stage WavefrontSchedule $?)
			(Substage PhiNode $?)
			?f0 <- (Propagation target ?t with alias ?a from block ?p0 
									  for block ?b)
			?f1 <- (Propagation target ?t with alias ?a from block ?p1 
									  for block ?b)
			(test (and (neq ?f0 ?f1) (neq ?p0 ?p1)))
			?pa <- (object (is-a PathAggregate) (Parent ?b))
			=>
			(retract ?f0 ?f1)
			(slot-insert$ ?pa InstructionPropagation 1 ?t ?a ?b !))
;------------------------------------------------------------------------------
(defrule MergePhiNodePropagationWithOtherPropagation
			(Stage WavefrontSchedule $?)
			(Substage PhiNode $?)
			?f0 <- (Propagation target ?t with alias ?a0 from block ?p0 
									  for block ?b)
			?f1 <- (Propagation target ?t with alias ?a1 from block ?p1 
									  for block ?b)
			(test (neq ?f0 ?f1))
			=>
			(retract ?f0 ?f1)
			(assert (Create phinode targeting instruction ?t for block ?b 
								 consisting of ?a0 ?p0 ?a1 ?p1 )))
;------------------------------------------------------------------------------
(defrule MergePhiNodePropagationWithCreateStatement
			(Stage WavefrontSchedule $?)
			(Substage PhiNode $?)
			?f0 <- (Propagation target ?t with alias ?a0 from block ?p0 
									  for block ?b)
			?f1 <- (Create phinode targeting instruction ?t for block ?b 
								consisting of $?targets)
			=>
			(retract ?f0 ?f1)
			(assert (Create phinode targeting instruction ?t for block ?b 
								 consisting of $?targets ?a0 ?p0 )))
;------------------------------------------------------------------------------
(defrule PutUnfulfilledItemsBackIntoPropagationList
			(declare (salience -10))
			(Stage WavefrontSchedule $?)
			(Substage PhiNode $?)
			?f0 <- (Propagation target ?t with alias ?a0 from block ?p0 for 
									  block ?b)
			?pa <- (object (is-a PathAggregate) (Parent ?b))
			=>
			(retract ?f0)
			(slot-insert$ ?pa InstructionPropagation 1 ?t ?a0 ?b !))
;------------------------------------------------------------------------------
(defrule NamePhiNodeFromCreateStatement-NotOriginalBlock
			(declare (salience -12))
			(Stage WavefrontSchedule $?)
			(Substage PhiNode $?)
			?fct <- (Create phinode targeting instruction ?t for block ?b
								 consisting of $?elements)
			?agObj <- (object (is-a PathAggregate) 
									(Parent ?b))
			?bb <- (object (is-a BasicBlock) 
								(ID ?b) 
								(Contents ?first $?rest)
								(UnlinkedInstructions $?ui))
			(test (not (member$ ?t $?ui)))
			(object (is-a Instruction) 
					  (ID ?first) 
					  (Pointer ?bPtr))
			(object (is-a Instruction) 
					  (ID ?t) 
					  (Type ?ty))
			(object (is-a LLVMType) 
					  (ID ?ty) 
					  (Pointer ?dataType))
			=>
			(retract ?fct)
			(bind ?name (sym-cat phi. (gensym*) . ?t))
			(bind ?count (/ (length$ $?elements) 2))
			(bind ?pointers (symbol-to-pointer-list ?elements))
			(make-instance ?name of PhiNode 
								(Parent ?b)
								(TimeIndex 0)
								(Pointer (llvm-make-phi-node ?name ?dataType ?count 
																	  ?bPtr ?pointers))
								(IncomingValueCount ?count)
								(Operands $?elements))
			;we've scheduled the given original instruction into this block
			; although it's just a ruse
			(slot-insert$ ?agObj ScheduledInstructions 1 ?t)
			(slot-insert$ ?agObj InstructionPropagation 1 ?t ?name ?b !)
			(slot-insert$ ?agObj ReplacementActions 1 ?t ?name !)
			(slot-insert$ ?bb Contents 1 ?name)
			(assert (Update duration for block ?b)))
;------------------------------------------------------------------------------
(defrule NamePhiNodeFromCreateStatement-OriginalBlock
			(declare (salience -12))
			(Stage WavefrontSchedule $?)
			(Substage PhiNode $?)
			?fct <- (Create phinode targeting instruction ?t for block ?b
								 consisting of $?elements)
			?agObj <- (object (is-a PathAggregate) 
									(Parent ?b))
			?bb <- (object (is-a BasicBlock) 
								(ID ?b) 
								(Contents ?first $?rest) 
								(UnlinkedInstructions $?ui))
			(test (not (member$ ?t ?ui)))
			(object (is-a Instruction) 
					  (ID ?first) 
					  (Pointer ?bPtr))
			?tObj <- (object (is-a Instruction) 
								  (ID ?t) 
								  (Type ?ty) 
								  (Pointer ?tPtr))
			(object (is-a LLVMType) 
					  (ID ?ty) 
					  (Pointer ?dataType))
			=>
			(retract ?fct)
			(bind ?name (sym-cat phi. (gensym*) . ?t))
			(bind ?count (/ (length$ $?elements) 2))
			(bind ?pointers (symbol-to-pointer-list ?elements))
			(bind ?phiPointer 
					(llvm-make-phi-node ?name ?dataType ?count ?bPtr ?pointers))
			(bind ?phiObj (make-instance ?name of PhiNode 
												  (Parent ?b)
												  (TimeIndex 0)
												  (Pointer ?phiPointer)
												  (IncomingValueCount ?count)
												  (Operands $?elements)))
			(llvm-replace-all-uses ?tPtr ?phiPointer)
			(llvm-unlink-and-delete-instruction ?tPtr)
			(unmake-instance ?tObj)
			(slot-insert$ ?agObj ScheduledInstructions 1 ?t)
			(slot-insert$ ?bb Contents 1 ?name)
			(assert (Update duration for block ?b)))
;------------------------------------------------------------------------------
(defrule ReindexBasicBlock 
			(Stage WavefrontSchedule $?)
			(Substage PhiNodeUpdate $?)
			?fct <- (Update duration for block ?b)
			(object (is-a BasicBlock) (ID ?b) (Contents $?c))
			=>
			;this is very much procedural but I frankly don't care
			;anymore. 
			(bind ?index 0)
			(progn$ (?t ?c)
					  (bind ?obj (instance-address (symbol-to-instance-name ?t)))
					  (modify-instance ?obj (TimeIndex ?index))
					  (bind ?index (+ ?index 1)))
			(retract ?fct))
;------------------------------------------------------------------------------
; Rules associated with advancing the wavefront
;------------------------------------------------------------------------------
(defrule MoveContentsToDeleteNodes
			"Moves blocks out of the contents into the closed list"
			(declare (salience 2701))
			(Stage WavefrontSchedule $?)
			(Substage AdvanceInit $?)
			?wave <- (object (is-a Wavefront) (ID ?z) (Parent ?r) 
								  (Contents $?c) (Closed $?cl))
			(test (or (> (length$ ?c) 0) (> (length$ ?cl) 0)))
			=>
			(slot-insert$ ?wave DeleteNodes 1 ?c ?cl))
;------------------------------------------------------------------------------
(defrule MarkShouldStayOnWavefront
			(declare (salience 343))
			(Stage WavefrontSchedule $?)
			(Substage AdvanceIdentify $?)
			?wave <- (object (is-a Wavefront) (ID ?q) (Parent ?r) 
								  (DeleteNodes $?a ?b $?c))
			?bb <- (object (is-a Diplomat) (ID ?b) (NextPathElements ?s))
			(object (is-a Diplomat) (ID ?s) (PreviousPathElements $?ppe))
			(test (not (subsetp ?ppe (send ?wave get-DeleteNodes)))) 
			?agObj <- (object (is-a PathAggregate) (Parent ?b))
			=>
      (object-pattern-match-delay
			(if (not (member$ ?b (send ?wave get-Closed))) then
			  (bind ?ind (member$ ?b (send ?wave get-Contents)))
			  (slot-delete$ ?wave Contents ?ind ?ind)
			  (slot-insert$ ?wave Closed 1 ?b))
			(modify-instance ?wave (DeleteNodes $?a $?c))))
;------------------------------------------------------------------------------
(defrule DeleteElementFromWavefront
			(declare (salience 180))
			(Stage WavefrontSchedule $?)
			(Substage Advance $?)
			?wave <- (object (is-a Wavefront) (ID ?id) (Parent ?r) 
								  (DeleteNodes ?a $?))
			(object (is-a Diplomat) (ID ?a) (NextPathElements $?npe))
			=>
      (object-pattern-match-delay
			(bind ?ind (member$ ?a (send ?wave get-Contents)))
			(bind ?ind2 (member$ ?a (send ?wave get-Closed)))
			(slot-delete$ ?wave DeleteNodes 1 1)
			(if ?ind then (slot-delete$ ?wave Contents ?ind ?ind))
			(if ?ind2 then (slot-delete$ ?wave Closed ?ind2 ?ind2))
			(assert (Add into ?id blocks $?npe))))
;------------------------------------------------------------------------------
(defrule PutSuccessorsOntoWavefront-Match
			(declare (salience 100))
			(Stage WavefrontSchedule $?)
			(Substage AdvanceEnd $?)
			?fct <- (Add into ?id blocks ?next $?rest)
			?wave <- (object (is-a Wavefront) (ID ?id))
			=>
			(retract ?fct)
			;I know that this is procedural but I really want to get this done
			(assert (Add into ?id blocks $?rest))
			(if (not (member$ ?next (send ?wave get-Contents))) then
			  (slot-insert$ ?wave Contents 1 ?next)))
;------------------------------------------------------------------------------
(defrule PutSuccessorsOntoWavefront-NoMoreElements
			(declare (salience 100))
			(Stage WavefrontSchedule $?)
			(Substage AdvanceEnd $?)
			?fct <- (Add into ? blocks)
			=>
			(retract ?fct))
;------------------------------------------------------------------------------
(defrule PonderRestartOfWavefrontScheduling
			(declare (salience -512))
			(Stage WavefrontSchedule $?)
			?fct <- (Substage Update $?)
			=>
			(bind ?instances (find-all-instances ((?wave Wavefront)) 
															 (> (length$ ?wave:Contents) 0)))
			(if (> (length$ ?instances) 0) then
			  (retract ?fct)
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
									  ;ScheduleObjectCreation 
									  ;ScheduleObjectUsage 
									  ;ResetScheduling 
									  ;InitLLVMUpdate
									  ;LLVMUpdate 
									  AdvanceInit 
									  AdvanceIdentify
									  Advance
									  AdvanceEnd
									  Update))))
;------------------------------------------------------------------------------
(defrule RetractUnlinkedInstructions
			(Stage WavefrontFinal $?)
			?bb <- (object (is-a BasicBlock) (ID ?b) 
								(UnlinkedInstructions ?i $?rest))
			?instruction <- (object (is-a Instruction) (ID ?i) (Parent ?b) 
											(Pointer ?ptr))
			(object (is-a PathAggregate) (Parent ?b) 
					  (InstructionPropagation $? ?i ?new ?b ! $?))
			(object (is-a Instruction) (ID ?new) (Pointer ?nPtr))
			=>
			;this is a little gross but it is a very easy way to ensure that
			;things work correctly
      (object-pattern-match-delay
			(llvm-replace-all-uses ?ptr ?nPtr)
			(modify-instance ?bb (UnlinkedInstructions $?rest))
			(llvm-unlink-and-delete-instruction ?ptr)
			(unmake-instance ?instruction)))
;------------------------------------------------------------------------------
; Update the dependencies on the wavefront
;
;
; This stage is the actual act of scheduling the blocks on the wavefront. 
; The first step is to reacquire all dependencies of the given blocks by
; running the same rules as before. The only difference is that we have to do
; it specially for the blocks on the wavefront. 
; 
; I'm thinking of just copying the rules from the analysis pass to here. It
; would be a duplication but I frankly don't care anymore. 
;------------------------------------------------------------------------------
(defrule CreateDependencyAnalysisTargets
			(declare (salience 10))
			(Stage WavefrontSchedule $?)
			(Substage DependencyAnalysis $?)
			(object (is-a Wavefront) (Parent ?r) (Contents $? ?e $?))
			(object (is-a BasicBlock) (ID ?e))
			(object (is-a PathAggregate) (Parent ?e) (OriginalStopIndex ?si))
			=>
			;only look at instructions starting at the original stop index. This
			;prevents unncessary recomputation
			(assert (Evaluate ?e for dependencies starting at ?si)))
;------------------------------------------------------------------------------
(defrule IdentifyWAR-Wavefront
			"Identifies a WAR dependency between two instructions. It will not 
			match if it turns out the values are constant integers or constant 
			floating point values"
			(Stage WavefrontSchedule $?)
			(Substage DependencyAnalysis $?)
			(Evaluate ?p for dependencies starting at ?si)
			?i0 <- (object (is-a Instruction) (Parent ?p) (ID ?t0)
								(Operands $? ?c $?) (TimeIndex ?ti0))
			(object (is-a TaggedObject&~ConstantInteger&~ConstantFloatingPoint) 
					  (ID ?c))
			?i1 <- (object (is-a Instruction) (Parent ?p) (ID ?t1)
								(TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?ti0 ?ti1)))
								(DestinationRegisters $? ?c $?))
			=>
			(assert (Instruction ?t1 consumes ?t0)
					  (Instruction ?t0 produces ?t1)))
;------------------------------------------------------------------------------
(defrule IdentifyRAW-Wavefront
			"Identifies a RAW dependency between two instructions in the same 
			block. It will not match if it turns out that the values are constant 
			integers or constant floating point values."
			(Stage WavefrontSchedule $?)
			(Substage DependencyAnalysis $?)
			(Evaluate ?p for dependencies starting at ?si)
			(object (is-a Instruction) (Parent ?p) (ID ?t0)
					  (DestinationRegisters $? ?c $?) (TimeIndex ?ti0))
			(object (is-a TaggedObject&~ConstantInteger&~ConstantFloatingPoint) 
					  (ID ?c))
			(object (is-a Instruction) (Parent ?p) (ID ?t1)
					  (Operands $? ?c $?) 
					  (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?ti0 ?ti1))))
			=>
			(assert (Instruction ?t1 consumes ?t0)
					  (Instruction ?t0 produces ?t1)))
;------------------------------------------------------------------------------
(defrule IdentifyWAW-Wavefront
			"Identifies a WAW dependency between two instructions in the same 
			block. It will not match if it turns out that the values are constant 
			integers or constant floating point values."
			(Stage WavefrontSchedule $?)
			(Substage DependencyAnalysis $?)
			(Evaluate ?p for dependencies starting at ?si)
			?i0 <- (object (is-a Instruction) (Parent ?p) (ID ?t0)
								(DestinationRegisters $? ?c $?) (TimeIndex ?ti0))
			(object (is-a TaggedObject&~ConstantInteger&~ConstantFloatingPoint) 
					  (ID ?c))
			?i1 <- (object (is-a Instruction) (Parent ?p) (ID ?t1) 
								(TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?ti0 ?ti1))) 
								(DestinationRegisters $? ?c $?))
			=>
			(assert (Instruction ?t1 consumes ?t0)
					  (Instruction ?t0 produces ?t1)))
;------------------------------------------------------------------------------
;these call instruction checks only work for new instructions or those that
; dont have a call dependency. As that was the only way they got into the 
; block in the first place
;------------------------------------------------------------------------------
(defrule MarkCallInstructionDependency-ModifiesMemory-Wavefront
			"Creates a series of dependencies for all instructions following a 
			call instruction if it turns out that the call could modify memory."
			(Stage WavefrontSchedule $?)
			(Substage DependencyAnalysis $?)
			(Evaluate ?p for dependencies starting at ?si)
			(object (is-a CallInstruction) (ID ?name) (Parent ?p) 
					  (DoesNotAccessMemory FALSE) (OnlyReadsMemory FALSE) 
					  (MayWriteToMemory TRUE)
					  (TimeIndex ?t0))
			(object (is-a Instruction) (Parent ?p) 
					  (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?t0 ?ti1)))
					  (HasCallDependency FALSE) (ID ?following))
			=>
			(assert (Instruction ?following has a CallDependency)
					  (Instruction ?following consumes ?name)
					  (Instruction ?name produces ?following)))
;------------------------------------------------------------------------------
(defrule MarkCallInstructionDependency-InlineAsm-Wavefront
			"Creates a series of dependencies for all instructions following a 
			call instruction if it turns out that the call is inline asm."
			(Stage WavefrontSchedule $?)
			(Substage DependencyAnalysis $?)
			(Evaluate ?p for dependencies starting at ?si)
			(object (is-a CallInstruction) (ID ?name) (Parent ?p) 
					  (IsInlineAsm TRUE)
					  (TimeIndex ?t0))
			(object (is-a Instruction) (Parent ?p) 
					  (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?t0 ?ti1)))
					  (HasCallDependency FALSE) (ID ?following))
			=>
			(assert (Instruction ?following has a CallDependency)
					  (Instruction ?following consumes ?name)
					  (Instruction ?name produces ?following)))
;------------------------------------------------------------------------------
(defrule MarkCallInstructionDependency-SideEffects-Wavefront
			"Creates a series of dependencies for all instructions following a 
			call instruction if it turns out that the call is inline asm."
			(Stage WavefrontSchedule $?)
			(Substage DependencyAnalysis $?)
			(Evaluate ?p for dependencies starting at ?si)
			(object (is-a CallInstruction) (ID ?name) (Parent ?p) 
					  (MayHaveSideEffects TRUE) (MayWriteToMemory TRUE) 
					  (TimeIndex ?t0))
			(object (is-a Instruction) (Parent ?p) 
					  (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?t0 ?ti1)))
					  (HasCallDependency FALSE) (ID ?following))
			=>
			(assert (Instruction ?following has a CallDependency)
					  (Instruction ?following consumes ?name)
					  (Instruction ?name produces ?following)))
;------------------------------------------------------------------------------
(defrule MarkNonLocalDependencies-Wavefront
			(Stage WavefrontSchedule $?)
			(Substage DependencyAnalysis $?)
			(Evaluate ?p for dependencies starting at ?si)
			?inst <- (object (is-a Instruction) (Parent ?p) 
								  (TimeIndex ?t&:(>= ?t ?si))
								  (Operands $? ?o $?))
			(object (is-a Instruction) (ID ?o) (Parent ~?p))
			=>
			(slot-insert$ ?inst NonLocalDependencies 1 ?o))
;------------------------------------------------------------------------------
(defrule Wavefront-MarkHasCallDependency
			(declare (salience -2))
			(Stage WavefrontSchedule $?)
			(Substage DependencyAnalysis $?)
			?fct <- (Instruction ?f has a CallDependency)
			?obj <- (object (is-a Instruction) (ID ?f))
			=>
			(modify-instance ?obj (HasCallDependency TRUE))
			(retract ?fct))
;------------------------------------------------------------------------------
(defrule InjectConsumers-Wavefront
			"Adds a given consumer to the target instruction"
			(declare (salience -5))
			(Stage WavefrontSchedule $?)
			(Substage DependencyAnalysis $?)
			?fct <- (Instruction ?target consumes ?id)
			?inst <- (object (is-a Instruction) (ID ?id))
			=>
			(retract ?fct)
			(if (not (member$ ?target (send ?inst get-Consumers))) then
			  (slot-insert$ ?inst Consumers 1 ?target)))
;------------------------------------------------------------------------------
(defrule InjectProducers-Wavefront
			"Adds a given producer to the target instruction"
			(declare (salience -5))
			(Stage WavefrontSchedule $?)
			(Substage DependencyAnalysis $?)
			?fct <- (Instruction ?target produces ?id)
			?inst <- (object (is-a Instruction) (ID ?id))
			=>
			(retract ?fct)
			(if (not (member$ ?target (send ?inst get-LocalDependencies))) then
			  (slot-insert$ ?inst LocalDependencies 1 ?target))
			(if (not (member$ ?target (send ?inst get-Producers))) then 
			  (slot-insert$ ?inst Producers 1 ?target)))
;------------------------------------------------------------------------------
(defrule StoreToLoadDependency-Wavefront
			(Stage WavefrontSchedule $?)
			(Substage DependencyAnalysis $?)
			(Evaluate ?p for dependencies starting at ?si)
			(object (is-a StoreInstruction) (Parent ?p) (ID ?t0)
					  (TimeIndex ?ti0) (MemoryTarget ?sym0))
			(object (is-a LoadInstruction) (Parent ?p) (ID ?t1) 
					  (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?ti0 ?ti1)))
					  (MemoryTarget ?sym1))
      (test (or-eq ?sym0 ?sym1 UNKNOWN))
			;(test (or (eq ?sym0 ?sym1) (eq ?sym0 UNKNOWN)))
			=>
			(assert (Instruction ?t1 consumes ?t0)
					  (Instruction ?t0 produces ?t1)))
;------------------------------------------------------------------------------
(defrule StoreToStoreDependency-Wavefront
			(Stage WavefrontSchedule $?)
			(Substage DependencyAnalysis $?)
			(Evaluate ?p for dependencies starting at ?si)
			(object (is-a StoreInstruction) (Parent ?p) (ID ?t0)
					  (TimeIndex ?ti0) (MemoryTarget ?sym0))
			(object (is-a StoreInstruction) (Parent ?p) (ID ?t1) 
					  (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?ti0 ?ti1)))
					  (MemoryTarget ?sym1))
      (test (or-eq ?sym0 ?sym1 UNKNOWN))
			;(test (or (eq ?sym0 ?sym1) (eq ?sym0 UNKNOWN)))
			=>
			(assert (Instruction ?t1 consumes ?t0)
					  (Instruction ?t0 produces ?t1)))
;------------------------------------------------------------------------------
(defrule LoadToStoreDependency-Wavefront
			(Stage WavefrontSchedule $?)
			(Substage DependencyAnalysis $?)
			(Evaluate ?p for dependencies starting at ?si)
			(object (is-a LoadInstruction) (Parent ?p) (ID ?t0)
					  (TimeIndex ?ti0) (MemoryTarget ?sym0)) 
			(object (is-a StoreInstruction) (Parent ?p) (ID ?t1) 
					  (TimeIndex ?ti1&:(and (>= ?ti1 ?si) (< ?ti0 ?ti1)))
					  (MemoryTarget ?sym1))
      (test (or-eq ?sym0 ?sym1 UNKNOWN))
			;(test (or (eq ?sym0 ?sym1) (eq ?sym0 UNKNOWN)))
			=>
			(assert (Instruction ?t1 consumes ?t0)
					  (Instruction ?t0 produces ?t1)))
;------------------------------------------------------------------------------
(defrule FinishedDependencyAnalysis 
			(declare (salience -800))
			(Stage WavefrontSchedule $?)
			(Substage DependencyAnalysis $?)
			?fct <- (Evaluate ?p for dependencies starting at ?v)
			(object (is-a BasicBlock) (ID ?p) (Parent ?r))
			=>
			(assert (Schedule ?p for ?r))
			(retract ?fct))
;------------------------------------------------------------------------------
(defrule RemoveInstructionsFromProducers
			(declare (salience 768))
			(Stage WavefrontSchedule $?)
			(Substage MergeUpdate $?)
			?fct <- (Remove evidence of ?tInst from instructions ?inst $?insts)
			?iObj <- (object (is-a Instruction) 
								  (ID ?inst) 
								  (Producers $?pb ?tInst $?pa)
								  (LocalDependencies $?ldb ?tInst $?lda))
			=>
			(retract ?fct)
			(assert (Remove evidence of ?tInst from instructions $?insts))
			(modify-instance ?iObj (Producers $?pb $?pa)
								  (LocalDependencies $?ldb $?lda))
			(slot-insert$ ?iObj NonLocalDependencies 1 ?tInst))
;------------------------------------------------------------------------------
(defrule RetractRemoveInstructionsFromProducers
			(declare (salience 768))
			(Stage WavefrontSchedule $?)
			(Substage MergeUpdate $?)
			?fct <- (Remove evidence of ? from instructions)
			=>
			(retract ?fct))
;------------------------------------------------------------------------------
(defrule StartRecomputeBlock
			(declare (salience 100))
			(Stage WavefrontSchedule $?)
			(Substage MergeUpdate $?)
			?fct <- (Recompute block ?b)
			?bb <- (object (is-a BasicBlock) (ID ?b) 
								(Contents $?instructions ?last))
			(object (is-a TerminatorInstruction) (ID ?last))
			=>
			(modify-instance ?bb (ReadsFrom) (WritesTo) (HasMemoryBarrier FALSE))
			(retract ?fct)
			(assert (Recompute block ?b with instructions $?instructions)))
;------------------------------------------------------------------------------
(defrule RecomputeNonMemoryInstructionForBlock
			(declare (salience 99))
			(Stage WavefrontSchedule $?)
			(Substage MergeUpdate $?)
			?fct <- (Recompute block ?b with instructions ?inst $?rest)
			(object (is-a BasicBlock) (ID ?b))
			(object (is-a Instruction&~LoadInstruction&~StoreInstruction) 
					  (ID ?inst) (Parent ?b))
			=>
			(retract ?fct)
			(assert (Recompute block ?b with instructions $?rest)))
;------------------------------------------------------------------------------
(defrule RecomputeLoadInstructionForBlock
			(declare (salience 99))
			(Stage WavefrontSchedule $?)
			(Substage MergeUpdate $?)
			?fct <- (Recompute block ?b with instructions ?inst $?rest)
			(object (is-a LoadInstruction) (ID ?inst) (Parent ?b) 
					  (MemoryTarget ?mt)) 
			?bb <- (object (is-a BasicBlock) (ID ?b))
			=>
			(if (not (member$ ?mt (send ?bb get-ReadsFrom))) then
			  (slot-insert$ ?bb ReadsFrom 1 ?mt))
			(retract ?fct)
			(assert (Recompute block ?b with instructions $?rest)))
;------------------------------------------------------------------------------
(defrule RecomputeStoreInstructionForBlock
			(declare (salience 99))
			(Stage WavefrontSchedule $?)
			(Substage MergeUpdate $?)
			?fct <- (Recompute block ?b with instructions ?inst $?rest)
			(object (is-a StoreInstruction) (ID ?inst) (Parent ?b) 
					  (MemoryTarget ?mt))
			?bb <- (object (is-a BasicBlock) (ID ?b))
			=>
			(if (not (member$ ?mt (send ?bb get-WritesTo))) then
			  (slot-insert$ ?bb WritesTo 1 ?mt))
			(retract ?fct)
			(assert (Recompute block ?b with instructions $?rest)))
;------------------------------------------------------------------------------
(defrule FinishRecomputationForBlock
			(declare (salience 98))
			(Stage WavefrontSchedule $?)
			(Substage MergeUpdate $?)
			?fct <- (Recompute block ?b with instructions)
			?bb <- (object (is-a BasicBlock) (ID ?b) (ReadsFrom $?rf)
								(WritesTo $?wt))
			=>
			(retract ?fct)
			(if (or (member$ UNKNOWN ?rf)
					  (member$ UNKNOWN ?wt)) then
			  (modify-instance ?bb (HasMemoryBarrier TRUE))))
;------------------------------------------------------------------------------
; Now we need to rename operands as need be within the blocks that these
; instructions have been scheduled into
;------------------------------------------------------------------------------
(defrule AssertReplacementActions
			"Iterates through the replacement actions multifield and asserts facts 
			related to the replacement of given values with another value"
			(declare (salience 100))
			(Stage WavefrontSchedule $?)
			(Substage Rename $?)
			(object (is-a PathAggregate) (Parent ?e) 
					  (ReplacementActions $? ?orig ?new ! $?))
			=>
			; I have turned you into a cheese sandwich, what do you say to that?
			(assert (Replace uses of ?orig with ?new for block ?e)))
;------------------------------------------------------------------------------
(defrule ReplaceUses
			(declare (salience 20))
			(Stage WavefrontSchedule $?)
			(Substage Rename $?)
			?fct <- (Replace uses of ?orig with ?new for block ?e)
			(object (is-a Instruction) (ID ?orig) (Pointer ?oPtr))
			(object (is-a Instruction) (ID ?new) (Pointer ?nPtr))
			(object (is-a BasicBlock) (ID ?e) (Contents $? ?new $?rest))
			=>
			(retract ?fct)
			(bind ?ptrList (create$))
			(bind ?symList (create$))
      (bind ?i0 1)
			(progn$ (?var $?rest)
					  (bind ?obj (symbol-to-instance-name ?var))
            (if (member$ ?orig (send ?obj get-Operands)) then
             (bind ?ptrList (insert$ ?ptrList ?i0 (send ?obj get-Pointer)))
             (bind ?symList (insert$ ?symList ?i0 ?var))
            (bind ?i0 (+ ?i0 1))))
      (assert ({ clips ! ?orig => ?new for ?symList })
              ({ llvm ! ?oPtr => ?nPtr for ?ptrList })))
;------------------------------------------------------------------------------
(defrule ReplaceUsesInLLVM
			(declare (salience -1))
			(Stage WavefrontSchedule $?)
			(Substage Rename $?)
      ?fct <- ({ llvm ! ?from => ?to for $?p2 })
			=>
			(if (llvm-replace-uses ?from ?to ?p2) then 
			  (retract ?fct) 
			  else
			  (printout t
							"Some kind of error occured when trying to replace uses. " 
							crlf "Make sure that you've done arguments correctly. " 
							crlf "The failing rule is ReplaceUsesInLLVM." crlf
							"?from = " ?from crlf
							"?to = " ?to crlf
							"?p2 = " ?p2 crlf
							"Now I'm exiting" crlf)
			  (exit)))
;------------------------------------------------------------------------------
(defrule ReplaceUsesInCLIPS
			(declare (salience -1))
			(Stage WavefrontSchedule $?)
			(Substage Rename $?)
      ?fct <- ({ clips ! ?from => ?to for ?symbol $?rest })
			?inst <- (object (is-a Instruction) (ID ?symbol) 
								  (Operands $?operands) (LocalDependencies $?locDep)
								  (NonLocalDependencies $?nLocDep))
			=>
			(modify-instance ?inst (Operands) (LocalDependencies) 
			 (NonLocalDependencies))
			(retract ?fct)
      (assert ({ clips ! ?from => ?to for $?rest })
              ({ clips ! ?from => ?to replacement ?symbol 
               operands $?operands })
				  ({ env: clips translation: ?from => ?to action: replacement
					  in: ?symbol type: local-dependencies
					  contents: $?locDep })
				  ({ env: clips translation: ?from => ?to action: replacement
						in: ?symbol type: non-local-dependencies
						contents: $?nLocDep })))
;------------------------------------------------------------------------------
(defrule ReplaceUsesInCLIPS-End
			(declare (salience -1))
			(Stage WavefrontSchedule $?)
			(Substage Rename $?)
      ?fct <- ({ clips ! ?from => ?to for })
			=>
			(retract ?fct))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualLocalDependencyEntries-NoMatch
 (declare (salience -2))
  (Stage WavefrontSchedule $?)
  (Substage Rename $?)
  ?fct <- ({
	  	env: clips
		translation: ?from => ?to 
		action: replacement
		in: ?symbol 
		type: local-dependencies
		contents: ?curr&~?from $?rest
	  })
  ?inst <- (object (is-a Instruction) (ID ?symbol))
  =>
  (object-pattern-match-delay
  (slot-insert$ ?inst LocalDependencies 1 ?curr)
  (retract ?fct)
  (assert ({ env: clips translation: ?from => ?to action: replacement in:
			  ?symbol type: local-dependencies contents: $?rest }))))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualLocalDependencyEntries-Match
 (declare (salience -2))
  (Stage WavefrontSchedule $?)
  (Substage Rename $?)
  ?fct <- ({
	  	env: clips
		translation: ?from => ?to 
		action: replacement
		in: ?symbol 
		type: local-dependencies
		contents: ?from $?rest
	  })
  ?inst <- (object (is-a Instruction) (ID ?symbol))
  =>
  (object-pattern-match-delay
  (slot-insert$ ?inst LocalDependencies 1 ?to)
  (retract ?fct)
  (assert ({ env: clips translation: ?from => ?to action: replacement in:
			  ?symbol type: local-dependencies contents: $?rest }))))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualNonLocalDependencyEntries-NoMatch
 (declare (salience -2))
  (Stage WavefrontSchedule $?)
  (Substage Rename $?)
  ?fct <- ({
	  	env: clips
		translation: ?from => ?to 
		action: replacement
		in: ?symbol 
		type: non-local-dependencies
		contents: ?curr&~?from $?rest
	  })
  ?inst <- (object (is-a Instruction) (ID ?symbol))
  =>
  (object-pattern-match-delay
  (slot-insert$ ?inst NonLocalDependencies 1 ?curr)
  (retract ?fct)
  (assert ({ env: clips translation: ?from => ?to action: replacement in:
			  ?symbol type: local-dependencies contents: $?rest }))))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualNonLocalDependencyEntries-Match
 (declare (salience -2))
  (Stage WavefrontSchedule $?)
  (Substage Rename $?)
  ?fct <- ({
	  	env: clips
		translation: ?from => ?to 
		action: replacement
		in: ?symbol 
		type: non-local-dependencies
		contents: ?from $?rest
	  })
  ?inst <- (object (is-a Instruction) (ID ?symbol))
  =>
  (object-pattern-match-delay
  (slot-insert$ ?inst NonLocalDependencies 1 ?to)
  (retract ?fct)
  (assert ({ env: clips translation: ?from => ?to action: replacement in:
			  ?symbol type: non-local-dependencies contents: $?rest }))))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualInstructionUses-NoMatch
			(declare (salience -2))
			(Stage WavefrontSchedule $?)
			(Substage Rename $?)
      ?fct <- ({ clips ! ?f => ?t replacement ?s operands ?op&~?f $?ops })
			?inst <- (object (is-a Instruction) (ID ?s))
			=>
			(slot-insert$ ?inst Operands 1 ?op)
			(retract ?fct)
      (assert ({ clips ! ?f => ?t replacement ?s operands $?ops })))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualInstructionUses-Match
			(declare (salience -2))
			(Stage WavefrontSchedule $?)
			(Substage Rename $?)
      ?fct <- ({ clips ! ?f => ?t replacement ?s operands ?f $?ops })
			?inst <- (object (is-a Instruction) (ID ?s))
			=>
			(slot-insert$ ?inst Operands 1 ?t)
			(retract ?fct)
      (assert ({ clips ! ?f => ?t replacement ?s operands $?ops })))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualInstructionUses-Empty
			(declare (salience -2))
			(Stage WavefrontSchedule $?)
			(Substage Rename $?)
      ?fct <- ({ clips ! ?f => ?t replacement ?s operands })
			=>
			(retract ?fct))
;------------------------------------------------------------------------------
; Rules associated with the act of actually scheduling instructions
; into blocks on the wavefront
;------------------------------------------------------------------------------
(defrule AssertScheduleCPVIntoTargetBlock 
			(Stage WavefrontSchedule $?)
			(Substage Merge $?)
			(object (is-a Wavefront) (Parent ?r) (Contents $? ?e $?))
			(object (is-a Diplomat) (ID ?e) (IsOpen TRUE))
			?agObj <- (object (is-a PathAggregate) (Parent ?e) 
									(MovableCompensationPathVectors $?cpvs)) 
			=>
			(if (> (length$ $?cpvs) 0) then
			  (modify-instance ?agObj (MovableCompensationPathVectors)))
			(progn$ (?cpv $?cpvs)
					  (assert (Determine schedule style for ?cpv into block ?e))))
;------------------------------------------------------------------------------
(defrule ScheduleStyleForCPVIsMove
			"This rule attempts to determine if the CPV should be moved into the 
			given block on the wavefront. If this is true then the fact to perform 
			this action will be asserted"
			(Stage WavefrontSchedule $?)
			(Substage Merge $?)
			?fct <- (Determine schedule style for ?cpv into block ?e)
			(object (is-a BasicBlock) (ID ?e) (Paths $?paths))
			(object (is-a CompensationPathVector) (ID ?cpv)
					  (Paths $?cpvPaths))
			;the two sets are the same
			(test (equal$ ?paths ?cpvPaths))
			=>
			(retract ?fct)
			(assert (Move ?cpv into ?e)))
;------------------------------------------------------------------------------
(defrule ScheduleStyleForCPVIsCompensate
			"This rule attempts to determine if the CPV should be copied into the 
			given block on the wavefront. If this is true then the fact to perform 
			this action will be asserted."
			(Stage WavefrontSchedule $?)
			(Substage Merge $?)
			?fct <- (Determine schedule style for ?cpv into block ?e)
			(object (is-a BasicBlock) (ID ?e) (Paths $?paths))
			(object (is-a CompensationPathVector) (ID ?cpv)
					  (Paths $?cpvPaths) (Parent ?i))
			;there are more paths in the CPV than in the block
			(test (subsetp ?paths ?cpvPaths))
			=>
			(retract ?fct)
			(assert (Clone ?cpv into ?e)))
;------------------------------------------------------------------------------
(defrule RemoveScheduleStyleForCPV
			(declare (salience 1))
			(Stage WavefrontSchedule $?)
			(Substage Merge $?)
			?fct <- (Determine schedule style for ?cpv into block ?e)
			(object (is-a BasicBlock) (ID ?e) (Paths $?paths) (Parent ?q))
			(object (is-a CompensationPathVector) (ID ?cpv)
					  (Paths $?cpvPaths) (Parent ?i))
			?agObj <- (object (is-a PathAggregate) (Parent ?e))
			(test (not (subsetp ?paths ?cpvPaths)))
			=>
			;TODO: Put code in here to delete a given instruction from the target
			;      instruction list as well. 
			;
			; Eventually, I will detect if we are in a loop. If we are then it is
			; necessary to figure out which paths remain in the loop and those
			; that exit. 
			;this should prevent a potential infinite loop
			;(printout t "Preventing " ?i " from being scheduled into " ?e crlf)
			(retract ?fct)
			(bind ?ind (member$ ?i (send ?agObj get-InstructionList)))
			(if ?ind then (slot-delete$ ?agObj InstructionList ?ind ?ind)))
;------------------------------------------------------------------------------
(defrule MoveInstructionIntoBlock
			"Moves the given object into bottom of the given block"
			(Stage WavefrontSchedule $?)
			(Substage Merge $?)
			?fct <- (Move ?cpv into ?e)
			?newBlock <- (object (is-a BasicBlock) 
										(ID ?e) 
										(Contents $?blockBefore ?last)
                    (Produces $?nBProds))
			?agObj <- (object (is-a PathAggregate) 
									(Parent ?e)
                  (InstructionPropagation $?agIP)
                  (ScheduledInstructions $?agSI)
                  (ReplacementActions $?agRA))
			?terminator <- (object (is-a TerminatorInstruction) 
										  (Pointer ?tPtr) 
										  (ID ?last) 
										  (TimeIndex ?ti) 
										  (Parent ?e))
			?cpvObject <- (object (is-a CompensationPathVector) 
										 (ID ?cpv) 
										 (Parent ?inst)
                     (ScheduleTargets $?cpvST)
                     (Aliases $?cpvAliases))
			?newInst <- (object (is-a Instruction) 
									  (ID ?inst) 
									  (Pointer ?nPtr) 
									  (Parent ?otherBlock) 
									  (DestinationRegisters ?register) 
                    (Consumers $?niConsumers)
									  (Class ?class))
			?oldBlock <- (object (is-a BasicBlock) 
										(ID ?otherBlock) 
										(Produces $?pBefore ?inst $?pRest)
										(Contents $?before ?inst $?rest))
			;TODO: add another rule where we have to update the consumers list as
			;      well
			=>
      (object-pattern-match-delay
			;(printout t "Scheduled " ?inst " into " ?e crlf)
			(modify-instance ?terminator (TimeIndex (+ ?ti 1)))
      ;(modify-instance ?newBlock (Produces ?nBProds ?register))
			(modify-instance ?oldBlock (Contents $?before $?rest) 
								  (Produces $?pBefore $?pRest))
			;(modify-instance ?cpvObject (Paths))
			(assert (Remove evidence of ?inst from instructions $?niConsumers)
								 ;(send ?newInst get-Consumers))
					  (Recompute block ?otherBlock))
			(retract ?fct)
			(if (eq StoreInstruction ?class) then 
       (modify-instance ?agObj 
        (ScheduledInstructions $?agSI ?inst ?register)
        (ReplacementActions $?agRA ?inst ?inst !))
			  ;(slot-insert$ ?agObj ScheduledInstructions 1 ?inst ?register)
			  (modify-instance ?newBlock 
         (Produces $?nBProds ?register)
         (Contents $?blockBefore ?inst ?last))
        (modify-instance ?cpvObject 
         (Paths)
         (ScheduleTargets ?cpvST ?e ?inst)
         (Aliases $?cpvAliases ?inst ?e))
			  (llvm-unlink-and-move-instruction-before ?nPtr ?tPtr)
			  ;(slot-insert$ ?cpvObject ScheduleTargets 1 ?e ?inst)
			  ;(slot-insert$ ?cpvObject Aliases 1 ?inst ?e)
			  ;(slot-insert$ ?agObj ReplacementActions 1 ?inst ?inst !)
			  else
			  (bind ?newName (sym-cat movedinstruction. (gensym*) . ?inst))
        (modify-instance ?cpvObject (Paths)
         (ScheduleTargets ?cpvST ?e ?newName)
         (Aliases ?cpvAliases ?newName ?e))
			  ;(slot-insert$ ?cpvObject ScheduleTargets 1 ?e ?newName)
			  ;(slot-insert$ ?cpvObject Aliases 1 ?newName ?e)
			  ;(slot-insert$ ?agObj ReplacementActions 1 ?inst ?newName !)
			  (modify-instance ?newBlock 
         (Produces $?nBProds ?register)
         (Contents $?blockBefore ?newName ?last))
			  (bind ?newPtr (llvm-clone-instruction ?nPtr ?newName))
			  ;purge the list of producers and consumers
			  (duplicate-instance ?inst to ?newName 
										 (ID ?newName) 
										 (Name ?newName)
										 (Pointer ?newPtr) 
										 (Producers) 
										 (Consumers)
										 (NonLocalDependencies) 
										 (LocalDependencies)
										 (TimeIndex ?ti) 
										 (Parent ?e))
			  (llvm-move-instruction-before ?newPtr ?tPtr)
			  (slot-insert$ ?oldBlock UnlinkedInstructions 1 ?inst)
        (modify-instance ?agObj (ReplacementActions $?agRA ?inst ?newName !)
         (InstructionPropagation $?agIP ?inst ?newName ?e !)
         (ScheduledInstructions $?agSI ?inst)))))
			  ;(slot-insert$ ?agObj InstructionPropagation 1 ?inst ?newName ?e !)
			  ;(slot-insert$ ?agObj ScheduledInstructions 1 ?inst))))
;------------------------------------------------------------------------------
(defrule CloneInstructionIntoBlock
			"Moves the given object into bottom of the given block"
			(Stage WavefrontSchedule $?)
			(Substage Merge $?)
			?fct <- (Clone ?cpv into ?e)
			?newBlock <- (object (is-a BasicBlock) 
										(ID ?e) 
										(Contents $?blockBefore ?last))
			?agObj <- (object (is-a PathAggregate) 
									(Parent ?e))
			?terminator <- (object (is-a TerminatorInstruction) 
										  (Pointer ?tPtr) 
										  (ID ?last) 
										  (TimeIndex ?ti) 
										  (Parent ?e))
			?cpvObject <- (object (is-a CompensationPathVector) 
										 (ID ?cpv) 
										 (Parent ?inst) 
										 (Paths $?cpvPaths))
			?newInst <- (object (is-a Instruction) 
									  (ID ?inst) 
									  (Pointer ?nPtr) 
									  (Parent ?otherBlock) 
									  (DestinationRegisters ?register) 
									  (Class ?class))
			=>
			;we also need to update all CPVs within 
			(retract ?fct)
  (object-pattern-match-delay
			(bind ?newName (sym-cat compensation.copy. (gensym*) . ?inst))
			;(printout t "Scheduled " ?inst " into " ?e " from " ?otherBlock 
			;            " as " ?newName crlf)
			(bind ?newPtr (llvm-clone-instruction ?nPtr ?newName))
			;purge the list of producers and consumers
			(duplicate-instance ?inst to ?newName 
									  (ID ?newName) 
									  (Name ?newName)
									  (Pointer ?newPtr) 
									  (Parent ?e)
									  (TimeIndex (+ ?ti 1)))
			(llvm-move-instruction-before ?newPtr ?tPtr)
			;we add the original name so that we don't have to do
			; an insane number of updates to the CPVs that follow
			; this object
			(if (eq StoreInstruction ?class) then 
			  (slot-insert$ ?agObj ScheduledInstructions 1 ?inst ?register)
			  else
			  (slot-insert$ ?agObj InstructionPropagation 1 ?inst ?newName ?e !)
			  (slot-insert$ ?agObj ScheduledInstructions 1 ?inst))
			(slot-insert$ ?newBlock Produces 1 ?register)
			(modify-instance ?newBlock (Contents $?blockBefore ?newName ?last))
			(slot-insert$ ?cpvObject ScheduleTargets 1 ?e ?newName)
			(slot-insert$ ?cpvObject Aliases 1 ?newName ?e) 
			(slot-insert$ ?agObj ReplacementActions 1 ?inst ?newName !)
			(assert (Recompute block ?otherBlock)
					  (Reopen blocks from ?cpv))
			(bind ?leftOvers (create$))
			(progn$ (?z ?cpvPaths)
					  (bind ?cPath (symbol-to-instance-name ?z))
					  (if (not (member$ ?e (send ?cPath get-Contents))) then
						 (bind ?leftOvers (insert$ ?leftOvers 1 ?z))))
			(modify-instance ?cpvObject (Paths ?leftOvers))))
;------------------------------------------------------------------------------
(defrule FAILURE-CLONE
			(declare (salience -768))
			(Stage WavefrontSchedule $?)
			(Substage Merge $?)
			(Clone ?cpv into ?e)
			(object (is-a CompensationPathVector) (ID ?cpv) (Parent ?p))
			=>
			(printout t "ERROR: Didn't clone " ?p " into " ?e crlf)
			(exit))
;------------------------------------------------------------------------------
(defrule FAILURE-MOVE
			(declare (salience -768))
			(Stage WavefrontSchedule $?)
			(Substage Merge $?)
			(Move ?cpv into ?e)
			(object (is-a CompensationPathVector) (ID ?cpv) (Parent ?p))
			=>
			(printout t "ERROR: Didn't move " ?p " into " ?e crlf)
			(exit))
;------------------------------------------------------------------------------
(defrule FAILURE-SCHEDULE-STYLE
			(declare (salience -768))
			(Stage WavefrontSchedule $?)
			(Substage Merge $?)
			(Determine schedule style for ?cpv into block ?e)
			?o <- (object (is-a CompensationPathVector) (ID ?cpv) (Parent ?p)
							  (Paths $?cpvPaths))
			?pa <- (object (is-a PathAggregate) (Parent ?e))
			(object (is-a Instruction) (ID ?p) (Parent ?bb))
			(object (is-a BasicBlock) (ID ?e) (Parent ?r) (Paths $?paths))
			(object (is-a Wavefront) (Parent ?r) (Contents $?z) (Closed $?y))
			(object (is-a Region) (ID ?r) (Entrances ?x $?))
			(object (is-a BasicBlock) (ID ?x) (Paths $?allPaths))
			=>
			(printout t "ERROR: Couldn't figure out scheduling stype for " ?p 
						 " which is targeted for " ?e crlf
						 "Blocks on the wavefront = " ?z crlf
						 "Closed Blocks = " ?y crlf
						 "For reference ?cpvPaths = " ?cpvPaths crlf
						 "For reference aliases of ?cpv are = " 
						 (send ?o get-Aliases) crlf
						 "For reference ?paths = " ?paths crlf
						 "Parent of " ?p " is " ?bb crlf
						 "Printing out the path aggregate for " ?p crlf )
			(send ?pa print)
			(progn$ (?apath ?allPaths)
					  (printout t "  " ?apath " = " 
									(send (symbol-to-instance-name ?apath) 
											get-Contents) 
									crlf))
			(facts)
			(exit))
;------------------------------------------------------------------------------
; Rules for reopening blocks on the wavefront
;------------------------------------------------------------------------------
(defrule AssertReopenBlocksOnWavefront
			(Stage WavefrontSchedule $?)
			(Substage ReopenBlocks $?)
			?fct <- (Reopen blocks from ?cpv)
			?obj <- (object (is-a CompensationPathVector) (ID ?cpv) 
								 (Failures $?failures))
			=>
			(retract ?fct)
			(modify-instance ?obj (Failures))
			(assert (From ?cpv reopen $?failures)))
;------------------------------------------------------------------------------
(defrule ReopenBlockOnWavefront
			(Stage WavefrontSchedule $?)
			(Substage ReopenBlocks $?)
			?fct <- (From ?cpv reopen ?fail $?failures)
			?wave <- (object (is-a Wavefront) (ID ?w) (Closed $?a ?fail $?b)
								  (Contents $?cnts))
			?bb <- (object (is-a BasicBlock) (ID ?fail) (IsOpen FALSE))
			?pa <- (object (is-a PathAggregate) (Parent ?fail)
								(ImpossibleCompensationPathVectors $?icpv))
			=>
			(modify-instance ?bb (IsOpen TRUE))
			(modify-instance ?pa (ImpossibleCompensationPathVectors)
								  (TargetCompensationPathVectors $?icpv))
			(progn$ (?q ?icpv)
					  (slot-insert$ ?pa InstructionList 1 
										 (send (symbol-to-instance-name ?q) get-Parent)))
			(modify-instance ?wave (Contents $?cnts ?fail) (Closed ?a ?b))
			(retract ?fct)
			(assert (From ?cpv reopen $?failures)))
;------------------------------------------------------------------------------
(defrule ReaddFailureToCPV
			(Stage WavefrontSchedule $?)
			(Substage ReopenBlocks $?)
			?fct <- (From ?cpv reopen ?fail $?failures)
			?wave <- (object (is-a Wavefront) (ID ?w) (Closed $?c))
			(test (not (member$ ?fail $?c)))
			?obj <- (object (is-a CompensationPathVector) (ID ?cpv))
			=>
			(slot-insert$ ?obj Failures 1 ?fail)
			(retract ?fct)
			(assert (From ?cpv reopen $?failures)))
;------------------------------------------------------------------------------
(defrule RetractEmptyReopenFact
			(Stage WavefrontSchedule $?)
			(Substage ReopenBlocks $?)
			?fct <- (From ? reopen)
			=>
			(retract ?fct))
;------------------------------------------------------------------------------

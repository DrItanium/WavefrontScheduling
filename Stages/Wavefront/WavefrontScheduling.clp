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
; The idea for wavefront scheduling is that we pull a region, construct
; schedules for all of the blocks within the region, identify blocks that can
; relinquish control over instructions and move them up and out of the given
; block and into blocks on the wavefront.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

(defrule RetractPotentiallyValidBlocksThatAreCompletelyEnclosed
         (Stage WavefrontSchedule $?)
         (Substage Strip $?)
         (CompletelyInvalid blocks for ?e are $?t)
         ?pv1 <- (PotentiallyValid blocks for ?e are $?q)
         (test (subsetp ?q ?t))
         =>
         (retract ?pv1))

(defrule StripoutIndividualElementsFromPotentiallyValid
         (declare (salience -1))
         (Stage WavefrontSchedule $?)
         (Substage Strip $?)
         ?f0 <- (PotentiallyValid blocks for ?e are $?before ?car $?rest)
         (CompletelyInvalid blocks for ?e are $? ?car $?)
         =>
         (retract ?f0)
         (assert (PotentiallyValid blocks for ?e are $?before $?rest)))

(defrule RetractEmptyPotentiallyValid
         (declare (salience -100))
         (Stage WavefrontSchedule $?)
         (Substage Strip $?)
         ?f0 <- (PotentiallyValid blocks for ?e are)
         =>
         (retract ?f0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule InjectPotentiallyValidBlocks 
         (Stage WavefrontSchedule $?)
         (Substage Inject $?)
         ;get the Mrs. Hitler birth certificate
         ?fct <- (PotentiallyValid blocks for ?e are ?t $?q)
         ?pa <- (object (is-a PathAggregate) (Parent ?e))
         =>
         (retract ?fct)
         (assert (PotentiallyValid blocks for ?e are $?q))
         (if (eq FALSE (member$ ?t (send ?pa get-PotentiallyValid))) then
           (slot-insert$ ?pa PotentiallyValid 1 ?t)))

(defrule PotentiallyValidBlocksUpdate-Last
         (Stage WavefrontSchedule $?)
         (Substage Inject $?)
         ;get the Mrs. Hitler birth certificate
         ?fct<- (PotentiallyValid blocks for ?e are)
         =>
         (retract ?fct))

(defrule InjectCompletelyInvalidBlocks 
         (Stage WavefrontSchedule $?)
         (Substage Inject $?)
         ;get the Mrs. Hitler birth certificate
         ?fct <- (CompletelyInvalid blocks for ?e are ?t $?rest)
         ?pa <- (object (is-a PathAggregate) (Parent ?e))
         =>
         (retract ?fct)
         (assert (CompletelyInvalid blocks for ?e are $?rest))
         (if (eq FALSE (member$ ?t (send ?pa get-CompletelyInvalid))) then
           (slot-insert$ ?pa CompletelyInvalid 1 ?t)))

(defrule CompletelyInvalidBlocksUpdate-Last
         (Stage WavefrontSchedule $?)
         (Substage Inject $?)
         ;get the Mrs. Hitler birth certificate
         ?fct <- (CompletelyInvalid blocks for ?e are)
         =>
         (retract ?fct))

(defrule InjectMemoryBarrierBlocks 
         (Stage WavefrontSchedule $?)
         (Substage Inject $?)
         ;get the Mrs. Hitler birth certificate
         ?fct <- (Element ?t has a MemoryBarrier for ?e)
         ?pa <- (object (is-a PathAggregate) (Parent ?e))
         =>
         (retract ?fct)
         (if (eq FALSE (member$ ?t (send ?pa get-MemoryBarriers))) then
           (slot-insert$ ?pa MemoryBarriers 1 ?t)))


(defrule InjectCallBarrierBlocks 
         (Stage WavefrontSchedule $?)
         (Substage Inject $?)
         ;get the Mrs. Hitler birth certificate
         ?fct <- (Element ?t has a CallBarrier for ?e)
         ?pa <- (object (is-a PathAggregate) (Parent ?e))
         =>
         (retract ?fct)
         (if (eq FALSE (member$ ?t (send ?pa get-CallBarriers))) then
           (slot-insert$ ?pa CallBarriers 1 ?t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; now that we have a path aggregate we need to get the list of instruction
; CPV's that represent valid movable instructions for the given block on the
; wavefront. 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defrule SelectValidCPVs 
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         (object (is-a Wavefront) (Parent ?r) (Contents $? ?e $?))
         (object (is-a BasicBlock) (ID ?e) (IsOpen TRUE))
         ?pa <- (object (is-a PathAggregate) (ID ?ag) (Parent ?e)
                        (PotentiallyValid $?pv))
         =>
         (assert (For ?e find CPVs for $?pv)))

(defrule FindValidCPVsForBlock
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (For ?e find CPVs for ?pv $?pvs)
         (object (is-a BasicBlock) (ID ?pv) (Contents $?instructions))
         =>
         (retract ?fct)
         (assert (For ?e find CPVs for $?pvs)
                 (Get CPVs out of ?pv for ?e using $?instructions)))

(defrule SkipRegionsForFindingValidCPVsForBlock
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (For ?e find CPVs for ?pv $?pvs)
         (object (is-a Region) (ID ?pv)) 
         =>
         (retract ?fct)
         (assert (For ?e find CPVs for $?pvs)))

(defrule RetractValidCPVsForBlock
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (For ?e find CPVs for)
         =>
         (retract ?fct))

(defrule IgnorePHIInstructions
         (declare (salience 1))
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using ?inst $?insts)
         (object (is-a PhiNode) (ID ?inst))
         =>
         (retract ?fct)
         (assert (Get CPVs out of ?pv for ?e using $?insts)))

(defrule IgnoreCallInstructions
         (declare (salience 1))
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using ?inst $?insts)
         (object (is-a CallInstruction) (ID ?inst))
         =>
         (retract ?fct)
         (assert (Get CPVs out of ?pv for ?e using $?insts)))

(defrule IgnoreTerminatorInstructions
         (declare (salience 1))
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using ?inst $?insts)
         (object (is-a TerminatorInstruction) (ID ?inst))
         =>
         (retract ?fct)
         (assert (Get CPVs out of ?pv for ?e using $?insts)))
(defrule DisableInstructionsDependentOnPhis
         (declare (salience 1))
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using ?inst $?insts)
         (object (is-a Instruction) (ID ?inst) (DestinationRegisters $? ?reg $?))
         (object (is-a PhiNode) (ID ?reg))
         =>
         (retract ?fct)
         (assert (Get CPVs out of ?pv for ?e using $?insts)))

(defrule DisableInstructionsDependentOnPhis-SourceRegisters
         (declare (salience 1))
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using ?inst $?insts)
         (object (is-a Instruction) (ID ?inst) (SourceRegisters $? ?reg $?))
         (object (is-a PhiNode) (ID ?reg))
         =>
         (retract ?fct)
         (assert (Get CPVs out of ?pv for ?e using $?insts)))
(defrule TagValidCPVs
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using ?inst $?insts)
         (object (is-a Instruction) (ID ?isnt) (IsTerminator FALSE) (HasCallDependency FALSE))
         =>
         ;(printout t "Tagged " ?inst " as valid for " ?e crlf)
         ;(facts)
         (retract ?fct)
         (assert (Get CPVs out of ?pv for ?e using $?insts)
                 (Marked ?inst as valid for block ?e)))

(defrule RetractDrainedGetCPVFacts
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Get CPVs out of ?pv for ?e using)
         =>
         (retract ?fct))

(defrule ReloadCPVIntoNewAggregate
         "Put the CPV that has already been created into the target path aggregate"
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Marked ?inst as valid for block ?e)
         (exists (object (is-a CompensationPathVector) (Parent ?inst)))
         (object (is-a CompensationPathVector) (Parent ?inst) (ID ?cpvID))
         ?agObj <- (object (is-a PathAggregate) (ID ?ag) (Parent ?e))
         (object (is-a Instruction) (ID ?inst) (NonLocalDependencies $?nlds)
                 (DestinationRegisters ?reg) (Class ?class))
         (test (eq FALSE (member$ ?cpvID (send ?agObj
                                               get-ImpossibleCompensationPathVectors))))
         =>
         (retract ?fct)
         (if (eq FALSE (member$ ?inst (send ?agObj get-InstructionList)))
           then
         ;  (printout t "Added " ?inst " to " ?e " from ReloadCPV " crlf)
           (slot-insert$ ?agObj InstructionList 1 ?inst))
         (if (eq FALSE (member$ ?reg (send ?agObj get-InstructionList))) then
         ;  (printout t "Added " ?reg " to " ?e " from ReloadCPV " crlf)
           (slot-insert$ ?agObj InstructionList 1 ?reg))
         (foreach ?nld ?nlds
                  (if (eq FALSE (member$ ?nld (send ?agObj get-InstructionList))) then
                    ;(printout t "Added non-local dependency " ?nld " to " ?e " from ReloadCPV" crlf)
                    (slot-insert$ ?agObj InstructionList 1 ?nld)))
         (slot-insert$ ?agObj CompensationPathVectors 1 ?cpvID))

(defrule CPVIsImpossible
         (Stage WavefrontSchedule $?)
         (Substage Acquire $?)
         ?fct <- (Marked ?inst as valid for block ?e)
         (exists (object (is-a CompensationPathVector) (Parent ?inst)))
         (object (is-a CompensationPathVector) (Parent ?inst) (ID ?cpvID))
         ?agObj <- (object (is-a PathAggregate) (ID ?ag) (Parent ?e))
         (object (is-a Instruction) (ID ?inst) (NonLocalDependencies $?nlds)
                 (DestinationRegisters ?reg) (Class ?class))
         (test (neq FALSE (member$ ?cpvID (send ?agObj
                                                get-ImpossibleCompensationPathVectors))))
         =>
         ;add the non-local dependencies
         (foreach ?nld ?nlds
                  (if (eq FALSE (member$ ?nld (send ?agObj get-InstructionList))) then
                    ;(printout t "Added non-local dependency " ?nld " to " ?e " from ImpossibleCPV" crlf)
                    (slot-insert$ ?agObj InstructionList 1 ?nld)))
         (retract ?fct))

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
         ;(printout t "(Marked " ?inst " as valid for block " ?e ")" crlf)
         ;(printout t "Original block = " ?pv crlf)
         (bind ?name (gensym*))
         (slot-insert$ ?pa CompensationPathVectors 1 ?name)
         (make-instance ?name of CompensationPathVector (Parent ?inst) 
                        (Paths $?paths) (OriginalBlock ?pv))
         (if (eq FALSE (member$ ?inst (send ?pa get-InstructionList)))
           then 
           (slot-insert$ ?pa InstructionList 1 ?inst))
         (if (eq FALSE (member$ ?reg (send ?pa get-InstructionList))) then
           (slot-insert$ ?pa InstructionList 1 ?reg))
         (foreach ?nld ?nlds
                  (if (eq FALSE (member$ ?nld (send ?pa get-InstructionList)))
                    then
                    ;(printout t "Added non-local dependency " ?nld " to " ?e " from MakeCPV" crlf)
                    (slot-insert$ ?pa InstructionList 1 ?nld))))
;(printout t "Created a CompensationPathVector for " ?c crlf)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Now we go through and attempt to schedule the instruction represented by 
; each CPV into the block on the wavefront. I call this stage merge. I had some
; far raunchier names but this is my thesis. Some of the potential names were
; OneeChanTheresNoWayThatCanFit, ImAMexiCan, Copulation, and many more.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defrule SetifyInstructionList
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?pa <- (object (is-a PathAggregate) (InstructionList $?a ?b $?c ?b $?d))
         =>
         (modify-instance ?pa (InstructionList $?a ?b $?c $?d)))
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
                 (Generate slices for block ?e in ?r with cpv ?cpv with stop block ?b 
                           using paths $?paths)))

(defrule RetractEmptySlicesCreationFact
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slices for block ? in ? using)
         =>
         (retract ?fct))
;we need to bond each path to a given 
(defrule QueryCanCreateSliceForPath
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slices for block ?e in ?r with cpv ?cpv with stop block ?b using paths ?path $?paths)
         (object (is-a Path) (ID ?path) (Contents $?z))
         (test (neq FALSE (member$ ?e ?z)))
         =>
         (retract ?fct)
         (assert (Generate slice for block ?e in ?r with cpv ?cpv with stop block
                           ?b using path ?path)
                 (Generate slices for block ?e in ?r with cpv ?cpv with stop block
                           ?b using paths $?paths)))

(defrule QueryCantCreateSliceForPath
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slices for block ?e in ?r with cpv ?cpv with stop block ?b using paths ?path $?paths)
         (object (is-a Path) (ID ?path) (Contents $?z))
         (test (eq FALSE (member$ ?e ?z)))
         =>
         (retract ?fct)
         (assert (Generate slices for block ?e in ?r with cpv ?cpv with stop block
                           ?b using paths $?paths)))

(defrule TryConstructNewSlice
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slice for block ?e in ?r with cpv ?cpv with stop block ?b using path ?path)
         (not (exists (object (is-a Slice) (Parent ?b) (TargetPath ?path) (TargetBlock ?e))))
         (object (is-a Path) (ID ?path) (Contents $? ?e $?slice ?b $?))
         =>
         (retract ?fct)
         (make-instance (gensym*) of Slice (Parent ?b) (TargetPath ?path)
                        (TargetBlock ?e) (Contents $?slice)))

(defrule SliceAlreadyExists
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slice for block ?e in ?r with cpv ?cpv with stop block ?b using path ?path)
         (exists (object (is-a Slice) (Parent ?b) (TargetPath ?path) (TargetBlock ?e)))
         =>
         (retract ?fct))

(defrule RemoveSliceAnalysisFact
         (Stage WavefrontSchedule $?)
         (Substage Slice $?)
         ?fct <- (Generate slices for block ?e in ?r with cpv ?cpv with stop block ?b using paths)
         =>
         (retract ?fct))

;only construct slices as we see fit as we can just reference them again.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Now that we have slices constructed it's time to run through the
; analyze-merge cycle. First up, analyze. In this phase we need to see if it
; is possible to schedule into the block. Actually, I can see that we already
; did the hard work as any regions that would have prevented code from moving
; up would have already prevented the block from being selected. Thus we should
; just check to see if we have a local dependency
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defrule InitialCPVSetupForPathAggregate
         "Load all of the compensation path vectors for the given path aggregate into
         the aggregates TargetCompensationPathVectors multifield"
         (Stage WavefrontSchedule $?)
         (Substage AnalyzeInit $?)
         (object (is-a Wavefront) (Contents $? ?blkID $?))
         ?agObj <- (object (is-a PathAggregate) (Parent ?blkID) 
                           (CompensationPathVectors $?cpvIDs))
         (test (> (length$ ?cpvIDs) 0))
         =>
         (modify-instance ?agObj (TargetCompensationPathVectors $?cpvIDs)))
(defrule SetifyTargetCompensationPathVectors
         (Stage WavefrontSchedule $?)
         (Substage AnalyzeInit $?)
         ?pa <- (object (is-a PathAggregate) (TargetCompensationPathVectors $?a ?b $?c ?b
                                                                            $?d))
         =>
         (modify-instance ?pa (TargetCompensationPathVectors $?a ?b $?c $?d)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defrule SelectCPVForAnalysis
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
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
         (foreach ?cpv ?cpvs
                  (bind ?o (symbol-to-instance-name ?cpv))
                  (bind ?pp (send ?o get-Paths))
                  (bind ?determinant FALSE)
                  (foreach ?p ?pp
                           (bind ?o2 (symbol-to-instance-name ?p))
                           (if ?determinant then 
                             (break)
                             else
                             (bind ?determinant 
                                   (or ?determinant
                                       (neq FALSE (member$ ?e (send ?o2 get-Contents)))))))
                  (if ?determinant then 
                    (bind ?result (create$ ?result ?cpv))))
         (assert (Analyze block ?e for ?r using cpvs $?result)))

(defrule SegmentCPVsApart
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Analyze block ?e for ?r using cpvs ?cpv $?cpvs)
         (object (is-a BasicBlock) (ID ?e))
         (object (is-a CompensationPathVector) (ID ?cpv) (Parent ?i))
         =>
         (retract ?fct)
         (assert (Analyze block ?e for ?r using cpvs $?cpvs)
                 (Analyze instruction ?i { associated cpv ?cpv } for ?e)))

(defrule RetractCPVSegmentationFact
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Analyze block ?a for ?b using cpvs)
         =>
         (retract ?fct))

(defrule TargetCPVIsImpossibleToScheduleIntoTargetBlock
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Analyze instruction ?i { associated cpv ?cpv } for ?e)
         ?agObj <- (object (is-a PathAggregate) (Parent ?e) (InstructionList $?il))
         (object (is-a Instruction) (ID ?i) 
                 (LocalDependencies $?ld)
                 (NonLocalDependencies $?nld))
         (test (not (and (subsetp ?ld ?il)
                         (subsetp ?nld ?il))))
         =>
         ;(printout t ?i " is impossible to schedule into " ?e crlf)
         (retract ?fct)
         (bind ?ind (member$ ?i ?il))
         (if (neq ?ind FALSE) then 
           (slot-delete$ ?agObj InstructionList ?ind ?ind))
         (assert (Cant schedule ?cpv for ?e ever)))

(defrule TargetCPVCantBeScheduledIntoTargetBlockYet
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Analyze instruction ?i { associated cpv ?cpv } for ?e)
         ?paObj <- (object (is-a PathAggregate) (Parent ?e) (InstructionList $?il)
                           (ScheduledInstructions $?sched))
         (object (is-a Instruction) (ID ?i) (LocalDependencies $?ld) 
                 (NonLocalDependencies $?nld) (Parent ?parent))
         (test (and (not (subsetp ?ld ?sched))
                    (subsetp ?ld ?il)
                    (subsetp ?nld ?il)))
         =>
         ;(printout t "Can't schedule " ?i " into " ?e " right now!" crlf)
         ;(printout t "Non Local Dependencies = " ?nld crlf)
         ;(printout t "Local Dependencies = " ?ld crlf)
         ;(printout t "Scheduled = " ?sched crlf)
         ;(printout t "Instruction List = " ?il crlf)
         ;(printout t "From = " ?parent crlf)
         (retract ?fct)
         (assert (Cant schedule ?cpv for ?e now)))

(defrule TargetCPVNeedsToBeSliceAnalyzed
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Analyze instruction ?i { associated cpv ?cpv } for ?e)
         (object (is-a PathAggregate) (Parent ?e) 
                 (ScheduledInstructions $?sched))
         (object (is-a Instruction) (ID ?i) (Parent ?b) (LocalDependencies $?ld))
         (test (subsetp ?ld ?sched))
         (object (is-a CompensationPathVector) (ID ?cpv) (Paths $?paths))
         (object (is-a BasicBlock) (ID ?b))
         =>
         ;(printout t "Instruction " ?i " needs to be slice analyzed for " ?e
         ;          crlf)
         (bind ?validPaths (create$))
         (foreach ?z ?paths
                  (bind ?obj (instance-name (symbol-to-instance-name ?z)))
                  (if (neq FALSE 
                           (member$ ?e (send ?obj get-Contents))) then
                    (bind ?validPaths (create$ ?validPaths ?z))))
         ;(printout t "validPaths for " ?cpv " = " ?validPaths crlf)
         (retract ?fct)
         (if (> (length$ ?validPaths) 0) then
           (assert (Pull slices for range ?e to ?b for instruction ?i { 
                         associated cpv ?cpv } using paths $?validPaths))))

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

(defrule RetractSliceSegmenterFact
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Pull slices for range ? to ? for instruction ? {
                       associated cpv ? } using paths)
         =>
         (retract ?fct))

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

(defrule MergeSliceAnalysisFacts-SingleSingle
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?f0 <- (Analyze slice ?s0 for ?e and cpv ?cpv)
         ?f1 <- (Analyze slice ?s1 for ?e and cpv ?cpv)
         (test (and (neq ?f0 ?f1) (neq ?s0 ?s1)))
         =>
         (retract ?f0 ?f1)
         (assert (Analyze in ?e using cpv ?cpv and slices ?s0 ?s1)))
(defrule ConvertSingleSliceRule
         (declare (salience -3))
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?f0 <- (Analyze slice ?s0 for ?e and cpv ?cpv)
         =>
         (retract ?f0)
         (assert (Analyze in ?e using cpv ?cpv and slices ?s0)))
;(defrule RetractSliceAnalysisFacts-SingleSingle
;         (Stage WavefrontSchedule $?)
;         (Substage Analyze $?)
;         ?f0 <- (Analyze slice ?s0 for ?e and cpv ?cpv)
;         ?f1 <- (Analyze slice ?s1 for ?e and cpv ?cpv)
;         (test (and (neq ?f0 ?f1) (neq ?s0 ?s1)))
;         =>
;         (retract ?f0 ?f1)
;         (assert (Analyze in ?e using cpv ?cpv and slices ?s0 ?s1)))

(defrule MergeSliceAnalysisFacts-SingleMulti
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?f0 <- (Analyze slice ?s0 for ?e and cpv ?cpv)
         ?f1 <- (Analyze in ?e using cpv ?cpv and slices $?z)
         (test (eq FALSE (member$ ?s0 $?z)))
         =>
         (retract ?f0 ?f1)
         (assert (Analyze in ?e using cpv ?cpv and slices $?z ?s0)))

(defrule RetractSliceAnalysisFacts-SingleMulti
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?f0 <- (Analyze slice ?s0 for ?e and cpv ?cpv)
         ?f1 <- (Analyze in ?e using cpv ?cpv and slices $?z)
         (test (neq FALSE (member$ ?s0 $?z)))
         =>
         (retract ?f0))

(defrule MergeSliceAnalysisFacts-MultiMulti
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?f0 <- (Analyze in ?e using cpv ?cpv and slices $?q)
         ?f1 <- (Analyze in ?e using cpv ?cpv and slices $?z)
         (test (neq ?f0 ?f1)) 
         =>
         (retract ?f0 ?f1)
         (assert (Analyze in ?e using cpv ?cpv and slices $?z $?q)))

(defrule SetifyAnalyzeSlicesFact
         (declare (salience -1))
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices $?a ?b $?c ?b $?d)
         =>
         (retract ?fct)
         (assert (Analyze in ?e using cpv ?cpv and slices $?a ?b $?c $?d)))

(defrule ERROR-ANALYSIS-FAILURE
         (declare (salience -900))
         (Stage WavefrontSchedule $?)
         (Substage Analyze $?)
         (Analyze instruction ?i for ?blkID)
         ?inst <- (object (is-a Instruction) (ID ?i))
         (object (is-a PathAggregate) (Parent ?blkID) (ScheduledInstructions $?si))
         ?cpv <- (object (is-a CompensationPathVector) (Parent ?i))
         =>
         (printout t "ERROR: ANALYZE INSTRUCTION " ?i " WASN'T MATCHED!!!" crlf)
         (printout t "SCHEDULED INSTRUCTIONS: " $?si crlf)
         (send ?inst print)
         (printout t crlf)
         (send ?cpv print)
         (exit))

; now that we have a list of slices to look at it's time to check and see if
; the given cpv can be moved up based on the slice. If it can't then assert 
; a fact that says as much

(defrule RetractSliceAnalysis
         "Retract all slice analysis if it turns out there is a failure fact"
         (Stage WavefrontSchedule $?)
         (Substage SliceAnalyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices $?)
         (exists (Cant schedule ?cpv for ?e ?))
         =>
         (retract ?fct))

(defrule AnalyzeSliceContentsForFailure-ProducerLowerThanTargetBlock
         "Does a check to make sure that non local dependencies prevent an instruction
         from being moved upward into the target block"
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
         ; (printout t "Failed Instruction " ?i " because producer is lower than block "
         ;					 ?e " on the wavefront" crlf)
         (retract ?fct)
         (bind ?ind (member ?i (send ?agObj get-InstructionList)))
         (if (neq FALSE ?ind) then
           (slot-delete$ ?agObj InstructionList ?ind ?ind))
         (assert (Cant schedule ?cpv for ?e ever)))

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
         ;(printout t "Removed " ?i " from being scheduled - Call Barrier" crlf)
         (bind ?ind (member$ ?i (send ?agObj get-InstructionList)))
         (if (neq FALSE ?ind) then 
           (slot-delete$ ?agObj InstructionList ?ind ?ind))
         (assert (Cant schedule ?cpv for ?e ever)))

(defrule SliceTargetHasMemoryBarrier
         "The given slice has an element that contains a memory barrier. A memory
         barrier is only created when analysis has failed to ascertain what is being
         read from or written to in memory."
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
         ;(printout t "Removed " ?i " from being scheduled into " ?e " - MemoryBarrier" crlf)
         (bind ?ind (member$ ?i (send ?agObj get-InstructionList)))
         (if (neq FALSE ?ind) then 
           (slot-delete$ ?agObj InstructionList ?ind ?ind))
         (assert (Cant schedule ?cpv for ?e ever)))

(defrule SliceTargetDoesntHaveMemoryBarrier-ModifiesSameMemory
         "The given slice has an element that contains a entry in the WritesTo list
         that is the same thing as the given load or store instruction"
         (Stage WavefrontSchedule $?)
         (Substage SliceAnalyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices ?s $?ss)
         (object (is-a Slice) (ID ?s) (TargetBlock ?e) 
                 (Parent ?b) (Contents $? ?element $?))
         (object (is-a CompensationPathVector) (ID ?cpv) (Parent ?i))
         ?instruction <- (object (is-a LoadInstruction|StoreInstruction) (ID ?i)
                                 (MemoryTarget ?mt) (DestinationRegisters ?dr))
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
         ;(send ?instruction print)
         ;(printout t crlf)
         ;(send ?agObj print)
         ;(printout t crlf)
         (assert (Cant schedule ?cpv for ?e ever)))

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

(defrule CanScheduleIntoBlockOnSlice
         (declare (salience -2))
         (Stage WavefrontSchedule $?)
         (Substage SliceAnalyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices ?s $?ss)
         =>
         (retract ?fct)
         (assert (Analyze in ?e using cpv ?cpv and slices $?ss)))



(defrule CanScheduleInstructionThisIteration
         (declare (salience -3))
         (Stage WavefrontSchedule $?)
         (Substage SliceAnalyze $?)
         ?fct <- (Analyze in ?e using cpv ?cpv and slices)
         =>
         (retract ?fct)
         (assert (Can schedule ?cpv for ?e)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defrule AddCPVToSuccessList
         (Stage WavefrontSchedule $?)
         (Substage MergeInit $?)
         ?fct <- (Can schedule ?cpvID for ?blkID)
         ?agObj <- (object (is-a PathAggregate) (Parent ?blkID))
         =>
         (retract ?fct)
         (slot-insert$ ?agObj MovableCompensationPathVectors 1 ?cpvID))

(defrule FailCPVForNow
         (Stage WavefrontSchedule $?)
         (Substage MergeInit $?)
         ?fct <- (Cant schedule ?cpvID for ?blkID now)
         ?agObj <- (object (is-a PathAggregate) (Parent ?blkID))
         =>
         (retract ?fct)
         (slot-insert$ ?agObj StalledCompensationPathVectors 1 ?cpvID))

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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;TODO INSERT CODE HANDLING PHI INSTRUCTION CREATION!!!
;     THIS WILL HAVE TO MODIFY THE ENTIRE RANGE OF THE INSTRUCTION MERGE
;     HOWEVER AT THIS POINT I NEED TO PUSH FORWARD. 
;    
;     THE IDEA BEHIND THIS THE PHI NODE CREATION IS THAT WE PROPAGATE THE
;     TRANSLATION TABLE THROUGH THE ACT OF MOVING INSTRUCTIONS INTO THE BLOCK
;     WHICH WILL ALLOW THE BLOCK ON THE WAVEFRONT TO DETERMINE IF IT NEEDS TO
;     GENERATE A PHI INSTRUCTION TO CONVERGE ALL OF THE PATHS FOR THE GIVEN
;     INSTRUCTION. THIS CAUSES THE ENTRIES FROM ALL OF THE DIFFERENT 
;     PREDECESSORS THAT REFER TO THAT INSTRUCTION TO BE REPLACED WITH THE NEW
;     PHI NODE'S NAME. THAT NAME IS PROPAGATED TO THE CHILDREN OF THIS NODE. 
;     WHENEVER WE HIT A CASE WHERE A JOIN BLOCK ENCOUNTERS THE SAME INSTRUCTION
;     ON MULTIPLE INSTRUCTIONPROPAGATION LISTS THEN IT IS A CANDIDATE FOR PHI
;     NODE CREATION AND REPLACEMENT.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defrule PonderMovementIteration
         (declare (salience 100))
         (Stage WavefrontSchedule $?)
         (Substage Ponder $?)
         (object (is-a Wavefront) (ID ?r) (Contents $? ?e $?))
         ?ag <- (object (is-a PathAggregate) (Parent ?e) (ID ?pa))
         (test (> (length$ (send ?ag get-StalledCompensationPathVectors)) 0))
         =>
         (bind ?container (send ?ag get-StalledCompensationPathVectors))
         ;(bind ?iContainer (create$))
         ;(foreach ?z ?container
         ; (bind ?iContainer (insert$ ?iContainer 1 (send (symbol-to-instance-name ?z)
         ;                         get-Parent))))
         ;(printout t "?container = " ?container crlf)
         ;(printout t "?iContainer = " ?iContainer crlf)
         (modify-instance ?ag (StalledCompensationPathVectors)
                          (TargetCompensationPathVectors ?container)))

(defrule DetermineIfAnotherMovementIsRequired
         (declare (salience -100))
         (Stage WavefrontSchedule $?)
         ?ponder <- (Substage Ponder $?rest)
         =>
         ;this returns a tuple
         (if (any-instancep ((?inst PathAggregate)) 
                            (> (length$ ?inst:TargetCompensationPathVectors) 0)) then
           (retract ?ponder)
           ;(printout t "Another Movement Required!" crlf)
           (assert (Substage Analyze SliceAnalyze MergeInit Merge MergeUpdate
                             ReopenBlocks Ponder $?rest))
           else
           (bind ?instances (find-all-instances ((?wave Wavefront)) TRUE))
           (foreach ?instance ?instances
                    (bind ?children (send ?instance get-Contents))
                    (foreach ?child ?children
                             (bind ?obj (symbol-to-instance-name ?child))
                             (modify-instance ?obj (IsOpen FALSE))))))

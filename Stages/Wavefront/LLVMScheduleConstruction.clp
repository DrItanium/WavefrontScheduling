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
(defrule ConstructScheduleObjectForBlock-HasPhis
         (declare (salience 10))
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectCreation $?)
         ?fct <- (Schedule ?e for ?r)
         (object (is-a TerminatorInstruction) (Parent ?e) (ID ?last))
         (object (is-a BasicBlock) (ID ?e) (Parent ?r)
                 (Contents $? ?lastPhi ?firstNonPhi $?instructions ?last $?))
         (object (is-a PhiNode) (ID ?lastPhi))
         (object (is-a Instruction&~PhiNode&~TerminatorInstruction) (ID ?firstNonPhi))
         =>
         ;strange that ?last is being incorporated into $?q
         (retract ?fct)
         ;(printout t "Retracted (Schedule " ?e " for " ?r ")" crlf)
         (assert (Update style for ?e is ?lastPhi))
         (make-instance (gensym*) of Schedule (Parent ?e) 
                        (Contents ?firstNonPhi ?instructions)))

(defrule ConstructScheduleObjectForBlock-DoesntHavePhis
         (declare (salience 10))
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectCreation $?)
         ?fct <- (Schedule ?e for ?r)
         (object (is-a BasicBlock) (ID ?e) (Parent ?r)
                 (Contents ?firstNonPhi $?instructions ?last $?))
         (object (is-a Instruction&~PhiNode&~TerminatorInstruction) (ID ?firstNonPhi))
         (object (is-a TerminatorInstruction) (Parent ?e) (ID ?last))
         =>
         (retract ?fct)
         ;(printout t "Retracted (Schedule " ?e " for " ?r ")" crlf)
         (assert (Update style for ?e is))
         (make-instance (gensym*) of Schedule (Parent ?e) 
                        (Contents ?firstNonPhi ?instructions)))

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
         ;(printout t "Retracted (Schedule " ?e " for " ?r ")" crlf)
         (retract ?fct))

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


(defrule PreschedulePhiNodes
         "Adds all phi nodes into the list of scheduled instructions.
         We can always assume they are ready to go too!"
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectCreation $?)
         ?schedObj <- (object (is-a Schedule) (ID ?n) (Parent ?p))
         (object (is-a BasicBlock) (ID ?p) (Contents $? ?c $?))
         (object (is-a PhiNode) (ID ?c))
         (test (eq FALSE (member$ ?c (send ?schedObj get-Scheduled))))
         =>
         (slot-insert$ ?schedObj Scheduled 1 ?c))
(defrule PrescheduleNonLocals
         "Marks all non local instructions as already scheduled. With the way that the
         dependency analysis goes only instructions that are actually valid will be
         scheduled first."
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectCreation $?)
         ?schedObj <- (object (is-a Schedule) (ID ?n) (Parent ?p) 
                              (Contents $? ?c $?))
         ?inst <- (object (is-a Instruction) (ID ?c) (Parent ?p)
                          (NonLocalDependencies $? ?d $?))
         (test (eq FALSE (member$ ?d (send ?schedObj get-Scheduled))))
         =>
         (slot-insert$ ?schedObj Scheduled 1 ?d))


(defrule PrintoutSchedules
         "Marks all non local instructions as already scheduled. With the way that the
         dependency analysis goes only instructions that are actually valid will be
         scheduled first."
         (declare (salience -10))
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectCreation $?)
         (Debug)
         (Schedule)
         ?schedule <- (object (is-a Schedule) (ID ?q))
         =>
         (send ?schedule print))

(defrule AssertCreateInstructionGroup
         (declare (salience -100))
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectCreation $?)
         (object (is-a Schedule) (ID ?q))
         =>
         ;(printout t "Fired AssertCreateInstructionGroup for " ?q crlf)
         (assert (Create InstructionGroup for ?q)))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defrule MakeInstructionGroupForSchedulePhase
         (declare (salience 2701))
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectUsage $?)
         ?fct <- (Create InstructionGroup for ?q)
         ?sched <- (object (is-a Schedule) (ID ?q) (TimeGenerator ?tg)
                           (Parent ?p) (Groups $?groups))
         (not (exists (object (is-a InstructionGroup) (TimeIndex ?tg) (Parent ?p))))
         =>
         (retract ?fct)
         (bind ?name (gensym*))
         ;(printout t "Contents for " ?q " = " (send ?sched get-Contents) crlf)
         (assert (Perform Schedule ?q for ?p))
         (make-instance ?name of InstructionGroup (Parent ?p) (TimeIndex ?tg))
         (modify-instance ?sched (TimeGenerator (+ 1 ?tg)) (Groups ?groups ?name)))

(defrule CanScheduleInstructionNow
         (declare (salience 343))
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectUsage $?)
         (Perform Schedule ?n for ?b)
         ?sched <- (object (is-a Schedule) (ID ?n) (Parent ?b)
                           (Contents ?curr $?) (Scheduled $?s))
         (object (is-a Instruction) (ID ?curr) 
                 (LocalDependencies $?p))
         (test (subsetp $?p $?s))
         =>
         ;(printout t "Scheduled " ?curr crlf)
         (slot-delete$ ?sched Contents 1 1)
         (slot-insert$ ?sched Success 1 ?curr))

(defrule MustStallInstructionForSchedule
         (declare (salience 343))
         (Stage WavefrontSchedule $?)
         (Substage ScheduleObjectUsage $?)
         (Peform Schedule ?n for ?b)
         ?sched <- (object (is-a Schedule) (ID ?n) 
                           (Contents ?curr $?) (Scheduled $?s))
         (object (is-a Instruction) (ID ?curr) 
                 (LocalDependencies $?p))
         (test (not (subsetp $?p $?s)))
         =>
         ;(printout t "Stalled " ?curr " Producers = " ?p ", and Scheduled = "
         ;          ?s " and success = " (send ?sched get-Success) crlf)
         (slot-delete$ ?sched Contents 1 1)
         (slot-insert$ ?sched Failure 1 ?curr))

(defrule EndInstructionScheduleAttempt
         ;(declare (salience 343))
         (Stage WavefrontSchedule $?)
         (Substage ResetScheduling $?)
         ?fct <- (Perform Schedule ?n for ?)
         ?sched <- (object (is-a Schedule) (ID ?n)
                           (Contents))
         =>
         (retract ?fct))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defrule ShouldCreateNewInstructionGroup
         (declare (salience 360))
         (Stage WavefrontSchedule $?)
         (Substage ResetScheduling $?)
         (object (is-a Schedule) (ID ?n) (Success $?len)
                 (Failure $?fail) (TimeGenerator ?tg))
         (test (and (> (length$ ?fail) 0) (> (length$ ?len) 0)))
         =>
         (assert (Create InstructionGroup for ?n)))

(defrule PutSuccessfulInstructionIntoInstructionGroup
         (declare (salience 270))
         (Stage WavefrontSchedule $?)
         (Substage ResetScheduling $?)
         ?sched <- (object (is-a Schedule) (ID ?n)
                           (Parent ?p)
                           (Success ?targ $?) 
                           (Groups $? ?last))
         ?ig <- (object (is-a InstructionGroup) (ID ?last) (Parent ?p)
                        (TimeIndex ?t))
         (object (is-a Instruction) (ID ?targ))
         =>
         (slot-insert$ ?sched Scheduled 1 ?targ)
         (slot-delete$ ?sched Success 1 1)
         (slot-insert$ ?ig Contents 1 ?targ))

(defrule PutSuccessfulStoreInstructionIntoInstructionGroup
         (declare (salience 271))
         (Stage WavefrontSchedule $?)
         (Substage ResetScheduling $?)
         ?sched <- (object (is-a Schedule) (ID ?n)
                           (Parent ?p)
                           (Success ?targ $?) 
                           (Groups $? ?last))
         ?ig <- (object (is-a InstructionGroup) (ID ?last) (Parent ?p))
         (object (is-a StoreInstruction) (ID ?targ) (DestinationRegisters ?reg))
         =>
         ;we need to schedule the target register in as well
         (slot-insert$ ?sched Scheduled 1 ?targ ?reg)
         (slot-delete$ ?sched Success 1 1)
         (slot-insert$ ?ig Contents 1 ?targ))

(defrule FinishedPopulatingInstructionGroup-AssertReset
         (declare (salience 200))
         (Stage WavefrontSchedule $?)
         (Substage ResetScheduling $?)
         (object (is-a Schedule) (ID ?n) (Contents) (Success) 
                 (Failure $?elements))
         (test (> (length$ ?elements) 0))
         =>
         (assert (Reset schedule ?n)))

(defrule FinishedPopulatingInstructionGroup-AssertFinished
         (declare (salience 200))
         (Stage WavefrontSchedule $?)
         (Substage ResetScheduling $?)
         (object (is-a Schedule) (ID ?n)
                 (Parent ?p) (Contents) (Success) (Failure))
         =>
         (assert (Schedule ?p using ?n in llvm)))

(defrule ResetTargetScheduleForAnotherGo
         (declare (salience 180))
         (Stage WavefrontSchedule $?)
         (Substage ResetScheduling $?)
         ?fct <- (Reset schedule ?n)
         ?sched <- (object (is-a Schedule) (ID ?n) (Parent ?p) (Contents) 
                           (Failure $?elements))
         =>
         (retract ?fct)
         (modify-instance ?sched (Contents ?elements) (Failure))
         (assert (Reset scheduling process)))

(defrule ResetSchedulingProcess
         (declare (salience -10))
         (Stage WavefrontSchedule $?)
         ?f0 <- (Substage ResetScheduling $?rest)
         ?f1 <- (Reset scheduling process)
         =>
         (retract ?f0 ?f1)
         (assert (Substage ScheduleObjectUsage ResetScheduling $?rest)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defrule SetupSchedulingContainer 
         (declare (salience 100))
         (Stage WavefrontSchedule $?)
         (Substage InitLLVMUpdate $?)
         (Schedule ?p using ?n in llvm)
         (object (is-a BasicBlock) (ID ?p) (Contents $? ?last))
         (object (is-a TerminatorInstruction) (ID ?last) (Pointer ?tPtr))
         =>
         (bind ?name (gensym*))
         (bind ?n2 (gensym*))
         (make-instance ?n2 of Hint (Type SymbolContainer) (Parent ?p))
         (make-instance ?name of Hint (Type Container) (Parent ?p)
                        (Point ?tPtr))
         (assert (Merge ?p at 0 using ?name and ?n2)))


(defrule ConstructLLVMEncoding 
         (Stage WavefrontSchedule $?)
         (Substage InitLLVMUpdate $?)
         (Schedule ?p using ?n in llvm)
         ?fct <- (Merge ?p at ?index using ?name and ?n2)
         (object (is-a Schedule) (Parent ?p) (TimeGenerator ?ti&:(< ?index ?ti)))
         ?container <- (object (is-a Hint) (ID ?name) (Type Container) 
                               (Parent ?p))
         ?sContainer <- (object (is-a Hint) (ID ?n2) (Type SymbolContainer) 
                                (Parent ?p))
         (object (is-a InstructionGroup) (TimeIndex ?index) (Parent ?p) 
                 (Contents $?contents))
         ;we need to get the elements out correctly...so we drain them out
         =>
         (retract ?fct)
         (assert (Merge ?p at (+ ?index 1) using ?name and ?n2))
         (bind ?ptrs (symbol-to-pointer-list ?contents))
         (modify-instance ?sContainer (Contents 
                                        (send ?sContainer get-Contents) ?contents))
         (modify-instance ?container (Contents 
                                       (send ?container get-Contents) ?ptrs)))

(defrule FinishLLVMEncoding-HasPhi
         (declare (salience -12))
         (Stage WavefrontSchedule $?)
         (Substage LLVMUpdate $?)
         (Schedule ?p using ?n in llvm)
         ?f2 <- (Update style for ?p is ?lastPhi)
         ?f1 <- (Merge ?p at ?index using ?name and ?n2)
         (object (is-a Schedule) (Parent ?p) (TimeGenerator ?ti&:(>= ?index ?ti)))
         ?hint <- (object (is-a Hint) (ID ?name) (Type Container) (Parent ?p)
                          (Point ?tPtr) (Contents $?contents))
         ?hint2 <- (object (is-a Hint) (ID ?n2) (Type SymbolContainer) 
                           (Parent ?p) (Contents $?symbols))
         ?bb <- (object (is-a BasicBlock) (ID ?p) 
                        (Contents $?before ?lastPhi $?instructions ?last $?rest))
         (object (is-a TerminatorInstruction) (ID ?last) (Pointer ?tPtr))
         =>
         ;(printout t "?symbols = " ?symbols crlf)
         (modify-instance ?bb 
                          (Contents $?before ?lastPhi ?symbols ?last $?rest))
         (llvm-schedule-block ?tPtr ?contents)
         (retract ?f1 ?f2)
         (unmake-instance ?hint ?hint2))

(defrule FinishLLVMEncoding-NoPhi
         (declare (salience -12))
         (Stage WavefrontSchedule $?)
         (Substage LLVMUpdate $?)
         (Schedule ?p using ?n in llvm)
         ?f2 <- (Update style for ?p is)
         ?f1 <- (Merge ?p at ?index using ?name and ?n2)
         (object (is-a Schedule) (Parent ?p) (TimeGenerator ?ti&:(>= ?index ?ti)))
         ?hint <- (object (is-a Hint) (ID ?name) (Type Container) (Parent ?p)
                          (Point ?tPtr) (Contents $?contents))
         ?hint2 <- (object (is-a Hint) (ID ?n2) (Type SymbolContainer) 
                           (Parent ?p) (Contents $?symbols))
         ?bb <- (object (is-a BasicBlock) (ID ?p))
         (object (is-a TerminatorInstruction) (ID ?last) (Parent ?p) 
                 (Pointer ?tPtr))
         =>
         ;(printout t "?symbols = " ?symbols crlf)
         (modify-instance ?bb (Contents ?symbols ?last))
         (llvm-schedule-block ?tPtr ?contents)
         (retract ?f1 ?f2)
         (unmake-instance ?hint ?hint2))

(defrule RetractMergeHints
         (declare (salience -25))
         (Stage WavefrontSchedule $?)
         (Substage LLVMUpdate $?)
         ?fct <- (Merge ? at ? using ? and ?)
         =>
         (retract ?fct))

(defrule RetractUpdateStyleHint
         (declare (salience -26))
         (Stage WavefrontSchedule $?)
         (Substage LLVMUpdate $?)
         ?fct <- (Update style for ? is $?)
         =>
         (retract ?fct))
(defrule RetractScheduleHint
         (declare (salience -100))
         (Stage WavefrontSchedule $?)
         (Substage LLVMUpdate $?)
         ?fct <- (Schedule ? using ? in llvm)
         =>
         (retract ?fct))

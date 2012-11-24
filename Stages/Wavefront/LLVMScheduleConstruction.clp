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
			(make-instance (gensym*) of Schedule (Parent ?e) 
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
			(make-instance (gensym*) of Schedule (Parent ?e) 
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
			?schedObj <- (object (is-a Schedule) (ID ?n) (Parent ?p) (Scheduled
					$?s))
			(object (is-a BasicBlock) (ID ?p) (Contents $? ?c $?))
			(object (is-a PhiNode) (ID ?c))
			(test (not (member$ ?c ?s)))
							;(send ?schedObj get-Scheduled))))
			=>
			(slot-insert$ ?schedObj Scheduled 1 ?c))
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
			;(test (not (member$ ?d (send ?schedObj get-Scheduled))))
			=>
			(slot-insert$ ?schedObj Scheduled 1 ?d))
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
			?sched <- (object (is-a Schedule) (ID ?n) (Contents ?curr $?) 
									(Scheduled $?s))
			(object (is-a Instruction) (ID ?curr) (LocalDependencies $?p))
			(test (subsetp $?p $?s))
			=>
      (object-pattern-match-delay
			(slot-delete$ ?sched Contents 1 1)
			(slot-insert$ ?sched Success 1 ?curr)))
;------------------------------------------------------------------------------
(defrule MustStallInstructionForSchedule
			(declare (salience 343))
			(Stage WavefrontSchedule $?)
			(Substage ScheduleObjectUsage $?)
			(Perform Schedule ?n for ?b)
			?sched <- (object (is-a Schedule) (ID ?n) (Contents ?curr $?) 
									(Scheduled $?s))
			(object (is-a Instruction) (ID ?curr) (LocalDependencies $?p))
			(test (not (subsetp $?p $?s)))
			=>
      (object-pattern-match-delay 
			(slot-delete$ ?sched Contents 1 1)
			(slot-insert$ ?sched Failure 1 ?curr)))
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
									(Success ?targ $?))
			(object (is-a Instruction) (ID ?targ))
			=>
			(send ?sched .MarkScheduled ?targ 1))
;------------------------------------------------------------------------------
(defrule PutSuccessfulStoreInstructionIntoInstructionStream
			(declare (salience 271))
			(Stage WavefrontSchedule $?)
			(Substage ResetScheduling $?)
			?sched <- (object (is-a Schedule) (ID ?n) (Parent ?p)
									(Success ?targ $?))
			(object (is-a StoreInstruction) (ID ?targ) (DestinationRegisters ?reg))
			=>
			(send ?sched .MarkStoreScheduled ?targ ?reg 1))
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
			(retract ?fct)
			(assert (Perform Schedule ?n for ?p))
			(modify-instance ?sched (Contents ?elements) (Failure))
			(assert (Reset scheduling process)))
;------------------------------------------------------------------------------
(defrule ResetSchedulingProcess
			(declare (salience -10))
			(Stage WavefrontSchedule $?)
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
			(modify-instance ?bb 
								  (Contents $?before ?lastPhi ?stream ?last $?rest))
			(llvm-schedule-block ?tPtr (symbol-to-pointer-list ?stream))
			(retract ?f1 ?f2))
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
			(modify-instance ?bb (Contents ?stream ?last))
			(llvm-schedule-block ?tPtr (symbol-to-pointer-list ?stream))
			(retract ?f1 ?f2))
;------------------------------------------------------------------------------
(defrule RetractUpdateStyleHint
			(declare (salience -26))
			(Stage WavefrontSchedule $?)
			(Substage LLVMUpdate $?)
			?fct <- (Update style for ? is $?)
			=>
			(retract ?fct))
;------------------------------------------------------------------------------

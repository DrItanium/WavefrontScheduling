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
; Contains rules associated with the act of actually scheduling instructions
; into blocks on the wavefront
;
; Written by Joshua Scoggins
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

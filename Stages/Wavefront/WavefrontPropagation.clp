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

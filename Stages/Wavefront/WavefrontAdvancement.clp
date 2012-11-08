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

(defrule MarkShouldStayOnWavefront
				 (declare (salience 343))
				 (Stage WavefrontSchedule $?)
				 (Substage AdvanceIdentify $?)
				 ?wave <- (object (is-a Wavefront) (ID ?q) (Parent ?r) (DeleteNodes $?a ?b $?c))
				 ?bb <- (object (is-a Diplomat) (ID ?b) (NextPathElements ?s))
				 (object (is-a Diplomat) (ID ?s) (PreviousPathElements $?ppe))
				 (test (not (subsetp ?ppe (send ?wave get-DeleteNodes)))) 
				 ?agObj <- (object (is-a PathAggregate) (Parent ?b))
				 =>
				 (if (eq FALSE (member$ ?b (send ?wave get-Closed))) then
				   (bind ?ind (member$ ?b (send ?wave get-Contents)))
				   (slot-delete$ ?wave Contents ?ind ?ind)
				   (slot-insert$ ?wave Closed 1 ?b))
				 (modify-instance ?wave (DeleteNodes $?a $?c)))

(defrule DeleteElementFromWavefront
				 (declare (salience 180))
				 (Stage WavefrontSchedule $?)
				 (Substage Advance $?)
				 ?wave <- (object (is-a Wavefront) (ID ?id) (Parent ?r) (DeleteNodes ?a $?))
				 (object (is-a Diplomat) (ID ?a) (NextPathElements $?npe))
				 =>
				 ;(printout t "Deleting " ?a " from the wavefront " crlf)
				 (bind ?ind (member$ ?a (send ?wave get-Contents)))
				 (bind ?ind2 (member$ ?a (send ?wave get-Closed)))
				 (slot-delete$ ?wave DeleteNodes 1 1)
				 (if (neq ?ind FALSE) then
					 (slot-delete$ ?wave Contents ?ind ?ind))
				 (if (neq ?ind2 FALSE) then
					 (slot-delete$ ?wave Closed ?ind2 ?ind2))
				 (assert (Add into ?id blocks $?npe)))

(defrule PutSuccessorsOntoWavefront-Match
				 (declare (salience 100))
				 (Stage WavefrontSchedule $?)
				 (Substage AdvanceEnd $?)
				 ?fct <- (Add into ?id blocks ?next $?rest)
				 ?wave <- (object (is-a Wavefront) (ID ?id))
				 =>
				 ;(printout t "Adding " ?next " to the wavefront " ?id crlf)
				 (retract ?fct)
				 ;I know that this is procedural but I really want to get this done
				 (assert (Add into ?id blocks $?rest))
				 (if (eq FALSE (member$ ?next (send ?wave get-Contents))) then
					 (slot-insert$ ?wave Contents 1 ?next)))

(defrule PutSuccessorsOntoWavefront-NoMoreElements
				 (declare (salience 100))
				 (Stage WavefrontSchedule $?)
				 (Substage AdvanceEnd $?)
				 ?fct <- (Add into ? blocks)
				 =>
				 (retract ?fct))

(defrule PonderRestartOfWavefrontScheduling
				 (declare (salience -512))
				 (Stage WavefrontSchedule $?)
				 ?fct <- (Substage Update $?)
				 =>
				 ;(assert (END WAVEFRONT))
				 (bind ?instances (find-all-instances ((?wave Wavefront)) 
													 (> (length$ ?wave:Contents) 0)))
				 ;(foreach ?inst ?instances
				;	(printout t (send ?inst get-Contents) " " 
				;	 (send ?inst get-Closed) crlf))
				; (printout t crlf)
				 (if (> (length$ ?instances) 0) then
					 ;(printout t "==================================" crlf)
					 (retract ?fct)
					 (assert (Substage Init Identify PhiIdentify PhiNode 
														 PhiNodeUpdate Pathing Strip Inject 
														 Acquire Slice AnalyzeInit Analyze 
														 SliceAnalyze MergeInit Merge MergeUpdate
														 ReopenBlocks
														 Ponder Rename DependencyAnalysis ScheduleObjectCreation 
														 ScheduleObjectUsage ResetScheduling InitLLVMUpdate
														 LLVMUpdate AdvanceInit AdvanceIdentify
														 Advance
														 AdvanceEnd
														 Update))))

				 
(defrule RetractUnlinkedInstructions
				 (Stage WavefrontFinal $?)
				 ?bb <- (object (is-a BasicBlock) (ID ?b) (UnlinkedInstructions ?i $?rest))
				 ?instruction <- (object (is-a Instruction) (ID ?i) (Parent ?b) 
																 (Pointer ?ptr))
				 (object (is-a PathAggregate) (Parent ?b) 
					(InstructionPropagation $? ?i ?new ?b ! $?))
				 (object (is-a Instruction) (ID ?new) (Pointer ?nPtr))
				 =>
				 ;this is a little gross but it is a very easy way to ensure that
				 ;things work correctly
				 (llvm-replace-all-uses ?ptr ?nPtr)
         (modify-instance ?bb (UnlinkedInstructions $?rest))
				 (llvm-unlink-and-delete-instruction ?ptr)
				 (unmake-instance ?instruction))

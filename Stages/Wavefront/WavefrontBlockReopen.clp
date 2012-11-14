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

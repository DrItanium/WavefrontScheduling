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
; FrequencyAnalysis.clp - Determines which regions to apply wavefront
; scheduling to 
; Written by Joshua Scoggins (6/30/2012) 
;------------------------------------------------------------------------------
(defrule InstanceFrequencyCounter
				 "Creates a frequency counter hint for basic blocks"
				 (declare (salience 220))
				 (Stage Analysis $?)
				 (object (is-a Region) (ID ?p) (CanWavefrontSchedule FALSE))
				 =>
				 (make-instance of FrequencyAnalysis (Parent ?p)))
;------------------------------------------------------------------------------
(defrule IncrementFrequencyCounter-BasicBlock
				 "Goes through a given Region counting the number of basic blocks found within
				 the region. Valid blocks are blocks that contain more than one instruction as
				 we don't want to count JS nodes as they don't usually contain code."
				 (declare (salience 210))
				 (Stage Analysis $?)
				 (object (is-a Region) (ID ?p) (Contents $? ?t $?) (CanWavefrontSchedule FALSE))
				 (object (is-a BasicBlock) (ID ?t) (Parent ?p) (Contents $?insts))
				 (test (> (length$ $?insts) 1))
				 ?fa <- (object (is-a FrequencyAnalysis) (Parent ?p))
				 =>
				 (send ?fa .IncrementFrequency))
;------------------------------------------------------------------------------
(defrule ImplyEnoughBlocks
				 "There are enough blocks within the target region to make it a candidate for
				 wavefront scheduling. Make a hint that says this. "
				 (declare (salience 200))
				 (Stage Analysis $?)
				 ?fa <- (object (is-a FrequencyAnalysis) (Parent ?p) 
												(Frequency ?z&:(and (< ?z 100) (> ?z 1))))
				 ?region <- (object (is-a Region) (ID ?p))
				 =>
				 (unmake-instance ?fa)
				 (modify-instance ?region (CanWavefrontSchedule TRUE)))
;------------------------------------------------------------------------------

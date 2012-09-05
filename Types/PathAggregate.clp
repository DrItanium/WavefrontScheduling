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
(defclass PathAggregate 
  "The PathAggregate is a very useful data structure that keeps track of all
  information regarding paths and scheduling for a given block on the wavefront.
  Like all objects in this project, it is a tagged object so that it can be
  easily queried without knowing it's name directly. "
  (is-a TaggedObject)
  (slot OriginalStopIndex (type NUMBER))
  (multislot MemoryInvalid (visibility public))
  (multislot MemoryValid (visibility public))
  (multislot PotentiallyValid (visibility public))
  (multislot MemoryBarriers (visibility public))
  (multislot CallBarriers (visibility public))
  (multislot CompletelyInvalid (visibility public))
  ;compensation path vector aspect of the PathAggregate
  (multislot InstructionList (visibility public))
  (multislot ReplacementActions (visibility public))
  (multislot InstructionPropagation (visibility public))
  (multislot ScheduledInstructions (visibility public))
  (multislot CompensationPathVectors (visibility public))
  (multislot TargetCompensationPathVectors (visibility public))
  (multislot MovableCompensationPathVectors (visibility public))
  (multislot ImpossibleCompensationPathVectors (visibility public))
  (multislot StalledCompensationPathVectors (visibility public)))

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
; PartialAspectChokeIdentification.clp - Uses the list called UsedInBlocks 
; in each instruction to ; fill in the two choke lists the blocks associated
; with each entry of this list. This means that the parent of the instruction
; must dominate the block in question in order for the result of the
; instruction in question to be valid. 
; 
; It also means that the blocks where the target instruction is used post
; dominates the parent block of the target instruction.
;
; This is true because of the following idea
; Given basic blocks A and G where G uses a value computed in A
; There are several cases:
;------------------------------------------------------------------------------
; 1) G is a direct successor of A 
;------------------------------------------------------------------------------
;     This means that A must execute before G can. It also means that if G is 
;     the only successor of A then A chokes G for all given paths.
;------------------------------------------------------------------------------
; 2) G is not a direct successor of A but is a successor none the less
;------------------------------------------------------------------------------
;     This means that there are an arbitrary number of blocks in between A and
;     G. It also means that A must execute before G. Otherwise the register is
;     will not be correct.
;     
;     A chokes G in this case if G is contained in every single path that A is
;     contained in. This can be easily gleaned from the act of path
;     construction.
;------------------------------------------------------------------------------
; Written by Joshua Scoggins (6/23/2012)
;------------------------------------------------------------------------------
(defrule MarkChokedByBlocks
 (Stage Analysis $?)
 (object (is-a Region) (ID ?qq) (CanWavefrontSchedule TRUE))
 ?bb0 <- (object (is-a BasicBlock) (Parent ?qq) (ID ?name) (ProducingBlocks $? ?pre $?))
 (object (is-a BasicBlock) (ID ?pre) (ConsumingBlocks $? ?name $?))
 (test (eq (member$ ?pre (send ?bb0 get-ChokedBy)) FALSE))
 =>
 (modify-instance ?bb0 (ChokedBy (send ?bb0 get-ChokedBy) ?pre)))
;------------------------------------------------------------------------------
(defrule MarkChoked
 (Stage Analysis $?)
 (object (is-a Region) (ID ?qq) (CanWavefrontSchedule TRUE))
 ?bb0 <- (object (is-a BasicBlock) (Parent ?qq) (ID ?name) 
   (ConsumingBlocks $? ?target $?))
 (object (is-a BasicBlock) (ID ?target) (ProducingBlocks $? ?name $?))
 (test (eq (member$ ?target (send ?bb0 get-Chokes)) FALSE))
 =>
 (modify-instance ?bb0 (Chokes (send ?bb0 get-Chokes) ?target)))
;------------------------------------------------------------------------------

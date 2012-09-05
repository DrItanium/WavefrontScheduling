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
(defclass PointerOperandObject (is-a TaggedObject)
 (slot PointerOperand (type SYMBOL)))

(defclass MemoryModifyingObject (is-a PointerOperandObject)
 (slot Alignment (type NUMBER) (range 0 ?VARIABLE))
 (slot IsAtomic (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsSimple (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsUnordered (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsVolatile (type SYMBOL) (allowed-values FALSE TRUE)))

(defclass PhiNode (is-a Instruction)
 (slot IncomingValueCount (type NUMBER) (range 0 ?VARIABLE))
 (slot HasConstantValue (type SYMBOL) (allowed-values FALSE TRUE)))

(defclass CallInstruction (is-a Instruction)
 (slot CalledFunction (type SYMBOL))
 (slot IsDereferenceablePointer (type SYMBOL) (allowed-values FALSE TRUE))
 (slot HasValueHandle (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsTailCall (type SYMBOL) (allowed-values FALSE TRUE))
 (multislot ArgumentOperands)
 (slot CallingConvention (type SYMBOL))
 (multislot Attributes)
 (slot IsNoInline (type SYMBOL) (allowed-values FALSE TRUE))
 (slot CanReturnTwice (type SYMBOL) (allowed-values FALSE TRUE))
 (slot DoesNotAccessMemory (type SYMBOL) (allowed-values FALSE TRUE))
 (slot OnlyReadsMemory (type SYMBOL) (allowed-values FALSE TRUE))
 (slot DoesNotReturn (type SYMBOL) (allowed-values FALSE TRUE))
 (slot DoesNotThrow (type SYMBOL) (allowed-values FALSE TRUE))
 (slot HasStructRetAttr (type SYMBOL) (allowed-values FALSE TRUE))
 (slot HasByValArgument (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsInlineAsm (type SYMBOL) (allowed-values FALSE TRUE)))

(defclass IntrinsicInstruction (is-a CallInstruction)
 (slot IntrinsicID (type NUMBER)))
(defclass DBGInfoIntrinsic (is-a IntrinsicInstruction))
(defclass MemoryIntrinsic (is-a IntrinsicInstruction)
 (slot RawDestination)
 (slot Length (type NUMBER) (range 0 ?VARIABLE))
 (slot AlignmentConstant (type NUMBER))
 (slot Alignment (type NUMBER) (range 0 ?VARIABLE))
 (slot IsVolatile (type SYMBOL) (allowed-values FALSE TRUE))
 (slot DestinationAddressSpace (type NUMBER) (range 0 ?VARIABLE))
 (slot Destination (type SYMBOL)))

(defclass BinaryOperator (is-a Instruction)
	(slot HasNoUnsignedWrap (type SYMBOL) (allowed-values FALSE TRUE))
	(slot HasNoSignedWrap (type SYMBOL) (allowed-values FALSE TRUE))
	(slot IsExact (type SYMBOL) (allowed-values FALSE TRUE)))

(defclass UnaryInstruction (is-a Instruction))
(defclass AllocaInstruction (is-a UnaryInstruction)
 ; DO NOT UNCOMMENT THIS LINE, it is for management purposes only!
 ;(slot SetAlignment (name "set-alignment") (type ExternalFunction) (takes-in instance , unsigned aligned) (returns void))
 (slot IsStaticAllocation (type SYMBOL) (allowed-values FALSE TRUE))
 (slot Alignment (type NUMBER) (range 0 ?VARIABLE))
 (slot PointerType (type SYMBOL)) ; from AllocaInst::getType
 (slot PointerType-Pointer (type NUMBER) (range 0 ?VARIABLE))
 (slot IsArrayAllocation (type SYMBOL) (allowed-values FALSE TRUE)) 
 (slot ArraySize (type NUMBER) (range 0 ?VARIABLE))
 (slot IsStatic (type SYMBOL) (allowed-values FALSE TRUE)))

(defclass CastInstruction (is-a UnaryInstruction)
 (slot IsIntegerCast (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsLosslessCast (type SYMBOL) (allowed-values FALSE TRUE))
 (slot SourceType (type SYMBOL))
 (slot DestinationType (type SYMBOL)))

(defclass BitCastInstruction (is-a CastInstruction))
(defclass FPExtInstruction (is-a CastInstruction))
(defclass FPToSIInstruction (is-a CastInstruction))
(defclass FPToUIInstruction (is-a CastInstruction))
(defclass FPTruncInstruction (is-a CastInstruction))
(defclass IntToPtrInstruction (is-a CastInstruction))
(defclass PtrToIntInstruction (is-a CastInstruction))
(defclass SExtInstruction (is-a CastInstruction))

(defclass LoadInstruction (is-a UnaryInstruction MemoryModifyingObject)
 (slot PointerAddressSpace (type NUMBER) (range 0 ?VARIABLE)))
	;getOrdering() is for fences...fuck that..for now
	;getSynchScope() is another interesting one...no dice

(defclass VAArgInstruction (is-a UnaryInstruction PointerOperandObject))
(defclass CompareInstruction (is-a Instruction)
 (slot SignedPredicate)
 (slot UnsignedPredicate)
 (slot IsFPPredicate (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsIntPredicate (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsRelational (type SYMBOL) (allowed-values FALSE TRUE))
 (slot Predicate (type NUMBER))
 (slot InversePredicate (type NUMBER))
 (slot SwappedPredicate (type NUMBER))
 (slot Opcode (type NUMBER))
 (slot IsEquality (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsSigned (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsUnsigned (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsTrueWhenEqual (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsFalseWhenEqual (type SYMBOL) (allowed-values FALSE TRUE)))
(defclass FloatingPointCompareInstruction (is-a CompareInstruction))

(defclass IntegerCompareInstruction (is-a CompareInstruction))
(defclass TerminatorInstruction (is-a Instruction)
 (multislot Successors))
(defmessage-handler TerminatorInstruction .AddSuccessor (?succ)
 (bind ?self:Successors (create$ ?self:Successors ?succ)))

(defclass BranchInstruction (is-a TerminatorInstruction)
 (slot IsUnconditional (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsConditional (type SYMBOL) (allowed-values FALSE TRUE))
 (slot Condition)
 ;(slot SwapSuccessors (type EXTERNAL_FUNCTION))
 )
	
(defclass IndirectBranchInstruction (is-a TerminatorInstruction)
 (slot Address (type NUMBER) (range 0 ?VARIABLE)))
;We store the destinations within the destination registers
(defclass InvokeInstruction (is-a TerminatorInstruction)
 (multislot Arguments)
 (slot CalledFunction)
 (slot NormalDestination)
 (slot UnwindDestination)
 (slot IsNoInline (type SYMBOL) (allowed-values FALSE TRUE))
 (slot OnlyReadsMemory (type SYMBOL) (allowed-values FALSE TRUE))
 (slot DoesNotReturn (type SYMBOL) (allowed-values FALSE TRUE))
 (slot DoesNotThrow (type SYMBOL) (allowed-values FALSE TRUE))
 (slot HasStructRetAttr (type SYMBOL) (allowed-values FALSE TRUE))
 (slot HasByValArgument (type SYMBOL) (allowed-values FALSE TRUE)))
 ;We don't need to know what function is being called 
(defmessage-handler InvokeInstruction .AddArgument (?arg)
 (bind ?self:Arguments (create$ ?self:Arguments ?arg)))

(defmessage-handler InvokeInstruction .AddArguments ($?arg)
 (bind ?self:Arguments (create$ ?self:Arguments ?arg)))

(defclass ResumeInstruction (is-a TerminatorInstruction)
 (slot Value (type SYMBOL)))
(defclass ReturnInstruction (is-a TerminatorInstruction)
 (slot ReturnValue (type SYMBOL)))
(defclass SwitchEntry (is-a TaggedObject)
 (slot Index (type NUMBER))
 (slot Target (allowed-classes BasicBlock InteropObject SYMBOL)))
(defclass SwitchInstruction (is-a TerminatorInstruction)
 (slot Condition (type SYMBOL))
 (slot DefaultDestination (allowed-classes BasicBlock InteropObject SYMBOL))
 (multislot Cases))
(defclass UnreachableInstruction (is-a TerminatorInstruction))
(defclass GetElementPointerInstruction (is-a Instruction PointerOperandObject)
 (slot PointerAddressSpace (type NUMBER) (range 0 ?VARIABLE))
 (slot NumIndices (type NUMBER) (range 0 ?VARIABLE))
 (slot HasIndices (type SYMBOL) (allowed-values FALSE TRUE))
 (slot HasAllZeroIndices (type SYMBOL) (allowed-values FALSE TRUE))
 (slot HasAllConstantIndices (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsInBounds (type SYMBOL) (allowed-values FALSE TRUE)))
(defclass AtomicCompareExchangeInstruction (is-a Instruction PointerOperandObject)
 (slot IsVolatile (type SYMBOL) (allowed-values FALSE TRUE))
 (slot CompareOperand (type SYMBOL))
 (slot NewValOperand (type SYMBOL))
 (slot PointerAddressSpace (type NUMBER) (range 0 ?VARIABLE)))
(defclass AtomicRMWInstruction (is-a Instruction PointerOperandObject)
 (slot Operation (type SYMBOL))
 (slot IsVolatile (type SYMBOL) (allowed-values FALSE TRUE))
 (slot ValueOperand (type SYMBOL)))

(defclass LandingPadInstruction (is-a Instruction)
 (slot PersonalityFunction (type SYMBOL))
 (slot IsCleanup (type SYMBOL) (allowed-values FALSE TRUE))
 (multislot Clauses)
 (slot IsCatch (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsFilter (type SYMBOL) (allowed-values FALSE TRUE)))
(defclass SelectInstruction (is-a Instruction)
 (slot Condition (type SYMBOL))
 (slot TrueValue (type SYMBOL))
 (slot FalseValue (type SYMBOL)))
(defclass ShuffleVectorInstruction (is-a Instruction)
 (slot Mask (type NUMBER))
 (multislot ShuffleMask (type NUMBER) (cardinality 0 16)))
(defclass StoreInstruction (is-a Instruction MemoryModifyingObject)
 (slot ValueOperand (type SYMBOL)))
;This is one of those instructions that have to be done inside C++
; I'm not wasting my time pulling in the entire contents of these types
(defclass ExtractElementInstruction (is-a Instruction))
(defclass InsertElementInstruction (is-a Instruction))
(defclass InsertValueInstruction (is-a Instruction))
(defclass FenceInstruction (is-a Instruction))
(defclass ExtractValueInstruction (is-a UnaryInstruction)
 (multislot Indices)
 (slot AggregateOperand))

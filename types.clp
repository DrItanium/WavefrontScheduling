;------------------------------------------------------------------------------
;Copyright (c) 2012-2015, Joshua Scoggins 
;All rights reserved.
;
;Redistribution and use in source and binary forms, with or without
;modification, are permitted provided that the following conditions are met:
;    * Redistributions of source code must retain the above copyright
;      notice, this list of conditions and the following disclaimer.
;    * Redistributions in binary form must reproduce the above copyright
;      notice, this list of conditions and the following disclaimer in the
;      documentation and/or other materials provided with the distribution.
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
; Types.clp - contains all of the types used by wavefront scheduling
;------------------------------------------------------------------------------
(defclass thing 
  (is-a USER)
  (slot parent 
        (type SYMBOL
              INSTANCE)
        (visibility public)))

;------------------------------------------------------------------------------
(defclass PathAggregate 
  "The PathAggregate is a very useful data structure that keeps track of all
  information regarding paths and scheduling for a given block on the wavefront.
  Like all objects in this project, it is a tagged object so that it can be
  easily queried without knowing it's name directly. "
  (is-a thing)
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
;------------------------------------------------------------------------------
(defclass Slice (is-a thing)
  (slot TargetBlock (type SYMBOL) (visibility public))
  (slot TargetPath (type SYMBOL) (visibility public))
  (multislot Contents (visibility public)))
;------------------------------------------------------------------------------
; An InteropObject stores a pointer to a type outside CLIPS
;------------------------------------------------------------------------------
(defclass InteropObject (is-a USER)
  (slot Pointer (visibility public) (type NUMBER)))
;------------------------------------------------------------------------------
(defclass LLVMObject (is-a thing InteropObject)
  (slot Name (visibility public))
  (multislot WritesTo (visibility public))
  (multislot ReadsFrom (visibility public)))
;------------------------------------------------------------------------------
(defclass Diplomat 
  "A Diplomat is a collection of fields that interact with other
  objects."
  (is-a LLVMObject)
  (slot IsOpen (type SYMBOL) (visibility public) 
		(allowed-values FALSE TRUE))
  (slot HasCallBarrier (type SYMBOL) (visibility public) 
		(allowed-values FALSE TRUE))
  (slot HasMemoryBarrier (type SYMBOL) (visibility public) 
		(allowed-values FALSE TRUE))
  (multislot PreviousPathElements (visibility public))
  (multislot NextPathElements (visibility public))
  (multislot Consumes)
  (multislot Produces)
  ;(multislot Chokes (visibility public))
  ;(multislot ChokedBy (visibility public))
  (multislot Paths (visibility public)))
;(multislot RegionalAllies (visibility public))
;(multislot FunctionalAllies (visibility public)))

;(defmessage-handler Diplomat .AddRegionalAlly (?a)
; (bind ?self:RegionalAllies (create$ ?self:RegionalAllies ?a)))
;
;(defmessage-handler Diplomat .AddFunctionalAlly (?a)
; (bind ?self:FunctionalAllies (create$ ?self:FunctionalAllies ?a)))

;(defmessage-handler Diplomat .AddPath (?path)
; (bind ?self:Paths (create$ ?self:Paths ?path)))

;(defmessage-handler Diplomat .AddChokes (?blk)
; (bind ?self:Chokes (create$ ?self:Chokes ?blk)))
;
;(defmessage-handler Diplomat .AddChokedBy (?blk)
; (bind ?self:ChokedBy (create$ ?self:ChokedBy ?blk)))

;------------------------------------------------------------------------------
(defclass List (is-a thing)
  (slot Length (type NUMBER) (default-dynamic 0))
  (multislot Contents (visibility public)))

(defmessage-handler List .Add (?element)
					(slot-direct-insert$ Contents (+ ?self:Length 1) ?element)
					(bind ?self:Length (+ ?self:Length 1)))

(defmessage-handler List .AddBefore (?point ?element)
					(bind ?ind (nth$ ?point ?self:Contents))
					(slot-direct-insert$ Contents ?ind ?element)
					(bind ?self:Length (+ 1 ?self:Length)))

(defmessage-handler List .AddAfter (?point ?element)
					(bind ?ind (+ 1 (nth$ ?point ?self:Contents)))
					(slot-direct-insert$ Contents ?ind ?element)
					(bind ?self:Length (+ 1 ?self:Length)))

(defmessage-handler List .Remove (?element)
					(bind ?self:Length (- ?self:Length 1))
					(bind ?self:Contents (delete-member$ ?self:Contents ?element)))

(defmessage-handler List .RemoveAt (?index)
					(bind ?self:Contents (- ?self:Length 1))
					(slot-direct-delete$ Contents ?index ?index))


(defmessage-handler List .AddRangeAt (?index $?elements)
					(slot-direct-insert$ Contents ?index $?elements))

(defmessage-handler List .ElementAt (?index)
					(nth$ ?index ?self:Contents))

(defmessage-handler List .Contains (?item)
					(neq (member$ ?item ?self:Contents) FALSE))

(defmessage-handler List .ContainsSubset ($?subset)
					(subsetp ?subset ?self:Contents))
;------------------------------------------------------------------------------
(defclass LLVMType (is-a LLVMObject)
  (slot IsVoidType (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsHalfType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsFloatType (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsDoubleType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsX86FP80Type  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsFP128Type  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsPPCFP128Type  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsFloatingPointType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsX86MMXType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsFPOrFPVectorType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsLabelType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsMetadataType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsIntegerType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsIntOrIntVectorType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsFunctionType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsStructType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsArrayType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsPointerType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsVectorType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsEmptyType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsPrimitiveType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsDerivedType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsFirstClassType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsSingleValueType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsAggregateType  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsSized  (type SYMBOL) (allowed-values FALSE TRUE))
  (slot PrimitiveSizeInBits (type NUMBER) (range 0 ?VARIABLE))
  (slot ScalarSizeInBits (type NUMBER) (range 0 ?VARIABLE))
  (slot FPMantissaWidth (type NUMBER) (range 0 ?VARIABLE))
  (slot ScalarType (allowed-classes LLVMType))
  (multislot Subtypes)
  (multislot TypeMakeup (type SYMBOL))
  (slot IsFunctionVarArg (type SYMBOL) (allowed-values FALSE TRUE))
  (slot QuickType (type SYMBOL)))

(defclass IntegerType (is-a LLVMType)
  (slot BitWidth (type NUMBER) (range 0 ?VARIABLE))
  (slot BitMask (type NUMBER))
  (slot SignBit (type NUMBER))
  (slot IsPowerOf2ByteWidth (type SYMBOL) (allowed-values FALSE TRUE)))

(defclass FunctionType (is-a LLVMType)
  (slot IsVarArg (type SYMBOL) (allowed-values FALSE TRUE))
  (slot ReturnType (allowed-classes LLVMType))
  (multislot Parameters))


(defmessage-handler FunctionType GetNumParams ()
					(length ?self:Parameters))

(defmessage-handler FunctionType GetParamType (?index)
					(nth$ ?index ?self:Parameters))

(defclass CompositeType (is-a LLVMType)
  (multislot Indicies))

(defclass StructType (is-a CompositeType)
  (slot Name (type SYMBOL))
  (slot IsPacked (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsLiteral (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsOpaque (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsSized (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasName (type SYMBOL) (allowed-values FALSE TRUE))
  (multislot Body))

(defmessage-handler StructType SetBody (?element ?isPacked)
					(bind ?self:IsPacked ?isPacked)
					(bind ?self:Body ?element))

(defmessage-handler StructType SetBody$ ($?types)
					(bind ?self:Body (create$ ?self:Body ?types)))

(defmessage-handler StructType GetNumElements ()
					(length ?self:Body))

(defmessage-handler StructType Elements ()
					(return ?self:Body))

(defmessage-handler StructType GetElementType (?n)
					(if (> ?n (length ?self:Body)) then 
					  (printout t "ERROR: Element out of range for message GetElementType of StructType!" crlf)
					  (exit)
					  else 
					  (return (nth$ ?n ?self:Body))))

(defclass SequentialType (is-a CompositeType)
  (slot ElementType (allowed-classes LLVMType)))

(defclass VectorType (is-a SequentialType)
  (slot BitWidth (type NUMBER) (range 0 ?VARIABLE))
  (slot NumElements (type NUMBER) (range 0 ?VARIABLE)))

(defclass PointerType (is-a SequentialType)
  (slot AddressSpace (type NUMBER) (range 0 ?VARIABLE)))

(defclass ArrayType (is-a SequentialType)
  (slot NumElements (type NUMBER) (range 0 ?VARIABLE)))

;------------------------------------------------------------------------------
(defclass LLVMValue (is-a LLVMObject)
  (slot HasAddressTaken (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsLandingPad (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasOneUse (type SYMBOL) (allowed-values FALSE TRUE))
  (slot NumberOfUses (type NUMBER) (range 0 ?VARIABLE))
  (slot Type (visibility public))
  ;(slot Name (type STRING))
  (slot ValueName)
  (multislot Users)
  (slot ValueID (type NUMBER) (range 0 ?VARIABLE))
  (slot RawSubclassOptionalData (type NUMBER) (range 0 ?VARIABLE))
  (slot HasValueHandle (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsDereferenceablePointer (type SYMBOL) (allowed-values FALSE TRUE)))


;(defmessage-handler LLVMValue HasName ()
; (return (> (str-length ?self:Name) 0)))
(defmessage-handler LLVMValue GetNumUses ()
					(length ?self:Users))
(defmessage-handler LLVMValue HasNUses (?n)
					(= ?n (length ?self:Users)))
(defmessage-handler LLVMValue HasNUsesOrMore (?n)
					(>= ?n (length ?self:Users)))
(defmessage-handler LLVMValue HasSameSubclassOptionalData (?v)
					(= ?self:RawSubclassOptionalData (send ?v get-RawSubclassOptionalData)))
;------------------------------------------------------------------------------
(defclass Argument (is-a LLVMValue)
  (slot Index (type NUMBER) (range 0 ?VARIABLE))
  (slot HasByValueAttribute (type SYMBOL) (allowed-values FALSE TRUE))
  (slot ParameterAlignment (type NUMBER) (range 0 ?VARIABLE))
  (slot HasNestAttribute (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasNoAliasAttribute (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasNoCaptureAttribute (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasStructRetAttribute (type SYMBOL) (allowed-values FALSE TRUE))
  (multislot Attributes))
;------------------------------------------------------------------------------
(defclass LLVMUser (is-a LLVMValue)
  (multislot Operands (visibility public)))

(defmessage-handler LLVMUser .AddOperand (?op)
					(bind ?self:Operands (create$ ?self:Operands ?op)))
(defmessage-handler LLVMUser .AddOperands ($?ops)
					(bind ?self:Operands (create$ ?self:Operands ?ops)))

;------------------------------------------------------------------------------
(defclass LLVMInlineAsm (is-a LLVMValue)
  (slot HasSideEffects (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsAlignStack (type SYMBOL) (allowed-values FALSE TRUE))
  (slot FunctionType (allowed-classes LLVMType))
  (slot AsmString (type STRING))
  (slot ConstraintString (type STRING)))

;------------------------------------------------------------------------------
(defclass LLVMMDNode (is-a LLVMValue)
  (multislot Operands)
  (slot IsFunctionLocal (type SYMBOL) (allowed-values FALSE TRUE))
  (slot TargetFunction (type SYMBOL)))
(defclass LLVMMDString (is-a LLVMValue)
  (slot String (type STRING)))
;------------------------------------------------------------------------------
(defclass DependencyChain (is-a thing)
  (slot Producers (default-dynamic (make-instance (gensym*) of List)))
  (slot Consumers (default-dynamic (make-instance (gensym*) of List))))

(defmessage-handler DependencyChain init after ()
					(bind ?id (send ?self get-ID))
					(send ?self:Producers put-Parent ?id) 
					(send ?self:Consumers put-Parent ?id))
(defmessage-handler DependencyChain .ProducerCount ()
					(send ?self:Producers .Count))
(defmessage-handler DependencyChain .ConsumerCount ()
					(send ?self:Consumers .Count))
(defmessage-handler DependencyChain .AddProducers ($?p)
					(send ?self:Producers .AddRange ?p))
(defmessage-handler DependencyChain .AddProducer (?p) 
					"Adds a producer to the list of producers"
					(send ?self:Producers .SetAdd ?p))
(defmessage-handler DependencyChain .AddConsumer (?p)
					"Adds a producer to the list of consumers"
					(send ?self:Consumers .SetAdd ?p))

(defmessage-handler DependencyChain .AddConsumers ($?s)
					(send ?self:Consumers .AddRange ?s))

(defmessage-handler DependencyChain .IsProducer (?p)
					(send ?self:Producers .Contains ?p))

(defmessage-handler DependencyChain .IsConsumer (?p)
					(send ?self:Consumers .Contains ?p))

(defmessage-handler DependencyChain .HasProducers ()
					(not (send ?self:Producers .IsEmpty)))

(defmessage-handler DependencyChain .HasConsumers ()
					(not (send ?self:Consumers .IsEmpty)))

(defmessage-handler DependencyChain .RemoveConsumer (?v)
					(send ?self:Consumers .Remove ?v))

(defmessage-handler DependencyChain .RemoveProducer (?v)
					(send ?self:Producers .Remove ?v))

(defmessage-handler DependencyChain .ProducersContainsSubset ($?v)
					(send ?self:Producers .ContainsSubset $?v))

(defmessage-handler DependencyChain .ConsumersContainsSubset ($?v)
					(send ?self:Consumers .ContainsSubset $?v))

(defmessage-handler DependencyChain .Producers () 
					"Returns the list of producers from the dependency information"
					(return (send ?self:Producers get-Contents)))

(defmessage-handler DependencyChain .Consumers () 
					"Returns the list of consumers from the dependency information"
					(return (send ?self:Consumers get-Contents)))

;------------------------------------------------------------------------------
(defclass InstructionGroup (is-a thing)
  (multislot Contents (visibility public))
  (slot TimeIndex (type NUMBER) (visibility public)))
;------------------------------------------------------------------------------
(defclass Constant (is-a LLVMUser)
  (slot IsNullValue (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsAllOnesValue (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsNegativeZeroValue (type SYMBOL) (allowed-values FALSE TRUE))
  (slot CanTrap (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsConstantUsed (type SYMBOL) (allowed-values FALSE TRUE))
  (slot RelocationInfo (type SYMBOL) (default nil) (allowed-symbols nil NoRelocations
																	LocalRelocation GlobalRelocations)))

(defmessage-handler Constant init after ()
					(bind ?self:Type Constant))

(defclass BlockAddress (is-a Constant)
  (slot TargetBlock (type SYMBOL)))
(defclass ConstantAggregateZero (is-a Constant)
  (slot Element (type SYMBOL)))
(defclass ConstantArray (is-a Constant))
(defclass ConstantDataSequential (is-a Constant)
  (multislot Elements)
  (slot ElementType (type SYMBOL))
  (slot ElementCount (type NUMBER) (range 0 ?VARIABLE))
  (slot ElementByteSize (type NUMBER) (range 0 ?VARIABLE))
  (slot IsString (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsCString (type SYMBOL) (allowed-values FALSE TRUE)))

(defclass ConstantDataArray (is-a ConstantDataSequential))
(defclass ConstantDataVector (is-a ConstantDataSequential))
(defclass ConstantExpression (is-a Constant)
  (slot Operation)
  (slot IsCast (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsCompare (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasIndices (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsGEPWithNoNotionalOverIndexing (type SYMBOL) (allowed-values FALSE TRUE))
  (slot Opcode (type NUMBER) (range 0 ?VARIABLE))
  (slot Predicate (type NUMBER) (range 0 ?VARIABLE))
  (multislot Indices)
  (slot OpcodeName (type SYMBOL)))

(defclass BinaryConstantExpression (is-a ConstantExpression))
(defclass CompareConstantExpression (is-a ConstantExpression)
  (slot Predicate (type NUMBER)))

(defclass ConstantFloatingPoint (is-a Constant)
  (slot IsZero (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsNegative (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsNaN (type SYMBOL) (allowed-values FALSE TRUE))
  (slot Value (type FLOAT))
  )
;TODO: IsExactlyValue calls

(defclass ConstantInteger (is-a Constant)
  (slot ZeroExtendedValue (type NUMBER))
  (slot SignExtendedValue (type NUMBER))
  (slot Width (type NUMBER) (range 0 ?VARIABLE))
  (slot Value (type SYMBOL NUMBER))
  (slot IsNegative (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsZero (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsOne (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsMinusOne (type SYMBOL) (allowed-values FALSE TRUE)))
(defclass PointerConstant (is-a Constant)
  (slot PointerType (type SYMBOL)))
(defclass ConstantPointerNull (is-a PointerConstant))
(defclass ConstantStruct (is-a PointerConstant))
(defclass ConstantVector (is-a PointerConstant)
  (slot SplatValue (type SYMBOL)))

(defclass GlobalValue (is-a Constant)
  (slot Alignment (type NUMBER))
  (slot HasUnnamedAddress (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasDefaultVisibility (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasHiddenVisibility (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasProtectedVisibility (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasSection (type SYMBOL) (allowed-values FALSE TRUE))
  (slot Section (type SYMBOL))
  (slot UseEmptyExceptConstants (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasExternalLinkage (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasAvailableExternallyLinkage (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasLinkOnceLinkage (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasWeakLinkage (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasAppendingLinkage (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasInternalLinkage (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasPrivateLinkage (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasLinkerPrivateLinkage (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasLinkerPrivateWeakLinkage (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasLinkerPrivateWeakDefAutoLinkage (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasLocalLinkage (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasDLLImportLinkage (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasDLLExportLinkage (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasExternalWeakLinkage (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasCommonLinkage (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsWeakForLinker (type SYMBOL) (allowed-values FALSE TRUE))
  (slot MayBeOverridden (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsDeclaration (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsMaterializable (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsDematerializable (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasUnnamedAddr (type SYMBOL) (allowed-values FALSE TRUE))
  (slot Initializer))

(defclass GlobalVariable (is-a GlobalValue)
  (slot HasInitializer (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasDefinitiveInitializer (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasUniqueInitializer (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsConstant (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsThreadLocal (type SYMBOL) (allowed-values FALSE TRUE)))
(defclass GlobalAlias (is-a GlobalValue)
  (slot Aliasee))

(defclass UndefValue (is-a Constant))


;------------------------------------------------------------------------------
(defclass Schedule (is-a thing)
  (multislot Contents (visibility public))
  (multislot Scheduled (visibility public))
  (multislot Success (visibility public)) 
  (multislot Failure (visibility public))
  (multislot InstructionStream (visibility public)))
;(multislot Groups (visibility public))
; (slot TimeGenerator (type NUMBER) (default-dynamic 0)))

(defmessage-handler Schedule .ScheduledContainsSubset (?a)
					(subsetp (create$ ?a) ?self:Scheduled))
(defmessage-handler Schedule .AddScheduledInstruction (?i)
					(bind ?self:Scheduled (create$ ?self:Scheduled ?i)))

(defmessage-handler Schedule .MarkScheduled (?t ?ind)
					(slot-direct-insert$ Scheduled ?ind ?t)
					(slot-direct-delete$ Success ?ind ?ind)
					(slot-direct-insert$ InstructionStream (+ 1 (length$ ?self:Scheduled)) ?t))

(defmessage-handler Schedule .MarkStoreScheduled (?t ?s ?ind)
					(slot-direct-insert$ Scheduled ?ind ?t ?s)
					(slot-direct-delete$ Success ?ind ?ind)
					(slot-direct-insert$ InstructionStream (+ 1 (length$ ?self:Scheduled)) ?t))



;------------------------------------------------------------------------------
; Instruction.clp - Base LLVM Instruction class
;------------------------------------------------------------------------------

(defclass Instruction (is-a LLVMUser InteropObject)
  (slot NumSuccessors)
  (slot HasValueHandle (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsDereferenceablePointer (type SYMBOL) (allowed-values FALSE TRUE))
  (slot MayWriteToMemory (type SYMBOL) (allowed-values FALSE TRUE)) 
  (slot MayReadFromMemory (type SYMBOL) (allowed-values FALSE TRUE))
  (slot MayReadOrWriteMemory (type SYMBOL) (allowed-values FALSE TRUE))
  (slot MayHaveSideEffects (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasCallDependency (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsBinaryOp (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsTerminator (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsShift (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsCast (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsArithmeticShift (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsLogicalShift (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsAssociative (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsCommutative (type SYMBOL) (allowed-values FALSE TRUE))
  (slot Predicate (type SYMBOL))
  (slot Operation (type SYMBOL))
  (slot TimeIndex (type NUMBER) (default-dynamic 0))
  ;(slot ExecutionLength (type NUMBER) (default-dynamic -1))
  (slot MemoryTarget (type SYMBOL) (default-dynamic nil))
  (multislot LocalDependencies)
  (multislot NonLocalDependencies)
  (multislot Consumers)
  (multislot Producers)
  (multislot DestinationRegisters))
;(multislot SourceRegisters (visibility public)))
;(multislot BlocksUsedIn (visibility public)))
;(slot InstructionType (type SYMBOL) (default-dynamic nil)))
;------------------------------------------------------------------------------
;(defmessage-handler Instruction init after ()
;copy the Operands into SourceRegisters and Producers list
;this should save a ton of time... :D
;(bind ?self:SourceRegisters ?self:Operands)
;(bind ?self:Producers ?self:Operands))
;------------------------------------------------------------------------------
(defmessage-handler Instruction .IncrementTimeIndex ()
					(bind ?self:TimeIndex (+ 1 ?self:TimeIndex)))
;------------------------------------------------------------------------------
(defmessage-handler Instruction .DecrementTimeIndex ()
					(bind ?self:TimeIndex (- ?self:TimeIndex 1)))
;------------------------------------------------------------------------------
; Hint.clp - Contains the basic hint type plus a few ease of access sub types
;            Hints are my way of quickly creating objects that map a single
;            object to a series of other objects. A hint also contains a type
;            field that allows hints to be further constrained by another type.
;            Suprisingly enough hints are quite useful as they allow facts to
;            be created with a minimal amount of effort yet are very expressive
;            in their contents. 
;
;            They can also keep track of the number of references they have
;------------------------------------------------------------------------------
(defclass Hint (is-a List)
  (slot Type (visibility public) (default nil))
  (slot Point (default nil))
  (slot ReferenceCount (visibility public) (type NUMBER)))

;------------------------------------------------------------------------------
(defmessage-handler Hint .IncrementReferenceCount ()
					(bind ?self:ReferenceCount (+ ?self:ReferenceCount 1)))
;------------------------------------------------------------------------------
(defmessage-handler Hint .DecrementReferenceCount ()
					(bind ?self:ReferenceCount (- ?self:ReferenceCount 1)))
;------------------------------------------------------------------------------
(deffunction hints-of-type-with-point (?type ?point)
			 "Gets all hints with the specified type and point"
			 (find-all-instances ((?h Hint)) 
								 (and (eq ?type (send ?h get-Type))
									  (eq ?point (send ?h get-Point)))))
;------------------------------------------------------------------------------
(deffunction hints-of-type (?type)
			 "Returns all hints of a given type"
			 (find-all-instances ((?h Hint)) (eq ?type (send ?h get-Type))))
;------------------------------------------------------------------------------
(deffunction hintp (?instance)
			 (if (or (instance-namep ?instance) 
					 (instance-addressp ?instance)) then
			   (bind ?conv ?instance)
			   else
			   (bind ?conv (symbol-to-instance-name ?instance)))
			 (return (eq (class ?conv) Hint)))
;------------------------------------------------------------------------------
(defclass Path (is-a Hint)
  (slot ExitBlock (type SYMBOL))
  (slot Closed (type SYMBOL) (allowed-values FALSE TRUE)))
;------------------------------------------------------------------------------
(defmessage-handler Path init after ()
					(bind ?self:Type Path))
;------------------------------------------------------------------------------
(defclass Hierarchy (is-a Hint))
;------------------------------------------------------------------------------
(defmessage-handler Hierarchy init after ()
					(bind ?self:Type Hierarchy))
;------------------------------------------------------------------------------
(defclass FrequencyAnalysis (is-a Hint)
  (slot Frequency (type NUMBER) (range 0 ?VARIABLE)))
;------------------------------------------------------------------------------
(defmessage-handler FrequencyAnalysis init after ()
					(bind ?self:Type FrequencyAnalysis))
;------------------------------------------------------------------------------
(defmessage-handler FrequencyAnalysis .IncrementFrequency ()
					(bind ?self:Frequency (+ 1 ?self:Frequency)))
;------------------------------------------------------------------------------
(defclass FlatList (is-a Hint))
;------------------------------------------------------------------------------
(defmessage-handler FlatList init after ()
					(bind ?self:Type FlatList))
;------------------------------------------------------------------------------
(defclass Wavefront (is-a Hint)
  (multislot Open (visibility public))
  (multislot DeleteNodes (visibility public))
  (multislot Closed (visibility public)))

(defmessage-handler Wavefront init after ()
					(bind ?self:Type Wavefront))
;------------------------------------------------------------------------------
(defclass MultiBlockContainer (is-a Diplomat List InteropObject)
  (multislot Entrances (visibility public))
  (multislot Exits (visibility public))
  (multislot SafePaths (visibility public))
  (multislot Joins (visibility public))
  (multislot Splits (visibility public)))

(defmessage-handler MultiBlockContainer .AddBlock (?BLK)
					(bind ?self:Contents (create$ ?self:Contents ?BLK)))

(defmessage-handler MultiBlockContainer .AddBlocks ($?blks)
					(bind ?self:Contents (create$ ?self:Contents ?blks)))

(defmessage-handler MultiBlockContainer .AddEntrance (?BLK)
					(bind ?self:Entrances (create$ ?self:Entrances ?BLK)))

(defmessage-handler MultiBlockContainer .AddExit (?BLK)
					(bind ?self:Exits (create$ ?self:Exits ?BLK)))

(defmessage-handler MultiBlockContainer .AddSafePath (?BLK)
					(bind ?self:SafePaths (create$ ?self:SafePaths ?BLK)))

(defmessage-handler MultiBlockContainer .AddJoin (?BLK)
					(bind ?self:Joins (create$ ?self:Joins ?BLK)))

(defmessage-handler MultiBlockContainer .AddSplit (?BLK)
					(bind ?self:Splits (create$ ?self:Splits ?BLK)))
;------------------------------------------------------------------------------
(defclass Region (is-a MultiBlockContainer)
  (slot CanWavefrontSchedule (type SYMBOL) (allowed-values FALSE TRUE))
  (slot IsSimple (type SYMBOL) (allowed-values FALSE TRUE))
  (slot Depth (type NUMBER) (range 0 ?VARIABLE))
  (slot IsTopLevelRegion (type SYMBOL) (allowed-values FALSE TRUE)))
;------------------------------------------------------------------------------
; BasicBlock.clp - A CLIPS wrapper for the LLVM type
(defclass BasicBlock (is-a Diplomat LLVMValue List)
  (multislot UnlinkedInstructions (visibility public))
  (multislot Predecessors)
  (multislot Successors))
;(multislot ProducingBlocks)
;(multislot ConsumingBlocks))
;(multislot InvariantOperands)
;(multislot VariantOperands))

(defmessage-handler BasicBlock .IsSplitBlock () 
					"Checks to see if this block is a split block. Meaning it has more than one
					successor"
					(> (length ?self:Successors) 1))

(defmessage-handler BasicBlock .IsJoinBlock () 
					"Checks to see if this block is a join block. Meaning it has more than one
					predecessor"
					(> (length ?self:Predecessors) 1))

(defmessage-handler BasicBlock .AddPredecessor (?p)
					(bind ?self:Predecessors (create$ ?self:Predecessors ?p)))

(defmessage-handler BasicBlock .AddPredecessors ($?p)
					(bind ?self:Predecessors (create$ ?self:Predecessors ?p)))

(defmessage-handler BasicBlock .AddSuccessor (?p)
					(bind ?self:Successors (create$ ?self:Successors ?p)))

(defmessage-handler BasicBlock .AddSuccessors ($?p)
					(bind ?self:Successors (create$ ?self:Successors ?p)))
;------------------------------------------------------------------------------
(defclass Function (is-a MultiBlockContainer))
;------------------------------------------------------------------------------
(defclass PointerOperandObject (is-a thing)
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
(defclass SwitchEntry (is-a thing)
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
;------------------------------------------------------------------------------
(defclass LLVMOperator (is-a LLVMUser)
  (slot Opcode (type NUMBER) (range 0 ?VARIABLE)))
(defclass FPMathOperator (is-a LLVMOperator)
  (slot FPAccuracy (type FLOAT)))
(defclass OverflowingBinaryOperator (is-a LLVMOperator)
  (slot HasNoUnsignedWrap (type SYMBOL) (allowed-values FALSE TRUE))
  (slot HasNoSignedWrap (type SYMBOL) (allowed-values FALSE TRUE)))
(defclass PossiblyExactOperator (is-a LLVMOperator)
  (slot IsExact (type SYMBOL) (allowed-values FALSE TRUE)))
;------------------------------------------------------------------------------
(defclass Loop (is-a Region)
  (slot BackEdgeCount (type NUMBER) (range 0 ?VARIABLE))
  (multislot BackEdges)
  (multislot ExitBlocks)
  (slot HeaderBlock)
  (slot LatchBlock)
  (slot LoopPreheader)
  (slot LoopPredecessor))

(defmessage-handler Loop .AddExitBlocks ($?exits)
					(bind ?self:ExitBlocks (create$ ?self:ExitBlocks ?exits)))

(defmessage-handler Loop .AddBackEdge (?BLK)
					(bind ?self:BackEdges (create$ ?self:BackEdges ?BLK)))

;------------------------------------------------------------------------------
(defclass Replacement (is-a thing)
  (slot Target)
  (multislot With))
;------------------------------------------------------------------------------
; This is a template instead of a class and is meant to provide fix up hints
; with respect to CFG modification
;------------------------------------------------------------------------------

(deftemplate ControlModification
			 (slot ModificationType (type SYMBOL) (allowed-values Relinquish Transfer))
			 (slot From (type SYMBOL))
			 (slot To (type SYMBOL))
			 (multislot Subject (type SYMBOL)))
;------------------------------------------------------------------------------
(defclass CompensationPathVector (is-a thing)
  (multislot Failures (visibility public))
  (multislot Paths (visibility public))
  (multislot ScheduleTargets (visibility public))
  (multislot Slices (visibility public))
  (multislot Aliases (visibility public))
  (slot OriginalBlock (visibility public)))
;------------------------------------------------------------------------------
(defclass OwnershipDeterminant (is-a thing) 
  (multislot Claims)
  (multislot IndirectClaims)
  (multislot PotentialChildren)) 

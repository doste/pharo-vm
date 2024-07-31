Class {
	#name : 'VMByteCodesTest',
	#superclass : 'VMInterpreterTests',
	#instVars : [
		'contextOop',
		'context',
		'callingFrame',
		'topFrame',
		'runnerClass'
	],
	#category : 'VMMakerTests-InterpreterTests',
	#package : 'VMMakerTests',
	#tag : 'InterpreterTests'
}

{ #category : 'helper-assertions' }
VMByteCodesTest >> assert: aBlock pop: anOop intoTemporary: anIndex [
	| oldStackSize |
	oldStackSize := interpreter stackPointer.
	
	aBlock value.
	
	self assert: interpreter stackPointer equals: oldStackSize + memory wordSize.
	self assert: (interpreter temporary: anIndex in: interpreter framePointer) equals: anOop
]

{ #category : 'helper-assertions' }
VMByteCodesTest >> assert: aBlock pushed: anOop [
	| oldStackSize |
	oldStackSize := interpreter stackPointer.
	
	aBlock value.
	
	self assert: interpreter stackPointer equals: oldStackSize - memory wordSize.
	self assert: interpreter stackTop equals: anOop.
	
]

{ #category : 'helper-assertions' }
VMByteCodesTest >> assert: aBlock returned: anOop [
	| callerSP |
	callerSP := interpreter frameCallerSP: interpreter framePointer.
	
	aBlock value.
	
	self assert: interpreter stackPointer equals: callerSP - memory wordSize.
	self assert: interpreter stackTop equals: anOop.
	
]

{ #category : 'helper-assertions' }
VMByteCodesTest >> assertPopped: aBlock [
	| oldStackSize |
	oldStackSize := interpreter stackPointer.
	
	aBlock value.
	
	self assert: interpreter stackPointer equals: oldStackSize + memory wordSize.
	
]

{ #category : 'tests-send' }
VMByteCodesTest >> buildFunctionForTesting [
	| functionAddress tfExternalFunction functionExternalAddress tfFunctionDefinition libFFIType cifArrayOfArgTypes cifArgTypes cif cifExternalAddress |
	"functionAddress := self compile: [ cogit MoveR: Arg0Reg R: TempReg .cogit RetN: 0 ]." "mov rdi, rax. ret"

	functionAddress := 16rFFFF.
	
	tfExternalFunction := self newObjectWithSlots: 2. 
	functionExternalAddress := self newExternalAddress: functionAddress. 
	tfFunctionDefinition := self newObjectWithSlots: 4.
	
	"Build CIF by hand:"
	
	"Build CIF argumentTypes"
	libFFIType := self newObjectWithSlots: 5.
	memory storePointer: 0 ofObject: libFFIType withValue: (memory integerObjectOf: 16rB).   "type"
	memory storePointer: 1 ofObject: libFFIType withValue: (memory integerObjectOf: 8).		   "size"
	memory storePointer: 2 ofObject: libFFIType withValue: (memory nilObject).					"alignment"
	memory storePointer: 3 ofObject: libFFIType withValue: (memory nilObject).					"elements"
	memory storePointer: 4 ofObject: libFFIType withValue: (memory nilObject).               "libFFI"
	
	cifArrayOfArgTypes := self newArrayWithSlots: 1. 
	memory storePointer: 0 ofObject: cifArrayOfArgTypes withValue: libFFIType.
	
	cifArgTypes := self newObjectWithSlots: 2. 
	memory storePointer: 0 ofObject: cifArgTypes withValue: cifArrayOfArgTypes.
	memory storePointer: 1 ofObject: cifArgTypes withValue: (memory integerObjectOf: 8888).
	
	"The CIF itself:"
	cif := self newObjectWithSlots: 8.
	memory storePointer: 0 ofObject: cif withValue: (memory integerObjectOf: 1).       "address"
	memory storePointer: 1 ofObject: cif withValue: (memory nilObject).		 	         "libFFI"
	memory storePointer: 2 ofObject: cif withValue: (memory nilObject).						"abi"
	memory storePointer: 3 ofObject: cif withValue: (memory integerObjectOf: 1).			"nargs"
	memory storePointer: 4 ofObject: cif withValue: cifArgTypes.                    	"arg_types"
	memory storePointer: 5 ofObject: cif withValue: (memory integerObjectOf: 16rB).  	"rtype"
	memory storePointer: 6 ofObject: cif withValue: (memory nilObject).              	"bytes"
	memory storePointer: 7 ofObject: cif withValue: (memory nilObject).              	"flags"
	 
	
	cifExternalAddress := self newExternalAddress: cif.
	
	
	memory storePointer: 0 ofObject: tfExternalFunction withValue: functionExternalAddress.
	memory storePointer: 1 ofObject: tfExternalFunction withValue: tfFunctionDefinition.
	memory storePointer: 0 "HANDLE" ofObject: tfFunctionDefinition withValue: cifExternalAddress.
	
	^tfExternalFunction
]

{ #category : 'helpers-bytecode-table' }
VMByteCodesTest >> firstPushTemporaryVariableBytecode [
	"in v3 bytecode table"
	^ 16
]

{ #category : 'helpers-bytecode-table' }
VMByteCodesTest >> firstStoreAndPopTemporaryVariableBytecode [
	^ 104
]

{ #category : 'helper-interpret' }
VMByteCodesTest >> interpret: aBlock [

	aBlock value
]

{ #category : 'tests-simd' }
VMByteCodesTest >> interpretNextBytecode [

	| count |
	count := 0.
	interpreter interpretWhile: [ 
		count := count + 1.
		count = 1 ]
]

{ #category : 'tests-pushThisContext' }
VMByteCodesTest >> interpretWithFrame: aBlock [

	callingFrame := stackBuilder addNewFrame method:
		                methodBuilder newMethod buildMethod.
	topFrame := stackBuilder addNewFrame method:
		            methodBuilder newMethod buildMethod.
	stackBuilder buildStack.

	self interpret: aBlock
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> pushTempTest: index [
	
	stackBuilder addNewFrame tempAt: index put: (memory integerObjectOf: 42).
	stackBuilder buildStack.
	interpreter currentBytecode: (self pushTemporaryVariableBytecodeAt: index).
	
	"first we push something, so there is something to duplicate"
	self
		assert: [ self interpret: [ interpreter pushTemporaryVariableBytecode ] ]
		pushed: (memory integerObjectOf: 42).

]

{ #category : 'helpers-bytecode-table' }
VMByteCodesTest >> pushTemporaryVariableBytecodeAt: offset [
	^ self firstPushTemporaryVariableBytecode + offset.
	
]

{ #category : 'tests-pushThisContext' }
VMByteCodesTest >> pushThisContextTopFrame [

	self interpretWithFrame: [ interpreter pushActiveContextBytecode ].

	contextOop := interpreter stackTop.
	context := VMContext
		newOnContext: contextOop
		withInterpreter: interpreter
]

{ #category : 'running' }
VMByteCodesTest >> setUp [

	| classFloat classArray |
	super setUp.
	self installFloat64RegisterClass.
	self setUpContextClass.
	classArray := self setArrayClassIntoClassTable.
	self setMessageClassIntoClassTable.
	
	runnerClass := self
		newClassInOldSpaceWithSlots: 0
		instSpec: Object instSpec.
	memory ensureBehaviorHash: runnerClass.

	interpreter libFFI: LibFFI new.
	interpreter libFFI interpreter: interpreter.

	memory classExternalAddress: (self
			 newClassInOldSpaceWithSlots: 0
			 instSpec: (memory byteFormatForNumBytes: 0)).
	memory classArray: classArray.
	memory classByteArray: (self
			 newClassInOldSpaceWithSlots: 0
			 instSpec: (memory byteFormatForNumBytes: 0)).

	classFloat := self
		              newClassInOldSpaceWithSlots: 0
		              instSpec: memory firstLongFormat.
	memory setHashBitsOf: classFloat to: ClassFloatCompactIndex.
	memory
		storePointer: ClassFloatCompactIndex
		ofObject: memory classTableFirstPage
		withValue: classFloat.

	self createLargeIntegerClasses
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> storeAndPopTemporaryIntoTempTest: index [
	
	stackBuilder addNewFrame
		tempAt: index put: (memory nilObject) ;
		stack: { memory integerObjectOf: 42 } .
	stackBuilder buildStack.
	
	interpreter currentBytecode: (self storeAndPopTemporaryVariableBytecodeAt: index).
	
	"first we push something, so there is something to duplicate"
	self assert: [ self interpret: [ interpreter storeAndPopTemporaryVariableBytecode ] ]
		pop: (memory integerObjectOf: 42)
		intoTemporary: index
]

{ #category : 'helpers-bytecode-table' }
VMByteCodesTest >> storeAndPopTemporaryVariableBytecodeAt: anInteger [ 
	^ self firstStoreAndPopTemporaryVariableBytecode + anInteger
]

{ #category : 'tests-pushThisContext' }
VMByteCodesTest >> testAccessingSenderOfContextShouldReturnContextOfSender [
	| oldMaybeSenderContext newMaybeSenderContext |
	self interpretWithFrame: [ interpreter pushActiveContextBytecode. ].
	oldMaybeSenderContext := interpreter instVar: SenderIndex ofContext: interpreter stackTop.
	interpreter pushActiveContextBytecode.
	newMaybeSenderContext := interpreter instVar: SenderIndex ofContext: interpreter stackTop.
	self assert: oldMaybeSenderContext equals: newMaybeSenderContext
]

{ #category : 'tests-simd' }
VMByteCodesTest >> testAddVectorBytecode [
	| index v0 v1 result firstTerm size |
	
	index := 0.

	firstTerm := 1.0 to: 2.0.
	size := firstTerm size.

	v0 := self new64BitIndexableFromArray: firstTerm.
	v1 := self new64BitIndexableFromArray: (firstTerm collect: [:i | i + size]).
	result := self new64BitIndexableOfSize: size. 
		
	stackBuilder addNewFrame
		stack: { v0. v1 } .
	stackBuilder buildStack.
	
	self interpret: [ interpreter addFloat64VectorBytecode ].
	
	result := interpreter stackTop.
	
	self deny: result equals: memory nilObject.
	self assert: (memory fetchFloat64: 0 ofObject: result) equals: 4.0.
	self assert: (memory fetchFloat64: 1 ofObject: result) equals: 6.0.
	
]

{ #category : 'tests-simd' }
VMByteCodesTest >> testArraySumUsingVectorBytecode [
	| cm x y result simulatedMethod z |

	x := self new64BitIndexableFromArray: #(1.0 2.0).
	y := self new64BitIndexableFromArray: #(10.0 20.0).
	z := self new64BitIndexableOfSize: 2.
	
	cm := IRBuilder buildMethod: [ :builder |
		builder
				numArgs: 3; 		
				addTemps: { #firstVector. #secondVector. #thirdVector };
				pushLiteral: 0;
				pushTemp: #firstVector;
				pushFloat64ArrayToRegister;
				pushLiteral: 0;
				pushTemp: #secondVector;
				pushFloat64ArrayToRegister;
				addFloat64Vector;
				pushLiteral: 0;
				pushTemp: #thirdVector;
				storeFloat64RegisterIntoArray;
				returnTop
		 ].
	
	simulatedMethod := methodBuilder fillFromPharoMethod: cm;
		          buildMethod.
	
	stackBuilder addNewFrame
		method: simulatedMethod;
		temps: { x. y. z.}.
	stackBuilder buildStack.
	
	interpreter interpretUntilReturn.
	
	result := interpreter stackTop.

	self assert: (memory fetchFloat64: 0 ofObject: result) equals: 11.0.
	self assert: (memory fetchFloat64: 1 ofObject: result) equals: 22.0.
	
]

{ #category : 'tests-fficall' }
VMByteCodesTest >> testBytecodeFFICall8BitNegativeInteger [

	| aMethod aMethodToActivate receiver receiverClass aMethodDictionary arg1 tfExternalFunction |
	
	
	tfExternalFunction := self 
		createExternalFunctionFor:  [ :anArgument | anArgument ] 
		withArgumentTypes: { interpreter libFFI sint8 } 
		withReturnType: interpreter libFFI sint8.

	methodBuilder newMethod literals: { tfExternalFunction }.
	aMethod := methodBuilder buildMethod.
	aMethodToActivate := methodBuilder newMethod
		                     numberOfArguments: 1;
		                     buildMethod.
	aMethod := methodBuilder newMethod
		bytecodes:
			#[ 
				16rE6 16r0						
						];
		numberOfArguments: 2;
		literals: { 
			tfExternalFunction
		};
		isPrimitive: false;
		buildMethod.
		
	receiver := memory integerObjectOf: 41.
	receiverClass := self setSmallIntegerClassIntoClassTable.
	self setUpMethodDictionaryIn: receiverClass.
	aMethodDictionary := memory
		                     fetchPointer: MethodDictionaryIndex
		                     ofObject: receiverClass.

	self
		installSelector: tfExternalFunction
		method: aMethod
		inMethodDictionary: aMethodDictionary.
	arg1 := memory integerObjectOf: -2.
	stackBuilder addNewFrame
		method: aMethod;
		stack: { 
				receiver.
				arg1.
	 }.
	stackBuilder buildStack.

	interpreter methodDictLinearSearchLimit: 3.
	interpreter setBreakSelector: nil.
	interpreter method: aMethod.

	self interpretNextBytecode.
	
	"Before calling to the bytecode we had to push the receiver and all the arguments.
	We should assert that the bytecode popped the 2 arguments and pushed the result.
	Here we assert that the result was pushed:"
	self assert: interpreter stackTop equals: (memory integerObjectOf: -2)

]

{ #category : 'tests-fficall' }
VMByteCodesTest >> testBytecodeFFICallAddTwoBigIntegers [

	| aMethod receiver receiverClass aMethodDictionary arg1 arg2 tfExternalFunction selectorOop simulatedInvokeFunctionWithArguments simulatedClassOfRunner simulatedRunner |
	"We create a simulated external function to call"
	tfExternalFunction := self
		                      createExternalFunctionFor: [ :anArgument :anotherArgument |
			                      anArgument + anotherArgument ]
		                      withArgumentTypes: {
				                      interpreter libFFI sint64.
				                      interpreter libFFI sint64 }
		                      withReturnType: interpreter libFFI sint64.

	simulatedInvokeFunctionWithArguments := methodBuilder newMethod
		                                        numberOfArguments: 2;
		                                        buildMethod.
	stackBuilder addNewFrame method: simulatedInvokeFunctionWithArguments.
	stackBuilder buildStack.

	simulatedClassOfRunner := self
		                          installClassIntoClassTableWithInstSpec: 1
		                          instSize: 0.
	simulatedRunner := memory instantiateClass: simulatedClassOfRunner.
	self setUpMethodDictionaryIn: simulatedClassOfRunner.

	"The method that we want to end up calling is all simulated, so it doesn't really matter its selector. Only that they are associated."
	selectorOop := memory integerObjectOf: 42.
	memory splObj: SelectorInvokeFunctionWithArguments put: selectorOop.
	self
		installSelector: selectorOop
		method: simulatedInvokeFunctionWithArguments
		inMethodDictionary: (memory
				 fetchPointer: MethodDictionaryIndex
				 ofObject: simulatedClassOfRunner).


	aMethod := methodBuilder newMethod
		           bytecodes: #[ 16rE6 16r1 ];
		           numberOfArguments: 2;
		           literals: {
				           simulatedRunner.
				           tfExternalFunction };
		           isPrimitive: false;
		           buildMethod.
	"byecodeFFICall n=1"

	"Here it doesn't matter the receiver of the method. We are only interested in testing the method, more specifically its bytecodes."
	receiver := memory integerObjectOf: 41.
	receiverClass := self setSmallIntegerClassIntoClassTable.
	self setUpMethodDictionaryIn: receiverClass.
	aMethodDictionary := memory
		                     fetchPointer: MethodDictionaryIndex
		                     ofObject: receiverClass.

	arg1 := memory integerObjectOf: memory maxSmallInteger.
	arg2 := memory integerObjectOf: memory maxSmallInteger.

	stackBuilder addNewFrame
		method: aMethod;
		stack: {
				receiver.
				arg1.
				arg2 }.
	stackBuilder buildStack.

	interpreter methodDictLinearSearchLimit: 3.
	interpreter setBreakSelector: nil.
	interpreter method: aMethod.

	self interpretNextBytecode.

	self
		assert: (memory signed64BitValueOf: interpreter stackTop)
		equals: memory maxSmallInteger + memory maxSmallInteger
]

{ #category : 'tests-fficall' }
VMByteCodesTest >> testBytecodeFFICallAddTwoNumbersCorrectly [

	| aMethod aMethodToActivate receiver receiverClass aMethodDictionary arg1 arg2 tfExternalFunction isFunctionCalled |
	isFunctionCalled := false.

	tfExternalFunction := self
		                      createExternalFunctionFor: [
			                      :anArgument
			                      :anotherArgument |
			                      isFunctionCalled := true.
			                      anArgument + anotherArgument ]
		                      withArgumentTypes: {
				                      interpreter libFFI uint64.
				                      interpreter libFFI uint64 }
		                      withReturnType: interpreter libFFI uint64.

	methodBuilder newMethod literals: { tfExternalFunction }.
	aMethod := methodBuilder buildMethod.
	aMethodToActivate := methodBuilder newMethod
		                     numberOfArguments: 2;
		                     buildMethod.
	aMethod := methodBuilder newMethod
		           bytecodes: #[ 16rE6 16r0 ];
		           numberOfArguments: 2;
		           literals: { tfExternalFunction };
		           isPrimitive: false;
		           buildMethod.
	"byecodeFFICall n=0"

	receiver := memory integerObjectOf: 41.
	receiverClass := self setSmallIntegerClassIntoClassTable.
	self setUpMethodDictionaryIn: receiverClass.
	aMethodDictionary := memory
		                     fetchPointer: MethodDictionaryIndex
		                     ofObject: receiverClass.

	self
		installSelector: tfExternalFunction
		method: aMethod
		inMethodDictionary: aMethodDictionary.
	arg1 := memory integerObjectOf: 111.
	arg2 := memory integerObjectOf: 222.
	stackBuilder addNewFrame
		method: aMethod;
		stack: {
				receiver.
				arg1.
				arg2 }.
	stackBuilder buildStack.

	interpreter methodDictLinearSearchLimit: 3.
	interpreter setBreakSelector: nil.
	interpreter method: aMethod.

	self interpretNextBytecode.

	self assert: isFunctionCalled.

	"Before calling to the bytecode we had to push the receiver and all the arguments.
	We should assert that the bytecode popped the 2 arguments and pushed the result.
	Here we assert that the result was pushed:"
	self
		assert: (memory integerValueOf: interpreter stackTop)
		equals: 111 + 222.

	"And here we assert that the 2 arguments were popped (the receiver was pushed before the args)"
	self assert: (interpreter stackValue: 1) equals: receiver
]

{ #category : 'tests-fficall' }
VMByteCodesTest >> testBytecodeFFICallFailWithBadDoubleArg [

	| callerFFIMethod ffiCallArgument aMethodDictionary runner aMethodToActivate tfExternalFunction expectedReceiver expectedTfExternalFunction expectedArgumentArray |

	"An invalid FFI call will send the message #invalidFFICall to the current context.
	Thus, install a method with that selector in the Context class"
	runner := memory instantiateClass: runnerClass.
	aMethodDictionary := self setUpMethodDictionaryIn: runnerClass.
	aMethodToActivate := methodBuilder newMethod
		                     numberOfArguments: 2;
		                     buildMethod.
	memory
		splObj: SelectorInvokeFunctionWithArguments
		put: (memory integerObjectOf: 17).
	self
		installSelector: (memory splObj: SelectorInvokeFunctionWithArguments)
		method: aMethodToActivate
		inMethodDictionary: aMethodDictionary.

	tfExternalFunction := self
		                      createExternalFunctionFor: [ :anArgument |
		                      anArgument ]
		                      withArgumentTypes:
		                      { interpreter libFFI double }
		                      withReturnType: interpreter libFFI void.


	callerFFIMethod := methodBuilder newMethod
		           bytecodes: #[ 16rE6 16r1 ];
		           numberOfArguments: 2;
		           literals: {
				           runner.
				           tfExternalFunction };
		           isPrimitive: false;
		           buildMethod.

	ffiCallArgument := memory integerObjectOf: 41.
	stackBuilder addNewFrame
		method: callerFFIMethod;
		stack: { ffiCallArgument }.
	stackBuilder buildStack.

	interpreter methodDictLinearSearchLimit: 3.
	interpreter setBreakSelector: nil.
	interpreter method: callerFFIMethod.

	self interpretNextBytecode.

	expectedReceiver := interpreter frameReceiver: (interpreter framePointer).
	expectedTfExternalFunction := interpreter itemporary: 0 in: (interpreter framePointer).
	expectedArgumentArray := interpreter itemporary: 1 in: (interpreter framePointer).
	
	self assert: expectedReceiver equals: runner.
	self assert: expectedTfExternalFunction equals: tfExternalFunction.
	
	self assert: (memory fetchClassOf: expectedArgumentArray) equals: memory classArray.
	self assert: (memory slotSizeOf: expectedArgumentArray) equals: 1.
	self assert: (memory fetchPointer: 0 ofObject: expectedArgumentArray) equals: ffiCallArgument.
]

{ #category : 'tests-fficall' }
VMByteCodesTest >> testBytecodeFFICallFailWithBadFunction [

	| aMethod receiver contextClass aMethodDictionary invalidExternalFunction simulatedClassOfRunner simulatedRunner aMethodToActivate |
	simulatedClassOfRunner := self
		                          installClassIntoClassTableWithInstSpec: 1
		                          instSize: 0.
	simulatedRunner := memory instantiateClass: simulatedClassOfRunner.

	"An invalid FFI call will send the message #invalidFFICall to the current context.
	Thus, install a method with that selector in the Context class"
	contextClass := self contextClass.
	aMethodDictionary := self setUpMethodDictionaryIn: contextClass.
	aMethodToActivate := methodBuilder newMethod
		                     numberOfArguments: 0;
		                     buildMethod.
	memory
		splObj: SelectorInvalidFFICall
		put: (memory integerObjectOf: 17).
	self
		installSelector: (memory splObj: SelectorInvalidFFICall)
		method: aMethodToActivate
		inMethodDictionary: aMethodDictionary.

	invalidExternalFunction := memory trueObject. "Bad function!"
	aMethod := methodBuilder newMethod
		           bytecodes: #[ 16rE6 16r1 ];
		           numberOfArguments: 2;
		           literals: {
				           simulatedRunner.
				           invalidExternalFunction };
		           isPrimitive: false;
		           buildMethod.

	receiver := memory integerObjectOf: 41.
	stackBuilder addNewFrame
		method: aMethod;
		stack: { receiver }.
	stackBuilder buildStack.

	interpreter methodDictLinearSearchLimit: 3.
	interpreter setBreakSelector: nil.
	interpreter method: aMethod.

	self interpretNextBytecode.

	self
		assert: (interpreter frameReceiver: interpreter framePointer)
		equals: (interpreter frameContext:
				 (interpreter frameCallerFP: interpreter framePointer)).
	self
		assert: (interpreter frameMethodObject: interpreter framePointer)
		equals: aMethodToActivate
]

{ #category : 'tests-fficall' }
VMByteCodesTest >> testBytecodeFFICallFailWithBadInt8Arg [

	| callerFFIMethod ffiCallArgument aMethodDictionary runner aMethodToActivate tfExternalFunction expectedReceiver expectedTfExternalFunction expectedArgumentArray |

	"An invalid FFI call will send the message #invalidFFICall to the current context.
	Thus, install a method with that selector in the Context class"
	runner := memory instantiateClass: runnerClass.
	aMethodDictionary := self setUpMethodDictionaryIn: runnerClass.
	aMethodToActivate := methodBuilder newMethod
		                     numberOfArguments: 2;
		                     buildMethod.
	memory
		splObj: SelectorInvokeFunctionWithArguments
		put: (memory integerObjectOf: 17).
	self
		installSelector: (memory splObj: SelectorInvokeFunctionWithArguments)
		method: aMethodToActivate
		inMethodDictionary: aMethodDictionary.

	tfExternalFunction := self
		                      createExternalFunctionFor: [ :anArgument |
		                      anArgument ]
		                      withArgumentTypes:
		                      { interpreter libFFI sint8 }
		                      withReturnType: interpreter libFFI void.


	callerFFIMethod := methodBuilder newMethod
		           bytecodes: #[ 16rE6 16r1 ];
		           numberOfArguments: 2;
		           literals: {
				           runner.
				           tfExternalFunction };
		           isPrimitive: false;
		           buildMethod.

	ffiCallArgument := memory trueObject.
	stackBuilder addNewFrame
		method: callerFFIMethod;
		stack: { ffiCallArgument }.
	stackBuilder buildStack.

	interpreter methodDictLinearSearchLimit: 3.
	interpreter setBreakSelector: nil.
	interpreter method: callerFFIMethod.

	self interpretNextBytecode.

	expectedReceiver := interpreter frameReceiver: (interpreter framePointer).
	expectedTfExternalFunction := interpreter itemporary: 0 in: (interpreter framePointer).
	expectedArgumentArray := interpreter itemporary: 1 in: (interpreter framePointer).
	
	self assert: expectedReceiver equals: runner.
	self assert: expectedTfExternalFunction equals: tfExternalFunction.
	
	self assert: (memory fetchClassOf: expectedArgumentArray) equals: memory classArray.
	self assert: (memory slotSizeOf: expectedArgumentArray) equals: 1.
	self assert: (memory fetchPointer: 0 ofObject: expectedArgumentArray) equals: ffiCallArgument.
]

{ #category : 'tests-fficall' }
VMByteCodesTest >> testBytecodeFFICallWithNonConmutativeOp [

	| aMethod aMethodToActivate receiver receiverClass aMethodDictionary arg1 arg2 tfExternalFunction isFunctionCalled |
	
	isFunctionCalled := false.
	
	tfExternalFunction := self 
		createExternalFunctionFor:  [ :anArgument :anotherArgument | isFunctionCalled := true . anArgument - anotherArgument ] 
		withArgumentTypes: { interpreter libFFI uint64. interpreter libFFI uint64} 
		withReturnType: interpreter libFFI uint64.

	methodBuilder newMethod literals: { tfExternalFunction }.
	aMethod := methodBuilder buildMethod.
	aMethodToActivate := methodBuilder newMethod
		                     numberOfArguments: 2;
		                     buildMethod.

	aMethod := methodBuilder newMethod
		bytecodes:
			#[ 
				"byecodeFFICall n=0" 16rE6 16r0						
						];
		numberOfArguments: 2;
		literals: { 
			tfExternalFunction
		};
		isPrimitive: false;
		buildMethod.
		
	receiver := memory integerObjectOf: 41.
	receiverClass := self setSmallIntegerClassIntoClassTable.
	self setUpMethodDictionaryIn: receiverClass.
	aMethodDictionary := memory
		                     fetchPointer: MethodDictionaryIndex
		                     ofObject: receiverClass.

	self
		installSelector: tfExternalFunction
		method: aMethod
		inMethodDictionary: aMethodDictionary.
	arg1 := memory integerObjectOf: 90.
	arg2 := memory integerObjectOf: 10.
	stackBuilder addNewFrame
		method: aMethod;
		stack: { 
				receiver.
				arg1.
				arg2 }.
	stackBuilder buildStack.

	interpreter methodDictLinearSearchLimit: 3.
	interpreter setBreakSelector: nil.
	interpreter method: aMethod.

	self interpretNextBytecode.

	self assert: isFunctionCalled.
	
	self assert: (memory integerValueOf:(interpreter stackTop))  equals: 90 - 10.
]

{ #category : 'tests-fficall' }
VMByteCodesTest >> testBytecodeFFICallWithNonConmutativeOpSignedInt [

	| aMethod aMethodToActivate receiver receiverClass aMethodDictionary arg1 arg2 tfExternalFunction isFunctionCalled |
	
	isFunctionCalled := false.
	
	tfExternalFunction := self 
		createExternalFunctionFor:  [ :anArgument :anotherArgument | isFunctionCalled := true. anArgument - anotherArgument ] 
		withArgumentTypes: { interpreter libFFI sint32. interpreter libFFI sint32} 
		withReturnType: interpreter libFFI sint32.

	methodBuilder newMethod literals: { tfExternalFunction }.
	aMethod := methodBuilder buildMethod.
	aMethodToActivate := methodBuilder newMethod
		                     numberOfArguments: 2;
		                     buildMethod.

	aMethod := methodBuilder newMethod
		bytecodes:
			#[ 
				"byecodeFFICall n=0" 16rE6 16r0						
						];
		numberOfArguments: 2;
		literals: { 
			tfExternalFunction
		};
		isPrimitive: false;
		buildMethod.
		
	receiver := memory integerObjectOf: 41.
	receiverClass := self setSmallIntegerClassIntoClassTable.
	self setUpMethodDictionaryIn: receiverClass.
	aMethodDictionary := memory
		                     fetchPointer: MethodDictionaryIndex
		                     ofObject: receiverClass.

	self
		installSelector: tfExternalFunction
		method: aMethod
		inMethodDictionary: aMethodDictionary.
	arg1 := memory integerObjectOf: 10.
	arg2 := memory integerObjectOf: 90.
	stackBuilder addNewFrame
		method: aMethod;
		stack: { 
				receiver.
				arg1.
				arg2 }.
	stackBuilder buildStack.

	interpreter methodDictLinearSearchLimit: 3.
	interpreter setBreakSelector: nil.
	interpreter method: aMethod.

	self interpretNextBytecode.

	self assert: isFunctionCalled.
	
	self assert: (memory integerValueOf:(interpreter stackTop))  equals: 10 - 90.
]

{ #category : 'tests-fficall' }
VMByteCodesTest >> testBytecodePopIntoReceiverWithReadOnlySendsAttemptToAssignMethod [

	| class object objectToPutInSlot attemptToAssignMethod attemptToAssignSelector aMethodDictionary |
	class := self
		         newClassInOldSpaceWithSlots: 0
		         instSpec: memory arrayFormat.
	object := memory instantiateClass: class indexableSize: 1.
	attemptToAssignSelector := memory integerObjectOf: 2.
	attemptToAssignMethod := methodBuilder newMethod
		                         numberOfArguments: 2;
		                         buildMethod.
	self setUpMethodDictionaryIn: class.
	aMethodDictionary := memory
		                     fetchPointer: MethodDictionaryIndex
		                     ofObject: class.
	self
		installSelector: attemptToAssignSelector
		method: attemptToAssignMethod
		inMethodDictionary: aMethodDictionary.

	memory splObj: SelectorAttemptToAssign put: attemptToAssignSelector.

	memory setIsImmutableOf: object to: true.

	objectToPutInSlot := memory instantiateClass: class indexableSize: 1.

	stackBuilder addNewFrame
		receiver: object;
		stack: { objectToPutInSlot }.
	stackBuilder buildStack.

	interpreter methodDictLinearSearchLimit: 3.
	interpreter setBreakSelector: nil.
	interpreter currentBytecode: 200.

	self interpret: [ interpreter storeAndPopReceiverVariableBytecode ].

	topFrame := VMStackFrame
		            newFramePointer: interpreter framePointer
		            withInterpreter: interpreter.
	self assert: topFrame method equals: attemptToAssignMethod
]

{ #category : 'tests-simd' }
VMByteCodesTest >> testCallMappedInlinedPrimitiveBytecode [

	| v0 v1 result method |
	v0 := self new64BitIndexableOfSize: 2.
	v1 := self new64BitIndexableOfSize: 2.
	memory storeFloat64: 0 ofObject: v0 withValue: 1.0.
	memory storeFloat64: 1 ofObject: v0 withValue: 2.0.
	memory storeFloat64: 0 ofObject: v1 withValue: 3.0.
	memory storeFloat64: 1 ofObject: v1 withValue: 4.0.
	
	method := methodBuilder newMethod
		          bytecodes: #[ "callMappedInlinedPrimitiveBytecode" 236 "addVectorBytecode" 0 ];
		          buildMethod.
	stackBuilder addNewFrame
		method: method;
		stack: { v0. v1 }.
	stackBuilder buildStack.
	
	self interpretNextBytecode.
	
	result := interpreter stackTop.
	self deny: result equals: memory nilObject.
	self assert: (memory fetchFloat64: 0 ofObject: result) equals: 4.0.
	self assert: (memory fetchFloat64: 1 ofObject: result) equals: 6.0
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testDuplicateStackTop [

	stackBuilder addNewFrame ; buildStack.
	
	"first we push something, so there is something to duplicate"
	self
		assert: [ self interpret: [ interpreter pushConstantOneBytecode ] ]
		pushed: (memory integerObjectOf: 1).

	"then we duplicate it"
	self
		assert: [ self interpret: [ interpreter duplicateTopBytecode  ] ]
		pushed: (memory integerObjectOf: 1).
	
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPopStackTopBytecode [

	stackBuilder addNewFrame ; buildStack.
	
	"first we push something"
	self
		assert: [ self interpret: [ interpreter pushConstantOneBytecode ] ]
		pushed: (memory integerObjectOf: 1).
	
	"then we pop it"
	self
		assertPopped: [ self interpret: [ interpreter popStackBytecode ] ]
	
]

{ #category : 'tests-simd' }
VMByteCodesTest >> testPushArrayToRegisterBytecode [
	| array index result |

	array := self new64BitIndexableOfSize: 4.
	memory storeFloat64: 0 ofObject: array withValue: 1.0. 
	memory storeFloat64: 1 ofObject: array withValue: 2.0.
	memory storeFloat64: 2 ofObject: array withValue: 3.0.
	memory storeFloat64: 3 ofObject: array withValue: 4.0. 
	
	index := memory integerObjectOf: 2.
	
	stackBuilder addNewFrame
		stack: { index. array } .
	stackBuilder buildStack.
	
	self interpret: [ interpreter pushFloat64ArrayToRegisterBytecode ].
	
	result := interpreter stackTop.
	
	self assert: (memory fetchFloat64: 0 ofObject: result) equals: 3.0.
	self assert: (memory fetchFloat64: 1 ofObject: result) equals: 4.0.
	
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushConstantFalseBytecode [
	stackBuilder addNewFrame ; buildStack.
	self
		assert: [ self interpret: [ interpreter pushConstantFalseBytecode ] ]
		pushed: memory falseObject
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushConstantMinusOneBytecode [
	stackBuilder addNewFrame ; buildStack.
	self
		assert: [ self interpret: [ interpreter pushConstantMinusOneBytecode ] ]
		pushed: (memory integerObjectOf: -1)
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushConstantNilBytecode [
	stackBuilder addNewFrame ; buildStack.
	self
		assert: [ self interpret: [ interpreter pushConstantNilBytecode ] ]
		pushed: memory nilObject
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushConstantOneBytecode [
	stackBuilder addNewFrame ; buildStack.
	self
		assert: [ self interpret: [ interpreter pushConstantOneBytecode ] ]
		pushed: (memory integerObjectOf: 1)
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushConstantReceiverBytecode [
	| intReceiver |
	intReceiver := memory integerObjectOf: 42.
	
	stackBuilder addNewFrame receiver: intReceiver.
	stackBuilder buildStack.

	self
		assert: [ self interpret: [ interpreter pushReceiverBytecode ] ]
		pushed: intReceiver
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushConstantTrueBytecode [
	stackBuilder addNewFrame ; buildStack.
	self
		assert: [ self interpret: [ interpreter pushConstantTrueBytecode ] ]
		pushed: memory trueObject
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushConstantTwoBytecode [
	stackBuilder addNewFrame ; buildStack.
	self
		assert: [ self interpret: [ interpreter pushConstantTwoBytecode ] ]
		pushed: (memory integerObjectOf: 2)
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushConstantZeroBytecode [
	stackBuilder addNewFrame ; buildStack.
	self
		assert: [ self interpret: [ interpreter pushConstantZeroBytecode ] ]
		pushed: (memory integerObjectOf: 0)
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushTemp0 [
	self pushTempTest: 0
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushTemp1 [
	self pushTempTest: 1
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushTemp10 [
	self pushTempTest: 10
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushTemp11 [
	self pushTempTest: 11
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushTemp2 [
	self pushTempTest: 2
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushTemp3 [
	self pushTempTest: 3
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushTemp4 [
	self pushTempTest: 4
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushTemp5 [
	self pushTempTest: 5
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushTemp6 [
	self pushTempTest: 6
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushTemp7 [
	self pushTempTest: 7
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushTemp8 [
	self pushTempTest: 8
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testPushTemp9 [
	self pushTempTest: 9
]

{ #category : 'tests-pushThisContext' }
VMByteCodesTest >> testPushThisContextIsContext [

	self pushThisContextTopFrame.
	self assert: (memory isContext: interpreter stackTop).
]

{ #category : 'tests-pushThisContext' }
VMByteCodesTest >> testPushThisContextPushesValidInstructionPointer [

	self pushThisContextTopFrame.
	self assert: (interpreter objectMemory isIntegerObject: context instructionPointer).
	self
		assert: (interpreter withoutSmallIntegerTags: context instructionPointer)
		equals: (interpreter frameCallerFP: interpreter framePointer)
]

{ #category : 'tests-pushThisContext' }
VMByteCodesTest >> testPushThisContextPushesValidPointerToTheFramePointer [
	
	self pushThisContextTopFrame.
	self
		assert: (interpreter objectMemory isIntegerObject: context sender).
	self
		assert: (interpreter withoutSmallIntegerTags: context sender)
		equals: interpreter framePointer
]

{ #category : 'tests-pushThisContext' }
VMByteCodesTest >> testPushThisContextPushesValidReceiver [

	self pushThisContextTopFrame.
	self assert: topFrame receiver equals: context receiver
]

{ #category : 'tests-pushThisContext' }
VMByteCodesTest >> testPushThisContextSetContextToFrame [

	self pushThisContextTopFrame.
	self assert: (interpreter frameContext: interpreter framePointer) equals: interpreter stackTop.
]

{ #category : 'tests-pushThisContext' }
VMByteCodesTest >> testPushThisContextSetFlagContextToFrame [

	self pushThisContextTopFrame.
	self assert: (interpreter frameHasContext: interpreter framePointer).
]

{ #category : 'tests-pushThisContext' }
VMByteCodesTest >> testPushThisContextTwiceMarriesOnce [
	| previousTop newTop |
	self interpretWithFrame: [ 
		interpreter pushActiveContextBytecode.
		previousTop := interpreter stackTop.
		interpreter pushActiveContextBytecode.
		newTop := interpreter stackTop.
		 ].
	self assert: newTop equals: previousTop.
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testReturnFalse [

	"We need to return to a method.
	So the method of the first stack should have a compiled method in the method field of the stack.
	using memory trueObject simulates that behavior."

	stackBuilder addNewFrame method: methodBuilder newMethod buildMethod.
	stackBuilder addNewFrame.
	stackBuilder buildStack.

	self
		assert: [ self interpret: [ interpreter returnFalse ] ]
		returned: memory falseObject
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testReturnTrue [

	"We need to return to a method.
	So the method of the first stack should have a compiled method in the method field of the stack.
	using memory trueObject simulates that behavior."

	stackBuilder addNewFrame method: methodBuilder newMethod buildMethod.
	stackBuilder addNewFrame.
	stackBuilder buildStack.

	self
		assert: [ self interpret: [ interpreter returnTrue ] ]
		returned: memory trueObject
]

{ #category : 'tests-pushThisContext' }
VMByteCodesTest >> testReturnsMarriedFrameWidowsContext [
	| topFrameContext |
	self interpretWithFrame: [ 
		interpreter pushActiveContextBytecode.
		interpreter returnTopFromMethod.
		].
	topFrameContext := interpreter stackTop.
	"The interpreter does not update the pages, they are updated on demand. 
	Before checking a frame isWindowed we have to synchronize the interpreter variables with the stackPages"
	interpreter writeBackHeadFramePointers.
	self assert: (interpreter isWidowedContext: topFrameContext)
]

{ #category : 'tests-send' }
VMByteCodesTest >> testSendMessageWithTwoArgumentsMakeAFrame [

	| selectorOop aMethod aMethodToActivate receiver receiverClass aMethodDictionary arg1 arg2 |
	selectorOop := memory integerObjectOf: 42.
	methodBuilder newMethod literals: { selectorOop }.
	aMethod := methodBuilder buildMethod.

	aMethodToActivate := methodBuilder newMethod
		                     numberOfArguments: 2;
		                     buildMethod.
	receiver := memory integerObjectOf: 41.
	receiverClass := self setSmallIntegerClassIntoClassTable.
	self setUpMethodDictionaryIn: receiverClass.
	aMethodDictionary := memory
		                     fetchPointer: MethodDictionaryIndex
		                     ofObject: receiverClass.

	self
		installSelector: selectorOop
		method: aMethodToActivate
		inMethodDictionary: aMethodDictionary.
	arg1 := memory integerObjectOf: 1.
	arg2 := memory integerObjectOf: 2.
	stackBuilder addNewFrame
		method: aMethod;
		stack: { 
				receiver.
				arg1.
				arg2 }.
	stackBuilder buildStack.

	interpreter methodDictLinearSearchLimit: 3.
	interpreter setBreakSelector: nil.
	interpreter method: aMethod.
	interpreter currentBytecode: 240.

	self interpret: [ interpreter sendLiteralSelector2ArgsBytecode ].


	self
		assert: (VMStackFrame
				 newFramePointer: interpreter framePointer
				 withInterpreter: interpreter) receiver
		equals: receiver.
	self assert: interpreter stackTop equals: receiver
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testStoreAndPopTemporary0 [
	self storeAndPopTemporaryIntoTempTest: 0
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testStoreAndPopTemporary1 [
	self storeAndPopTemporaryIntoTempTest: 1
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testStoreAndPopTemporary2 [
	self storeAndPopTemporaryIntoTempTest: 2
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testStoreAndPopTemporary3 [
	self storeAndPopTemporaryIntoTempTest: 3
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testStoreAndPopTemporary4 [
	self storeAndPopTemporaryIntoTempTest: 4
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testStoreAndPopTemporary5 [
	self storeAndPopTemporaryIntoTempTest: 5
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testStoreAndPopTemporary6 [
	self storeAndPopTemporaryIntoTempTest: 6
]

{ #category : 'tests-push-simple' }
VMByteCodesTest >> testStoreAndPopTemporary7 [
	self storeAndPopTemporaryIntoTempTest: 7
]

{ #category : 'tests-simd' }
VMByteCodesTest >> testStoreRegisterIntoArrayBytecode [
	| register index array result |
	
	array := self new64BitIndexableOfSize: 4.
	memory storeFloat64: 0 ofObject: array withValue: 1.0. 
	memory storeFloat64: 1 ofObject: array withValue: 2.0.
	memory storeFloat64: 2 ofObject: array withValue: 3.0.
	memory storeFloat64: 3 ofObject: array withValue: 4.0. 
	
	register := self new64BitIndexableOfSize: 2.
	memory storeFloat64: 0 ofObject: register withValue: 5.0. 
	memory storeFloat64: 1 ofObject: register withValue: 6.0.
	
	index := memory integerObjectOf: 2.
	
	stackBuilder addNewFrame
		stack: { register. index. array }.
	stackBuilder buildStack.
	
	self interpret: [ interpreter storeFloat64RegisterIntoArrayBytecode ].
	
	result := interpreter stackTop.
	
	self assert: (memory fetchFloat64: 2 ofObject: result) equals: 5.0.
	self assert: (memory fetchFloat64: 3 ofObject: result) equals: 6.0.
	
	self assert: (memory fetchFloat64: 2 ofObject: array) equals: 5.0.
	self assert: (memory fetchFloat64: 3 ofObject: array) equals: 6.0.
]

{ #category : 'tests-simd' }
VMByteCodesTest >> testSubVectorBytecode [

	| index vector0 vector1 result |
	index := 0.

	vector0 := self new64BitIndexableOfSize: 2.
	memory storeFloat64: 0 ofObject: vector0 withValue: 5.0.
	memory storeFloat64: 1 ofObject: vector0 withValue: 3.0.

	vector1 := self new64BitIndexableOfSize: 2.
	memory storeFloat64: 0 ofObject: vector1 withValue: 2.0.
	memory storeFloat64: 1 ofObject: vector1 withValue: 1.0.

	stackBuilder addNewFrame stack: {
			vector0.
			vector1 }.
	stackBuilder buildStack.

	self interpret: [ interpreter subFloat64VectorBytecode ].

	result := interpreter stackTop.

	self deny: result equals: memory nilObject.
	self assert: (memory fetchFloat64: 0 ofObject: result) equals: 3.0.
	self assert: (memory fetchFloat64: 1 ofObject: result) equals: 2.0
]

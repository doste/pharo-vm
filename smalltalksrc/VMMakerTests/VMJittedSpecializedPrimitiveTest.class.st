Class {
	#name : #VMJittedSpecializedPrimitiveTest,
	#superclass : #VMJittedPrimitivesTest,
	#pools : [
		'CogRTLOpcodes'
	],
	#category : #'VMMakerTests-JitTests'
}

{ #category : #'building suites' }
VMJittedSpecializedPrimitiveTest class >> wordSizeParameters [

	^ ParametrizedTestMatrix new
		addCase: { #ISA -> #'X64'. #wordSize -> 8};
		yourself
]

{ #category : #'tests - primitiveGreaterOrEqual' }
VMJittedSpecializedPrimitiveTest >> testPrimitiveFFI [
	
	| endInstruction primitiveAddress tfExternalFunction addressOfTheCFunctionToCall |
	
	interpreter libFFI: LibFFI new.
	interpreter libFFI interpreter: interpreter.
	
	primitiveAddress := self compile: [ 
		cogit objectRepresentation genPrimitiveSameThreadCalloutUint64Uint64.
		"If the primitive fails it continues, so we need to have an instruction to detect the end"
		endInstruction := cogit Stop ].
	
	tfExternalFunction := self 
		createExternalFunctionFor:  [ :anArgument |  anArgument ] 
		withArgumentTypes: { interpreter libFFI uint64 } 
		withReturnType: interpreter libFFI uint64.
		
	addressOfTheCFunctionToCall := memory fetchPointer: 0 ofObject: tfExternalFunction.

	self prepareStackForSendReceiver: (memory nilObject) arguments: { tfExternalFunction . memory integerObjectOf: 8888 }.	
	
	self runFrom: primitiveAddress until: addressOfTheCFunctionToCall.
	self assert: self machineSimulator rdi equals: 8888.
	
]

{ #category : #'tests - primitiveGreaterOrEqual' }
VMJittedSpecializedPrimitiveTest >> testPrimitiveFFIFunctionIsCalledCorrectly [

	| primitiveAddress tfExternalFunction addressOfTheCFunctionToCall |
	interpreter libFFI: LibFFI new.
	interpreter libFFI interpreter: interpreter.

	primitiveAddress := self compile: [
		                    cogit objectRepresentation
			                    genPrimitiveSameThreadCalloutUint64Uint64.
		                    "If the primitive fails it continues, so we need to have an instruction to detect the end"
		                    cogit Stop ].

	tfExternalFunction := self
		                      createExternalFunctionFor: [ :anArgument |
		                      anArgument ]
		                      withArgumentTypes:
		                      { interpreter libFFI uint64 }
		                      withReturnType: interpreter libFFI uint64.

	addressOfTheCFunctionToCall := memory
		                               fetchPointer: 0
		                               ofObject: tfExternalFunction.

	self prepareStackForSendReceiver: memory nilObject arguments: {
			tfExternalFunction.
			(memory integerObjectOf: 8888) }.

	self openMachineDebuggerAt: primitiveAddress.

	self runFrom: primitiveAddress until: addressOfTheCFunctionToCall.
	self
		assert: self machineSimulator pc
		equals: addressOfTheCFunctionToCall.
	self assert: self machineSimulator rdi equals: 8888
]

{ #category : #'tests - primitiveGreaterOrEqual' }
VMJittedSpecializedPrimitiveTest >> testPrimitiveFFIFunctionReturnsCorreclty [ 

	| primitiveAddress tfExternalFunction addressOfTheCFunctionToCall |
	interpreter libFFI: LibFFI new.
	interpreter libFFI interpreter: interpreter.

	primitiveAddress := self compile: [
		                    cogit objectRepresentation
			                    genPrimitiveSameThreadCalloutUint64Uint64.
		                    "If the primitive fails it continues, so we need to have an instruction to detect the end"
		                    cogit Stop ].

	tfExternalFunction := self
		                      createExternalFunctionFor: [ :anArgument |
		                      anArgument ]
		                      withArgumentTypes:
		                      { interpreter libFFI uint64 }
		                      withReturnType: interpreter libFFI uint64.

	addressOfTheCFunctionToCall := memory
		                               fetchPointer: 0
		                               ofObject: tfExternalFunction.

	self prepareStackForSendReceiver: memory nilObject arguments: {
			tfExternalFunction.
			(memory integerObjectOf: 8888) }.

	self openMachineDebuggerAt: primitiveAddress.

	self runFrom: primitiveAddress until: callerAddress.
	self
		assert: self machineSimulator pc
		equals: addressOfTheCFunctionToCall.
	self assert: self machineSimulator rdi equals: 8888
]

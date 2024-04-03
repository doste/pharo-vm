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
	1halt.
	primitiveAddress := self compile: [ 
		cogit objectRepresentation genPrimitiveSameThreadCalloutUint64Uint64.
		"If the primitive fails it continues, so we need to have an instruction to detect the end"
		endInstruction := cogit Stop ].
	
	tfExternalFunction := self 
		createExternalFunctionFor:  [ :anArgument |  anArgument ] 
		withArgumentTypes: { interpreter libFFI uint64 } 
		withReturnType: interpreter libFFI uint64.
		
	addressOfTheCFunctionToCall :=  interpreter readAddress: (memory fetchPointer: 0 ofObject: tfExternalFunction).

	self prepareStackForSendReceiver: (memory nilObject) arguments: { tfExternalFunction . memory integerObjectOf: 8888 }.	
	
	self runFrom: primitiveAddress until: addressOfTheCFunctionToCall.
	self assert: self machineSimulator rdi equals: 8888.
	
]

{ #category : #'tests - primitiveGreaterOrEqual' }
VMJittedSpecializedPrimitiveTest >> testPrimitiveFFIFunctionIsCalledCorrectly [

	| primitiveAddress tfExternalFunction addressOfTheCFunctionToCall aFunctionBlock |
	interpreter libFFI: LibFFI new.
	interpreter libFFI interpreter: interpreter.

	primitiveAddress := self compile: [
		                    cogit objectRepresentation
			                    genPrimitiveSameThreadCalloutUint64Uint64.
		                    "If the primitive fails it continues, so we need to have an instruction to detect the end"
		                    cogit Stop ].

	aFunctionBlock := [ :anArgument | anArgument ].

	tfExternalFunction := self
		                      createExternalFunctionFor: aFunctionBlock
		                      withArgumentTypes:
		                      { interpreter libFFI uint64 }
		                      withReturnType: interpreter libFFI uint64.

	addressOfTheCFunctionToCall :=  interpreter libFFI addressForBlock: aFunctionBlock.

	self prepareStackForSendReceiver: memory nilObject arguments: {
			tfExternalFunction.
			(memory integerObjectOf: 8888) }.

	self runFrom: primitiveAddress until: addressOfTheCFunctionToCall.
	self
		assert: self machineSimulator pc
		equals: addressOfTheCFunctionToCall.
	"The second argument, the uint64 in our case, it's passed in the RSI register"
	self assert: self machineSimulator rsi equals: 8888
]

{ #category : #'tests - primitiveGreaterOrEqual' }
VMJittedSpecializedPrimitiveTest >> testPrimitiveFFIFunctionReturnsCorreclty [ 

	| primitiveAddress tfExternalFunction addressOfTheCFunctionToCall aFunctionBlock mappedFunctionBinary |
	interpreter libFFI: LibFFI new.
	interpreter libFFI interpreter: interpreter.
	interpreter libFFI startingAddress: 16r1000.
1halt.

   mappedFunctionBinary := ByteArray new: 4096.
	#(16r55 16r48 16r89 16re5 16r48 16r8d 16r04 16r37 16r5d 16rc3 16r66 16r0f 16r1f 16r44 16r00 16r00) doWithIndex: [ :elem :idx | mappedFunctionBinary at: idx put: elem ].
	machineSimulator mapMemory: mappedFunctionBinary at: 16r1000.

	primitiveAddress := self compile: [
		                    cogit objectRepresentation
			                    genPrimitiveSameThreadCalloutUint64Uint64.
		                    "If the primitive fails it continues, so we need to have an instruction to detect the end"
		                    cogit Stop ].

	aFunctionBlock := [ :anArgument | anArgument ].

	tfExternalFunction := self
		                      createExternalFunctionFor: aFunctionBlock
		                      withArgumentTypes:
		                      { interpreter libFFI uint64 }
		                      withReturnType: interpreter libFFI uint64.

	addressOfTheCFunctionToCall :=  interpreter libFFI addressForBlock: aFunctionBlock.


	self prepareStackForSendReceiver: memory nilObject arguments: {
			tfExternalFunction.
			(memory integerObjectOf: 8888) }.

self openMachineDebuggerAt: primitiveAddress.

	"self runFrom: primitiveAddress until: callerAddress."
	
	machineSimulator
		simulateLeafCallOf: 16r1000
		nextpc: primitiveAddress
		memory: nil.

	self
		assert: self machineSimulator pc
		equals: addressOfTheCFunctionToCall.
		
	self assert: self machineSimulator rdi equals: 8888
]

{ #category : #'tests - primitiveGreaterOrEqual' }
VMJittedSpecializedPrimitiveTest >> testPrimitiveFFIFunctionReturnsCorrecltyVersion2 [

	| primitiveAddress tfExternalFunction addressOfTheCFunctionToCall aFunctionBlock functionAddress functionExternalAddress tfFunctionDefinition cif cifExternalAddress |
	interpreter libFFI: LibFFI new.
	interpreter libFFI interpreter: interpreter.
	"interpreter libFFI startingAddress: 16r1000."
1halt.
	
	functionAddress := self compile: [ cogit MoveR: Arg0Reg R: TempReg .cogit RetN: 0 ]. "mov rdi, rax. ret"

	primitiveAddress := self compile: [
		                    cogit objectRepresentation
			                    genPrimitiveSameThreadCalloutUint64Uint64.
		                    "If the primitive fails it continues, so we need to have an instruction to detect the end"
		                    cogit Stop ].

	aFunctionBlock := [ :anArgument | anArgument ].

	tfExternalFunction := self newObjectWithSlots: 2. 
	functionExternalAddress := self newExternalAddress: functionAddress. 
	tfFunctionDefinition := self newObjectWithSlots: 1.
	
	cif := interpreter libFFI newCif.
	cif argumentTypes: { interpreter libFFI uint64 }.
	cif returnType: interpreter libFFI uint64.
		
	cifExternalAddress := self newExternalAddress: (cif address). 

	memory storePointer: 0 ofObject: tfExternalFunction withValue: functionExternalAddress.
	memory storePointer: 1 ofObject: tfExternalFunction withValue: tfFunctionDefinition.
	memory storePointer: 0 ofObject: tfFunctionDefinition withValue: cifExternalAddress.

	
	"self
		createFramefulCallFrom: callerAddress
		receiver: memory nilObject
		arguments: { memory integerObjectOf: 8888 }
		temporaries: #(  )."

	self prepareStackForSendReceiver: memory nilObject arguments: {
			tfExternalFunction.
			(memory integerObjectOf: 8888) }.

	self openMachineDebuggerAt: primitiveAddress .
1halt.
	self runFrom: primitiveAddress until: callerAddress.
1halt.
	"machineSimulator
		simulateLeafCallOf: 16r1000
		nextpc: primitiveAddress
		memory: nil.
	self
		assert: self machineSimulator pc
		equals: addressOfTheCFunctionToCall."
		
	self assert: self machineSimulator rdi equals: 8888
]

{ #category : #'tests - primitiveGreaterOrEqual' }
VMJittedSpecializedPrimitiveTest >> testPrimitiveFFIShouldFailWithArgumentNegative [
	
	| endInstruction primitiveAddress tfExternalFunction  aFunctionBlock |
	
	interpreter libFFI: LibFFI new.
	interpreter libFFI interpreter: interpreter.

	primitiveAddress := self compile: [ 
		cogit objectRepresentation genPrimitiveSameThreadCalloutUint64Uint64.
		"If the primitive fails it continues, so we need to have an instruction to detect the end"
		endInstruction := cogit Stop ].
	
	aFunctionBlock := [ :anArgument | anArgument ].

	tfExternalFunction := self
		                      createExternalFunctionFor: aFunctionBlock
		                      withArgumentTypes:
		                      { interpreter libFFI uint64 }
		                      withReturnType: interpreter libFFI uint64.

	self prepareStackForSendReceiver: memory nilObject arguments: {
			tfExternalFunction.
			(memory integerObjectOf: -7777) }.	"Not an uint64! It should fail."

	
	self runFrom: primitiveAddress until: endInstruction address.
	
]

{ #category : #'tests - primitiveGreaterOrEqual' }
VMJittedSpecializedPrimitiveTest >> testPrimitiveFFIShouldFailWithArgumentNotImmediate [
	
	| endInstruction primitiveAddress tfExternalFunction  aFunctionBlock |
	
	interpreter libFFI: LibFFI new.
	interpreter libFFI interpreter: interpreter.

	primitiveAddress := self compile: [ 
		cogit objectRepresentation genPrimitiveSameThreadCalloutUint64Uint64.
		"If the primitive fails it continues, so we need to have an instruction to detect the end"
		endInstruction := cogit Stop ].
	
	aFunctionBlock := [ :anArgument | anArgument ].

	tfExternalFunction := self
		                      createExternalFunctionFor: aFunctionBlock
		                      withArgumentTypes:
		                      { interpreter libFFI uint64 }
		                      withReturnType: interpreter libFFI uint64.

	self prepareStackForSendReceiver: memory nilObject arguments: {
			tfExternalFunction.
			memory trueObject }.	"Not an uint64! It should fail."

	
	self runFrom: primitiveAddress until: endInstruction address.
	
]

{ #category : #'tests - primitiveGreaterOrEqual' }
VMJittedSpecializedPrimitiveTest >> testPrimitiveFFIShouldFailWithInvalidCifNargs [
	
	| endInstruction primitiveAddress tfExternalFunction  aFunctionBlock functionAddress functionExternalAddress tfFunctionDefinition cif cifExternalAddress |
	
	interpreter libFFI: LibFFI new.
	interpreter libFFI interpreter: interpreter.

	primitiveAddress := self compile: [ 
		cogit objectRepresentation genPrimitiveSameThreadCalloutUint64Uint64.
		"If the primitive fails it continues, so we need to have an instruction to detect the end"
		endInstruction := cogit Stop ].
	
	aFunctionBlock := [ :anArgument | anArgument ].

	"tfExternalFunction := self
		                      createExternalFunctionFor: aFunctionBlock
		                      withArgumentTypes:
		                      { interpreter libFFI uint64 }
		                      withReturnType: interpreter libFFI uint64."
	functionAddress := interpreter libFFI registerFunction: aFunctionBlock.

	tfExternalFunction := self newObjectWithSlots: 2. 
	functionExternalAddress := self newExternalAddress: functionAddress. 
	tfFunctionDefinition := self newObjectWithSlots: 1.
	
	cif := interpreter libFFI newCif.
	cif argumentTypes: { interpreter libFFI uint64 . interpreter libFFI uint64}.    "<-- Bad CIF!"
	cif returnType: interpreter libFFI uint64.
		
	cifExternalAddress := self newExternalAddress: (cif address). 

	memory storePointer: 0 ofObject: tfExternalFunction withValue: functionExternalAddress.
	memory storePointer: 1 ofObject: tfExternalFunction withValue: tfFunctionDefinition.
	memory storePointer: 0 ofObject: tfFunctionDefinition withValue: cifExternalAddress.	


	self prepareStackForSendReceiver: memory nilObject arguments: {
			tfExternalFunction.
			memory trueObject }.	"Not an uint64! It should fail."

	
	self runFrom: primitiveAddress until: endInstruction address.
	
]

{ #category : #'tests - primitiveGreaterOrEqual' }
VMJittedSpecializedPrimitiveTest >> testPrimitiveFFIShouldFailWithInvalidCifRtype [
	
	| endInstruction primitiveAddress tfExternalFunction  aFunctionBlock functionAddress functionExternalAddress tfFunctionDefinition cif cifExternalAddress |
	
	interpreter libFFI: LibFFI new.
	interpreter libFFI interpreter: interpreter.

	primitiveAddress := self compile: [ 
		cogit objectRepresentation genPrimitiveSameThreadCalloutUint64Uint64.
		"If the primitive fails it continues, so we need to have an instruction to detect the end"
		endInstruction := cogit Stop ].
	
	aFunctionBlock := [ :anArgument | anArgument ].

	"tfExternalFunction := self
		                      createExternalFunctionFor: aFunctionBlock
		                      withArgumentTypes:
		                      { interpreter libFFI uint64 }
		                      withReturnType: interpreter libFFI uint64."
	functionAddress := interpreter libFFI registerFunction: aFunctionBlock.

	tfExternalFunction := self newObjectWithSlots: 2. 
	functionExternalAddress := self newExternalAddress: functionAddress. 
	tfFunctionDefinition := self newObjectWithSlots: 1.
	
	cif := interpreter libFFI newCif.
	cif argumentTypes: { interpreter libFFI uint64 }.    
	cif returnType: interpreter libFFI uint8.					"<-- Bad CIF!"
		
	cifExternalAddress := self newExternalAddress: (cif address). 

	memory storePointer: 0 ofObject: tfExternalFunction withValue: functionExternalAddress.
	memory storePointer: 1 ofObject: tfExternalFunction withValue: tfFunctionDefinition.
	memory storePointer: 0 ofObject: tfFunctionDefinition withValue: cifExternalAddress.	


	self prepareStackForSendReceiver: memory nilObject arguments: {
			tfExternalFunction.
			memory trueObject }.	"Not an uint64! It should fail."

	
	self runFrom: primitiveAddress until: endInstruction address.
	
]

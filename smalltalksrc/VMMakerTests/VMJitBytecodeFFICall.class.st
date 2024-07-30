Class {
	#name : 'VMJitBytecodeFFICall',
	#superclass : 'VMStackToRegisterMappingCogitTest',
	#category : 'VMMakerTests',
	#package : 'VMMakerTests'
}

{ #category : 'building suites' }
VMJitBytecodeFFICall class >> wordSizeParameters [

	"Test that ffi calls are optimized in x64.
	For ARM64 and 32 bits there is a separate set of tests checking that it falls back"
	^ ParametrizedTestMatrix new
		addCase: { #ISA -> #'X64'. #wordSize -> 8};
		yourself
]

{ #category : 'helpers' }
VMJitBytecodeFFICall >> createExternalFunctionForCogitBlock: aCogitBlock withArgumentTypes: argumentTypes withReturnType: returnType [

	| functionAddress tfExternalFunction functionExternalAddress tfFunctionDefinition cif cifExternalAddress |
	
	functionAddress := self compile: aCogitBlock.
	tfExternalFunction := self newObjectWithSlots: 2. 
	functionExternalAddress := self newExternalAddress: functionAddress. 
	tfFunctionDefinition := self newObjectWithSlots:4 .
	
	cif := interpreter libFFI newCif.
	cif argumentTypes: argumentTypes.
	cif returnType: returnType.
		
	cifExternalAddress := self newExternalAddress: (cif address). 

	memory storePointer: 0 ofObject: tfExternalFunction withValue: functionExternalAddress.
	memory storePointer: 1 ofObject: tfExternalFunction withValue: tfFunctionDefinition.
	memory storePointer: 0 ofObject: tfFunctionDefinition withValue: cifExternalAddress.	

	^ tfExternalFunction
]

{ #category : 'helpers' }
VMJitBytecodeFFICall >> createExternalFunctionForCogitBlockWithOnlyAStopInstructionWithArgumentTypes: argumentTypes withReturnType: returnType [

	| functionAddress tfExternalFunction functionExternalAddress tfFunctionDefinition cif cifExternalAddress |
	
	functionAddress := self compile: [ cogit Stop ].
	tfExternalFunction := self newObjectWithSlots: 2. 
	functionExternalAddress := self newExternalAddress: functionAddress. 
	tfFunctionDefinition := self newObjectWithSlots:4 .
	
	cif := interpreter libFFI newCif.
	cif argumentTypes: argumentTypes.
	cif returnType: returnType.
		
	cifExternalAddress := self newExternalAddress: (cif address). 

	memory storePointer: 0 ofObject: tfExternalFunction withValue: functionExternalAddress.
	memory storePointer: 1 ofObject: tfExternalFunction withValue: tfFunctionDefinition.
	memory storePointer: 0 ofObject: tfFunctionDefinition withValue: cifExternalAddress.	

	^ {tfExternalFunction. functionAddress}
]

{ #category : 'helpers' }
VMJitBytecodeFFICall >> createExternalFunctionWithAddress: anAddress withArgumentTypes: argumentTypes withReturnType: returnType [

	| tfExternalFunction functionExternalAddress tfFunctionDefinition cif cifExternalAddress |

	tfExternalFunction := self newObjectWithSlots: 2. 
	functionExternalAddress := self newExternalAddress: anAddress. 
	tfFunctionDefinition := self newObjectWithSlots:4 .
	
	cif := interpreter libFFI newCif.
	cif argumentTypes: argumentTypes.
	cif returnType: returnType.
		
	cifExternalAddress := self newExternalAddress: (cif address). 

	memory storePointer: 0 ofObject: tfExternalFunction withValue: functionExternalAddress.
	memory storePointer: 1 ofObject: tfExternalFunction withValue: tfFunctionDefinition.
	memory storePointer: 0 ofObject: tfFunctionDefinition withValue: cifExternalAddress.	

	^ tfExternalFunction
]

{ #category : 'helpers' }
VMJitBytecodeFFICall >> fakeTrampoline [
	^ self compile: [ cogit RetN: 0 ]

]

{ #category : 'running' }
VMJitBytecodeFFICall >> setUp [

	super setUp.
	LibFFIConstants initialize.
	
	"genBytecodeFFICall needs this trampoline to compile the fallback argument array allocation.
	Set a fake trampoline by default. Override in the tests if necessary"
	cogit ceScheduleScavengeTrampoline: self fakeTrampoline.
	
	"genBytecodeFFICall needs this trampoline to compile the fallback message send.
	Set a fake trampoline by default. Override in the tests if necessary"
	cogit ordinarySendTrampolineAt: 2 put: self fakeTrampoline.
]

{ #category : 'tests' }
VMJitBytecodeFFICall >> testBytecodeFFICallLargeExternalAddress [

	| aVeryLargeAddress tfExternalFunction stopAddress addr methodObject |
	
	"Test that the C function is called correctly: the genBytecodeFFICall jumps to the given address and that it doesn't 'cut' the address."
	aVeryLargeAddress := 16rFFFFFFFFFFFFFFFF.
	
	tfExternalFunction := self createExternalFunctionWithAddress: aVeryLargeAddress withArgumentTypes: { interpreter libFFI uint64 } 
											withReturnType: interpreter libFFI uint64.

	methodObject := methodBuilder newMethod
		                literals: {
				                memory nilObject.
				                tfExternalFunction };
		                buildMethod.

	addr := self
		        compile: [
			        cogit methodOrBlockNumTemps: 1.
			        cogit methodOrBlockNumArgs: 1.
			cogit needsFrame: true.
			        cogit initSimStackForFramefulMethod: 0.


			        cogit methodObj: methodObject.
			        cogit ssPushConstant: (memory integerObjectOf: 888).
			        cogit byte0: 230.
			        cogit byte1: 1.
			        cogit genBytecodeFFICall.

			        "The bytecode (as all bytecodes) will push its result to the stack. We move it to a register so we can then assert about its value."

			        "cogit PopR: ReceiverResultReg."
			        cogit ssTop moveToReg: ReceiverResultReg.
			        cogit ssPop: 1.

			        "This instruction should not be called"
			        stopAddress := cogit Stop ]
		        bytecodes: 1.

	self runFrom: addr until: aVeryLargeAddress.

	self
		assert: machineSimulator instructionPointerRegisterValue
		equals: aVeryLargeAddress
]

{ #category : 'tests' }
VMJitBytecodeFFICall >> testBytecodeFFICallSwitchToTheCStack [

	| tfExternalFunctionAndCompiledBlock stopAddress addr methodObject cStackPointer tfExternalFunction compiledBlockWithStop |
	tfExternalFunctionAndCompiledBlock := self
		                     createExternalFunctionForCogitBlockWithOnlyAStopInstructionWithArgumentTypes:
		                      { interpreter libFFI uint64 }
		                      withReturnType: interpreter libFFI uint64.
	"tfExternalFunctionAndCompiledBlock will be an array of two elements: the TFExternalFunction and the address of the compiled block with a Stop"
	tfExternalFunction :=	tfExternalFunctionAndCompiledBlock first.
		
	compiledBlockWithStop := tfExternalFunctionAndCompiledBlock second.

	methodObject := methodBuilder newMethod
		                literals: {
				                memory nilObject.
				                tfExternalFunction };
		                buildMethod.

	addr := self
		        compile: [
			        cogit methodOrBlockNumTemps: 1.
			        cogit methodOrBlockNumArgs: 1.
			        cogit initSimStackForFramefulMethod: 0.
					  cogit needsFrame: true. 

			        cogit methodObj: methodObject.
			        cogit ssPushConstant: (memory integerObjectOf: 888).
			        cogit byte0: 230.
			        cogit byte1: 1.
			        cogit genBytecodeFFICall.

			        "This instruction should not be called"
			        stopAddress := cogit Stop ]
		        bytecodes: 1.
	
	"smalltalkStackPointer := machineSimulator smalltalkStackPointerRegisterValue."
	cStackPointer := cogit getCStackPointer.
	
		"1halt. self openMachineDebuggerAt:  compiledBlockWithStop." 
	self runFrom: addr until: compiledBlockWithStop.
"1halt."
	self assert: (machineSimulator stackPointerRegisterValue) equals: cStackPointer - 8  "We assert that we switched correctly to use the C stack"
	


]

{ #category : 'tests' }
VMJitBytecodeFFICall >> testBytecodeFFICallWithExternalFunctionAccessToTheCorrectArgument [

	| tfExternalFunction stopAddress addr methodObject actualExternalAddress anExternalAddressObject |
	tfExternalFunction := self
		                      createExternalFunctionForCogitBlock: [  "add the two int args and return the pointer"
			                      cogit AddR: Arg0Reg R: ReceiverResultReg.
										cogit MoveR: Arg1Reg R: TempReg.
			                      cogit RetN: 0 ]
		                      withArgumentTypes:
		                      { interpreter libFFI uint64 . interpreter libFFI pointer . interpreter libFFI uint32  }
		                      withReturnType: interpreter libFFI pointer.
	
	actualExternalAddress := memory integerObjectOf: 16rffff.
	anExternalAddressObject := self newExternalAddress: actualExternalAddress.

	methodObject := methodBuilder newMethod
		                literals: {
				                memory nilObject.
				                tfExternalFunction };
		                buildMethod.

	addr := self
		        compile: [
			        cogit methodOrBlockNumTemps: 1.
			        cogit methodOrBlockNumArgs: 1.
			        cogit initSimStackForFramefulMethod: 0.
					  cogit needsFrame: true. 

			        cogit methodObj: methodObject.
			        cogit ssPushConstant: (memory integerObjectOf: 1).
					  cogit ssPushConstant: anExternalAddressObject.
					  cogit ssPushConstant: (memory integerObjectOf: 3).
			        cogit byte0: 230.
			        cogit byte1: 1.
			        cogit genBytecodeFFICall.
			
					"The genBytecodeFFICall left us in ReceiverResultReg a new ExternalAddress object.
					  We need to access to its first slot to extract the actual external address"
					  cogit MoveMw: 8 "skip the header" r: ReceiverResultReg R: ReceiverResultReg.

			        "This instruction should not be called"
			        stopAddress := cogit Stop ]
		        bytecodes: 1.
		
	self runFrom: addr until: stopAddress address.

	self
		assert: machineSimulator receiverRegisterValue
		equals: actualExternalAddress.
]

{ #category : 'tests' }
VMJitBytecodeFFICall >> testBytecodeFFICallWithExternalFunctionThreeArgs [

	| tfExternalFunction stopAddress addr methodObject |
	tfExternalFunction := self
		                      createExternalFunctionForCogitBlock: [  "add the three args"
			                      cogit MoveR: Arg0Reg R: TempReg.
										cogit AddR: Arg1Reg R: TempReg.
										cogit AddR: ReceiverResultReg R: TempReg.
			                      cogit RetN: 0 ]
		                      withArgumentTypes:
		                      { interpreter libFFI uint64 . interpreter libFFI sint8 . interpreter libFFI uint32  }
		                      withReturnType: interpreter libFFI uint64.
	
	methodObject := methodBuilder newMethod
		                literals: {
				                memory nilObject.
				                tfExternalFunction };
		                buildMethod.

	addr := self
		        compile: [
			        cogit methodOrBlockNumTemps: 1.
			        cogit methodOrBlockNumArgs: 1.
			        cogit initSimStackForFramefulMethod: 0.
					  cogit needsFrame: true. 

			        cogit methodObj: methodObject.
			        cogit ssPushConstant: (memory integerObjectOf: 1).
					  cogit ssPushConstant: (memory integerObjectOf: 2).
					  cogit ssPushConstant: (memory integerObjectOf: 3).
			        cogit byte0: 230.
			        cogit byte1: 1.
			        cogit genBytecodeFFICall.

			        "This instruction should not be called"
			        stopAddress := cogit Stop ]
		        bytecodes: 1.
		
	self runFrom: addr until: stopAddress address.

	self
		assert: machineSimulator receiverRegisterValue
		equals: (memory integerObjectOf: (1+2+3))
]

{ #category : 'tests' }
VMJitBytecodeFFICall >> testBytecodeFFICallWithSimpleExternalFunction [

	| tfExternalFunction stopAddress addr methodObject |
	tfExternalFunction := self
		                      createExternalFunctionForCogitBlock: [
			                      cogit MoveR: Arg0Reg R: TempReg.
			                      cogit RetN: 0 ]
		                      withArgumentTypes:
		                      { interpreter libFFI uint64 }
		                      withReturnType: interpreter libFFI uint64.
	
	methodObject := methodBuilder newMethod
		                literals: {
				                memory nilObject.
				                tfExternalFunction };
		                buildMethod.

	addr := self
		        compile: [
			        cogit methodOrBlockNumTemps: 1.
			        cogit methodOrBlockNumArgs: 1.
			        cogit initSimStackForFramefulMethod: 0.
					  cogit needsFrame: true. 

			        cogit methodObj: methodObject.
	
			        cogit ssPushConstant: (memory integerObjectOf: 888).
			        cogit byte0: 230.
			        cogit byte1: 1.
			        cogit genBytecodeFFICall.

			        "This instruction should not be called"
			        stopAddress := cogit Stop ]
		        bytecodes: 1.
		
	self runFrom: addr until: stopAddress address.

	self
		assert: machineSimulator receiverRegisterValue
		equals: (memory integerObjectOf: 888)
]

{ #category : 'tests' }
VMJitBytecodeFFICall >> testBytecodeFFIExternalFunctionPointerPointer [

	| tfExternalFunction stopAddress addr methodObject actualExternalAddress anExternalAddressObject |
	"Test the prototype pointer fn(pointer) works"
	
	tfExternalFunction := self
		                      createExternalFunctionForCogitBlock: [
										cogit MoveR: Arg0Reg R: TempReg.
										cogit RetN: 0
			                      ]
		                      withArgumentTypes:
		                         { interpreter libFFI pointer }
		                      withReturnType: interpreter libFFI pointer.

	methodObject := methodBuilder newMethod
		                literals: {
				                memory nilObject.   "this would be the runner"
				                tfExternalFunction };
		                buildMethod.
	
	actualExternalAddress := memory integerObjectOf: 16rffff.
	anExternalAddressObject := self newExternalAddress: actualExternalAddress.

	addr := self
		        compile: [
			        cogit methodOrBlockNumTemps: 1.
			        cogit methodOrBlockNumArgs: 1.
					  cogit needsFrame: true. 
			        cogit initSimStackForFramefulMethod: 0.
			        cogit methodObj: methodObject.
			    
					  cogit ssPushConstant: anExternalAddressObject.
					  cogit byte0: 230.
			        cogit byte1: 1.
			        cogit genBytecodeFFICall.
			
					  "The genBytecodeFFICall left us in ReceiverResultReg a new ExternalAddress object.
					  We need to access to its first slot to extract the actual external address"
					  cogit MoveMw: 8 "skip the header" r: ReceiverResultReg R: ReceiverResultReg.

			        "This instruction should not be called"
			        stopAddress := cogit Stop ]
		        bytecodes: 1.
		
	self runFrom: addr until: stopAddress address.

	self
		assert: machineSimulator receiverRegisterValue
		equals: actualExternalAddress.
]

{ #category : 'tests' }
VMJitBytecodeFFICall >> testBytecodeFFIExternalFunctionReturnsLargeInteger [

	| tfExternalFunction stopAddress addr methodObject |
	"Test the prototype pointer fn(pointer) works"
	
	tfExternalFunction := self
		                      createExternalFunctionForCogitBlock: [
										cogit MoveCw: (memory maxSmallInteger) R: TempReg.
										cogit AddR: Arg0Reg R: TempReg. 
										cogit RetN: 0
			                      ]
		                      withArgumentTypes:
		                         { interpreter libFFI uint8 }
		                      withReturnType: interpreter libFFI sint64.

	methodObject := methodBuilder newMethod
		                literals: {
				                memory nilObject.   "this would be the runner"
				                tfExternalFunction };
		                buildMethod.

	addr := self
		        compile: [
			        cogit methodOrBlockNumTemps: 1.
			        cogit methodOrBlockNumArgs: 1.
					  cogit needsFrame: true. 
			        cogit initSimStackForFramefulMethod: 0.
			        cogit methodObj: methodObject.
			    
					  cogit ssPushConstant: (memory integerObjectOf: 1).
					  cogit byte0: 230.
			        cogit byte1: 1.
			        cogit genBytecodeFFICall.
			
			        "This instruction should not be called"
			        stopAddress := cogit Stop ]
		        bytecodes: 1.

	self runFrom: addr until: stopAddress address.

	self
		assert: machineSimulator receiverRegisterValue
		equals: (memory integerObjectOf: (memory maxSmallInteger + 1))
]

{ #category : 'tests' }
VMJitBytecodeFFICall >> testBytecodeFFIExternalFunctionVoidPointerExtractsExternalAddress [

	| tfExternalFunction stopAddress addr methodObject actualExternalAddress anExternalAddressObject |
	"Test the prototype void fn(pointer) works.
	
	The external function to test doesn't return anything but will just copy the pointer given as argument."
	tfExternalFunction := self
		                      createExternalFunctionForCogitBlock: [
										cogit MoveR: Arg0Reg R: ReceiverResultReg.
										cogit RetN: 0
			                      ]
		                      withArgumentTypes:
		                         { interpreter libFFI pointer }
		                      withReturnType: interpreter libFFI void.

	methodObject := methodBuilder newMethod
		                literals: {
				                memory nilObject.   "this would be the runner"
				                tfExternalFunction };
		                buildMethod.
	
	actualExternalAddress := memory integerObjectOf: 16rffff.
	anExternalAddressObject := self newExternalAddress: actualExternalAddress.

	addr := self
		        compile: [
			        cogit methodOrBlockNumTemps: 1.
			        cogit methodOrBlockNumArgs: 1.
					  cogit needsFrame: true. "<<<<<< ojo"
			        cogit initSimStackForFramefulMethod: 0.
			        cogit methodObj: methodObject.
			    
					  cogit ssPushConstant: anExternalAddressObject.
					  cogit byte0: 230.
			        cogit byte1: 1.
			        cogit genBytecodeFFICall.

			        "This instruction should not be called"
			        stopAddress := cogit Stop ]
		        bytecodes: 1.

	self runFrom: addr until: stopAddress address.

	self
		assert: machineSimulator receiverRegisterValue
		equals: actualExternalAddress.
]

{ #category : 'tests' }
VMJitBytecodeFFICall >> testInvalidExternalAddressShouldFallback [

	| tfExternalFunction stopAddress addr methodObject anInvalidExternalAddress runner marker |
	"The external function to test doesn't return anything but will just copy the pointer given as argument."
	marker := memory integerObjectOf: 17.
	tfExternalFunction := self
		                      createExternalFunctionForCogitBlock: [
			                      cogit MoveR: Arg0Reg R: ReceiverResultReg.
			                      cogit RetN: 0 ]
		                      withArgumentTypes:
		                      { interpreter libFFI pointer }
		                      withReturnType: interpreter libFFI void.

	runner := memory integerObjectOf: 751.
	methodObject := methodBuilder newMethod
		                literals: {
				                runner.
				                tfExternalFunction };
		                buildMethod.

	anInvalidExternalAddress := memory integerObjectOf: 16rffff.

	addr := self
		        compile: [
			        cogit methodOrBlockNumTemps: 1.
			        cogit methodOrBlockNumArgs: 1.
			        cogit needsFrame: true.
			        cogit initSimStackForFramefulMethod: 0.
			        cogit methodObj: methodObject.

			        cogit ssPushConstant: marker.
			        cogit ssPushConstant: anInvalidExternalAddress.
			        cogit byte0: 230.
			        cogit byte1: 1.
			        cogit genBytecodeFFICall.

			        "This instruction should not be called"
			        stopAddress := cogit Stop ]
		        bytecodes: 1.

	self runFrom: addr until: (cogit simulatedTrampolineFor:
			 #ceFallbackFFICallUsingRunner:andExternalFunction:).

	self assert: machineSimulator carg0RegisterValue equals: runner.
	self
		assert: machineSimulator carg1RegisterValue
		equals: tfExternalFunction.
	self assert: interpreter stackTop equals: anInvalidExternalAddress.
	self assert: (interpreter stackValue: 1) equals: marker
]

{ #category : 'tests' }
VMJitBytecodeFFICall >> testNegative32BitInteger [

	| tfExternalFunction stopAddress addr methodObject |
	tfExternalFunction := self
		                      createExternalFunctionForCogitBlock: [
			                      cogit MoveR: Arg0Reg R: TempReg.
			                      cogit RetN: 0 ]
		                      withArgumentTypes:
		                      { interpreter libFFI sint32 }
		                      withReturnType: interpreter libFFI sint32.
	
	methodObject := methodBuilder newMethod
		                literals: {
				                memory nilObject.
				                tfExternalFunction };
		                buildMethod.

	addr := self
		        compile: [
			        cogit methodOrBlockNumTemps: 1.
			        cogit methodOrBlockNumArgs: 1.
			        cogit initSimStackForFramefulMethod: 0.
					  cogit needsFrame: true. 

			        cogit methodObj: methodObject.
			        cogit ssPushConstant: (memory integerObjectOf: -12).
			        cogit byte0: 230.
			        cogit byte1: 1.
			        cogit genBytecodeFFICall.

			        "This instruction should not be called"
			        stopAddress := cogit Stop ]
		        bytecodes: 1.
		
	self runFrom: addr until: stopAddress address.

	self
		assert: machineSimulator receiverRegisterValue
		equals: (memory integerObjectOf: -12)
]

{ #category : 'tests' }
VMJitBytecodeFFICall >> testNegative64BitInteger [

	| tfExternalFunction stopAddress addr methodObject |
	tfExternalFunction := self
		                      createExternalFunctionForCogitBlock: [
			                      cogit MoveR: Arg0Reg R: TempReg.
			                      cogit RetN: 0 ]
		                      withArgumentTypes:
		                      { interpreter libFFI sint64 }
		                      withReturnType: interpreter libFFI sint64.
	
	methodObject := methodBuilder newMethod
		                literals: {
				                memory nilObject.
				                tfExternalFunction };
		                buildMethod.

	addr := self
		        compile: [
			        cogit methodOrBlockNumTemps: 1.
			        cogit methodOrBlockNumArgs: 1.
			        cogit initSimStackForFramefulMethod: 0.
					  cogit needsFrame: true. 

			        cogit methodObj: methodObject.
			        cogit ssPushConstant: (memory integerObjectOf: -200).
			        cogit byte0: 230.
			        cogit byte1: 1.
			        cogit genBytecodeFFICall.

			        "This instruction should not be called"
			        stopAddress := cogit Stop ]
		        bytecodes: 1.
		
	self runFrom: addr until: stopAddress address.

	self
		assert: machineSimulator receiverRegisterValue
		equals: (memory integerObjectOf: -200)
]

{ #category : 'tests' }
VMJitBytecodeFFICall >> testNegative8BitInteger [

	| tfExternalFunction stopAddress addr methodObject |
	tfExternalFunction := self
		                      createExternalFunctionForCogitBlock: [
			                      cogit MoveR: Arg0Reg R: TempReg.
			                      cogit RetN: 0 ]
		                      withArgumentTypes:
		                      { interpreter libFFI sint8 }
		                      withReturnType: interpreter libFFI sint8.
	
	methodObject := methodBuilder newMethod
		                literals: {
				                memory nilObject.
				                tfExternalFunction };
		                buildMethod.

	addr := self
		        compile: [
			        cogit methodOrBlockNumTemps: 1.
			        cogit methodOrBlockNumArgs: 1.
			        cogit initSimStackForFramefulMethod: 0.
					  cogit needsFrame: true. 

			        cogit methodObj: methodObject.
			        cogit ssPushConstant: (memory integerObjectOf: -3).
			        cogit byte0: 230.
			        cogit byte1: 1.
			        cogit genBytecodeFFICall.

			        "This instruction should not be called"
			        stopAddress := cogit Stop ]
		        bytecodes: 1.
		
	self runFrom: addr until: stopAddress address.

	self
		assert: machineSimulator receiverRegisterValue
		equals: (memory integerObjectOf: -3)
]

{ #category : 'tests' }
VMJitBytecodeFFICall >> testPreserveLiveConstantInStack [

	| tfExternalFunction stopAddress addr methodObject |
	"Test that the C function is called correctly and that the bytecode doesn't mess the stack up, this is: it pops the arguments and pushes the result."
	tfExternalFunction := self
		                      createExternalFunctionForCogitBlock: [
			                      | loop done |
			                      cogit MoveCq: 0 R: TempReg.
			                      cogit MoveCq: 0 R: ClassReg.
			                      cogit MoveR: Arg0Reg R: Arg1Reg.
			                      loop := cogit CmpR: ClassReg R: Arg0Reg.
			                      done := cogit JumpLess: 0.

			                      cogit AddR: Arg1Reg R: TempReg.
			                      cogit SubCq: 1 R: Arg1Reg.
			                      cogit AddCq: 1 R: ClassReg.

			                      cogit Jump: loop.

			                      done jmpTarget: cogit Label.

			                      cogit RetN: 0 ]
		                      withArgumentTypes:
		                      { interpreter libFFI uint64 }
		                      withReturnType: interpreter libFFI uint64.

	methodObject := methodBuilder newMethod
		                literals: {
				                memory nilObject.
				                tfExternalFunction };
		                buildMethod.

	addr := self
		        compile: [
			        cogit methodOrBlockNumTemps: 1.
			        cogit methodOrBlockNumArgs: 1.
			        cogit initSimStackForFramefulMethod: 0.
			        cogit needsFrame: true.
			        cogit methodObj: methodObject.

			        cogit ssPushConstant: (memory integerObjectOf: 0). "a stack canary, just to check that the stack was not messed up."
			        cogit ssPushConstant: (memory integerObjectOf: 7).
			        cogit byte0: 230.
			        cogit byte1: 1.
			        cogit genBytecodeFFICall.

			        "Pop the result of the function value and read the top of the stack to verify if it has the marker value"
			        cogit ssPop: 1.

			        "Now, the canary should be in the top of the stack"
			        cogit ssTop moveToReg: Arg1Reg.

			        "This instruction should not be called"
			        stopAddress := cogit Stop ]
		        bytecodes: 1.

	self runFrom: addr until: stopAddress address.

	self
		assert: machineSimulator arg1RegisterValue
		equals: (memory integerObjectOf: 0)
]

{ #category : 'tests' }
VMJitBytecodeFFICall >> testPreserveLiveRegister [
	|  cogitBlock tfExternalFunction  stopAddress addr  methodObject |
	
	"Test that the C function is called correctly and that the bytecode doesn't write into a register that is being used elsewhere."
	self assert: (cogit isCallerSavedReg: ClassReg).
	
	cogitBlock := [	| loop done |	"This compiled block receives an integer 'n' and returns the value 1+2+...+n"
		 cogit MoveCq: 0 R: TempReg.
		 cogit MoveCq: 0 R: ClassReg.
		 cogit MoveR: Arg0Reg R: Arg1Reg. 
		 loop := cogit CmpR: ClassReg R: Arg0Reg.
		 done := cogit JumpLess: 0.
		
		 cogit AddR: Arg1Reg R: TempReg.
		 cogit SubCq: 1 R: Arg1Reg. 
		 cogit AddCq: 1 R: ClassReg. 
		 cogit Jump: loop.	
			
		 done jmpTarget: cogit Label.    
		 cogit RetN: 0
	  ].
		
	tfExternalFunction := self createExternalFunctionForCogitBlock: cogitBlock
											withArgumentTypes: { interpreter libFFI uint64.} 
											withReturnType: interpreter libFFI uint64.	
	methodObject :=  (methodBuilder newMethod
			 literals:{memory nilObject. tfExternalFunction};
			 buildMethod).
			
    addr := self
        compile: [ 
	
				cogit methodOrBlockNumTemps: 1.
				cogit methodOrBlockNumArgs: 1.
				cogit initSimStackForFramefulMethod: 0.
				cogit needsFrame: true. "<<<<<< ojo"
				cogit methodObj: methodObject.
				
				cogit MoveCq: (memory integerObjectOf: 19) R: ClassReg.  "We want to test that after the bytecode call, Arg0Reg was preserved, this is: it still contains 19." 
				cogit ssPushRegister: ClassReg. 								 "For Arg0Reg to be preserved we have to push it. This way, the system knows that its value must be preserved."
	
            cogit ssPushConstant: (memory integerObjectOf: 7).
            cogit byte0: 230.
            cogit byte1: 1.
            cogit genBytecodeFFICall.

				"Pop the result of the function value and read the top of the stack to verify if it has the marker value"
				cogit ssPop: 1.
				cogit ssTop moveToReg: ClassReg.
				
				"This instruction should not be called"
            stopAddress := cogit Stop.]
        bytecodes: 1.

	self runFrom: addr until: stopAddress address. 

	self assert: machineSimulator classRegisterValue equals: (memory integerObjectOf: 19).
]

{ #category : 'tests' }
VMJitBytecodeFFICall >> testTwoArgsUnsigned64BitsIntegers [

	| tfExternalFunction stopAddress addr methodObject |
	"Test that the C function is called correctly and that the bytecode doesn't mess the stack up, this is: it pops the arguments and pushes the result."
	tfExternalFunction := self
		                      createExternalFunctionForCogitBlock: [
			                       cogit MoveR: Arg0Reg R: TempReg.
										  cogit AddR: Arg1Reg R: TempReg. 
			                       cogit RetN: 0 ]
		                      withArgumentTypes:
		                      { interpreter libFFI uint64 . interpreter libFFI uint64 }
		                      withReturnType: interpreter libFFI uint64.

	methodObject := methodBuilder newMethod
		                literals: {
				                memory nilObject.
				                tfExternalFunction };
		                buildMethod.

	addr := self
		        compile: [
			        cogit methodOrBlockNumTemps: 1.
			        cogit methodOrBlockNumArgs: 1.
					  cogit needsFrame: true.
			        cogit initSimStackForFramefulMethod: 0.


			        cogit methodObj: methodObject.
			        cogit ssPushConstant: (memory integerObjectOf: 10).
			        cogit ssPushConstant: (memory integerObjectOf: 20).
			        cogit byte0: 230.
			        cogit byte1: 1.
			        cogit genBytecodeFFICall.
			   
			        "This instruction should not be called"
			        stopAddress := cogit Stop ]
		        bytecodes: 1.

	self runFrom: addr until: stopAddress address.
	
	self
		assert: machineSimulator receiverRegisterValue
		equals: (memory integerObjectOf: 30)
]

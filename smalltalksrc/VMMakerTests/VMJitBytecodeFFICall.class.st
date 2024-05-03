Class {
	#name : #VMJitBytecodeFFICall,
	#superclass : #VMStackToRegisterMappingCogitTest,
	#category : #VMMakerTests
}

{ #category : #'tests - extended push bytecode - push inst var' }
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

{ #category : #tests }
VMJitBytecodeFFICall >> testBytecodeFFICallWithComplexExternalFunction [
	|  cogitBlock tfExternalFunction  stopAddress addr  methodObject |
	
	"Test that the C function is called correctly and that the bytecode doesn't mess the stack up, this is: it pops the arguments and pushes the result."
	
	cogitBlock := [	| loop done |	
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
				cogit methodObj: methodObject.
	
				cogit ssPushConstant: (memory integerObjectOf: 0). "a stack canary, just to check that the stack was not messed up."
            cogit ssPushConstant: (memory integerObjectOf: 7).
            cogit byte0: 230.
            cogit byte1: 1.
            cogit genBytecodeFFICall.
				
				"The bytecode (as all bytecodes) will push its result to the stack. We move it to a register so we can then assert about its value."
				cogit ssTop moveToReg: ReceiverResultReg.
				cogit ssPop: 1.
				
				"Pop the canary."
				"cogit PopR: Arg1Reg."
				cogit ssTop moveToReg: Arg1Reg.
				cogit ssPop: 1.
				
				"This instruction should not be called"
            stopAddress := cogit Stop.]
        bytecodes: 1.

	self runFrom: addr until: stopAddress address . 

	self assert: machineSimulator receiverRegisterValue equals: (memory integerObjectOf: (7 + 6 + 5 + 4 + 3 + 2 + 1)).
	
	self assert: machineSimulator arg1RegisterValue equals: (memory integerObjectOf: 0).
]

{ #category : #tests }
VMJitBytecodeFFICall >> testBytecodeFFICallWithComplexExternalFunctionAndPreservesValuesInRegisters [
	|  cogitBlock tfExternalFunction  stopAddress addr  methodObject |
	
	"Test that the C function is called correctly and that the bytecode doesn't writo into a register that is being used elsewhere."
	
	cogitBlock := [	| loop done |	
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
				
				cogit MoveCq: (memory integerObjectOf: 19) R: Arg0Reg.  "We want to test that after the bytecode call, Arg0Reg was preserved, this is: it still contains 19." 
				cogit ssPushRegister: Arg0Reg. 								 "For Arg0Reg to be preserved we have to push it. This way, the system knows that its value must be preserved."
	
            cogit ssPushConstant: (memory integerObjectOf: 7).
            cogit byte0: 230.
            cogit byte1: 1.
            cogit genBytecodeFFICall.
				
				"The bytecode (as all bytecodes) will push its result to the stack. We move it to a register so we can then assert about its value."
				cogit ssTop moveToReg: ReceiverResultReg.
				cogit ssPop: 1.
				
				"Pop the preserved value"
				cogit ssTop moveToReg: Arg0Reg.
				cogit ssPop: 1.
				
				"This instruction should not be called"
            stopAddress := cogit Stop.]
        bytecodes: 1.

	self runFrom: addr until: stopAddress address . 

	self assert: machineSimulator receiverRegisterValue equals: (memory integerObjectOf: (7 + 6 + 5 + 4 + 3 + 2 + 1)).
	
	self assert: machineSimulator arg0RegisterValue equals: (memory integerObjectOf: 19).
]

{ #category : #tests }
VMJitBytecodeFFICall >> testBytecodeFFICallWithSimpleExternalFunction [

	| tfExternalFunction stopAddress addr methodObject |
	"Test that the C function is called correctly and that the bytecode doesn't mess the stack up, this is: it pops the arguments and pushes the result."
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


			        cogit methodObj: methodObject.
			        cogit ssPushConstant: (memory integerObjectOf: 888).
			        "cogit PushCq: (memory integerObjectOf: 888)."
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

	self runFrom: addr until: stopAddress address.

	self
		assert: machineSimulator receiverRegisterValue
		equals: (memory integerObjectOf: 888)
]

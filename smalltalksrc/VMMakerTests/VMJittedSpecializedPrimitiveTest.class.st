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
VMJittedSpecializedPrimitiveTest >> testPrimitiveFFIFunctionReturnsCorreclty [

	| primitiveAddress tfExternalFunction functionAddress functionExternalAddress tfFunctionDefinition cif cifExternalAddress libFFIType cifArrayOfArgTypes cifArgTypes |
	interpreter libFFI: LibFFI new.
	interpreter libFFI interpreter: interpreter.
	
	functionAddress := self compile: [ cogit MoveR: Arg0Reg R: TempReg .cogit RetN: 0 ]. "mov rdi, rax. ret"

	primitiveAddress := self compile: [
		                    cogit objectRepresentation
			                    genPrimitiveSameThreadCalloutUint64Uint64.
		                    "If the primitive fails it continues, so we need to have an instruction to detect the end"
		                    cogit Stop ].


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

	
	self prepareStackForSendReceiver: memory nilObject arguments: {
			tfExternalFunction.
			(memory integerObjectOf: 8888).
			 }.

	"self openMachineDebuggerAt: primitiveAddress."
	
	self runFrom: primitiveAddress until: callerAddress.
		
	self assert: self machineSimulator rax equals: (memory integerObjectOf: 8888)
]

{ #category : #'tests - primitiveGreaterOrEqual' }
VMJittedSpecializedPrimitiveTest >> testPrimitiveFFIFunctionShouldFailNegativeArgument [

	| primitiveAddress tfExternalFunction functionAddress functionExternalAddress tfFunctionDefinition cif cifExternalAddress libFFIType cifArrayOfArgTypes cifArgTypes endInstruction |
	interpreter libFFI: LibFFI new.
	interpreter libFFI interpreter: interpreter.
	
	functionAddress := self compile: [ cogit MoveR: Arg0Reg R: TempReg .cogit RetN: 0 ]. "mov rdi, rax. ret"

	primitiveAddress := self compile: [
		                    cogit objectRepresentation
			                    genPrimitiveSameThreadCalloutUint64Uint64.
		                    "If the primitive fails it continues, so we need to have an instruction to detect the end"
		                    endInstruction := cogit Stop ].


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

	
	self prepareStackForSendReceiver: memory nilObject arguments: {
			tfExternalFunction.
			(memory integerObjectOf: -77).														"<--- Negative argument. It should fail!"
			 }.

	"self openMachineDebuggerAt: primitiveAddress."
		
	self runFrom: primitiveAddress until: endInstruction address.
]

{ #category : #'tests - primitiveGreaterOrEqual' }
VMJittedSpecializedPrimitiveTest >> testPrimitiveFFIShouldFailWithArgumentNotImmediate [

	| primitiveAddress tfExternalFunction functionAddress functionExternalAddress tfFunctionDefinition cif cifExternalAddress libFFIType cifArrayOfArgTypes cifArgTypes endInstruction |

	interpreter libFFI: LibFFI new.
	interpreter libFFI interpreter: interpreter.
	
	functionAddress := self compile: [ cogit MoveR: Arg0Reg R: TempReg .cogit RetN: 0 ]. "mov rdi, rax. ret"

	primitiveAddress := self compile: [
		                    cogit objectRepresentation
			                    genPrimitiveSameThreadCalloutUint64Uint64.
		                    "If the primitive fails it continues, so we need to have an instruction to detect the end"
		                    endInstruction := cogit Stop ].


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
	memory storePointer: 0 ofObject: cif withValue: (memory integerObjectOf: 16rB).    "address"
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

	
	self prepareStackForSendReceiver: memory nilObject arguments: {
			tfExternalFunction.
			memory trueObject. 													"<- Argument of the function is not a number!"												
			 }.

	"self openMachineDebuggerAt: primitiveAddress.
		1halt."
	self runFrom: primitiveAddress until: endInstruction address.
	
]

{ #category : #'tests - primitiveGreaterOrEqual' }
VMJittedSpecializedPrimitiveTest >> testPrimitiveFFIShouldFailWithInvalidCifNargs [

	| primitiveAddress tfExternalFunction functionAddress functionExternalAddress tfFunctionDefinition cif cifExternalAddress libFFIType cifArrayOfArgTypes cifArgTypes endInstruction |

	interpreter libFFI: LibFFI new.
	interpreter libFFI interpreter: interpreter.
	
	functionAddress := self compile: [ cogit MoveR: Arg0Reg R: TempReg .cogit RetN: 0 ]. "mov rdi, rax. ret"

	primitiveAddress := self compile: [
		                    cogit objectRepresentation
			                    genPrimitiveSameThreadCalloutUint64Uint64.
		                    "If the primitive fails it continues, so we need to have an instruction to detect the end"
		                    endInstruction := cogit Stop ].


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
	
	cifArrayOfArgTypes := self newArrayWithSlots: 2. 													  "<---- Bad CIF! The argument should be just one, so the argumentTypes array should have only one element."
	memory storePointer: 0 ofObject: cifArrayOfArgTypes withValue: libFFIType.              
	memory storePointer: 1 ofObject: cifArrayOfArgTypes withValue: libFFIType.					"cif argumentTypes: { interpreter libFFI uint64 . interpreter libFFI uint64}. "
																														"It doesn't really matter how the argumentTypes array looks. The primitive first checks the 'nargs' field of the CIF (which always corresponds
																														to argumentTypes size), if it is not 1 then it will fail."	
	cifArgTypes := self newObjectWithSlots: 2. 
	memory storePointer: 0 ofObject: cifArgTypes withValue: cifArrayOfArgTypes.					"Array"
	memory storePointer: 1 ofObject: cifArgTypes withValue: (memory integerObjectOf: 0).     "offset"
	
	"The CIF itself:"
	cif := self newObjectWithSlots: 8.
	memory storePointer: 0 ofObject: cif withValue: (memory integerObjectOf: 16rB).    "address"
	memory storePointer: 1 ofObject: cif withValue: (memory nilObject).		 	         "libFFI"
	memory storePointer: 2 ofObject: cif withValue: (memory nilObject).						"abi"
	memory storePointer: 3 ofObject: cif withValue: (memory integerObjectOf: 2).			"nargs"						 "<---- Bad CIF! The argument should be just one!."
	memory storePointer: 4 ofObject: cif withValue: cifArgTypes.                    	"arg_types"
	memory storePointer: 5 ofObject: cif withValue: (memory integerObjectOf: 16rB).  	"rtype"
	memory storePointer: 6 ofObject: cif withValue: (memory nilObject).              	"bytes"
	memory storePointer: 7 ofObject: cif withValue: (memory nilObject).              	"flags"
	 
	
	cifExternalAddress := self newExternalAddress: cif.
	
	
	memory storePointer: 0 ofObject: tfExternalFunction withValue: functionExternalAddress.
	memory storePointer: 1 ofObject: tfExternalFunction withValue: tfFunctionDefinition.
	memory storePointer: 0 "HANDLE" ofObject: tfFunctionDefinition withValue: cifExternalAddress.

	
	self prepareStackForSendReceiver: memory nilObject arguments: {
			tfExternalFunction.
			(memory integerObjectOf: 8888).														
			 }.

	"self openMachineDebuggerAt: primitiveAddress."
		
	self runFrom: primitiveAddress until: endInstruction address.
	
]

{ #category : #'tests - primitiveGreaterOrEqual' }
VMJittedSpecializedPrimitiveTest >> testPrimitiveFFIShouldFailWithInvalidCifRtype [
	
	| primitiveAddress tfExternalFunction functionAddress functionExternalAddress tfFunctionDefinition cif cifExternalAddress libFFIType cifArrayOfArgTypes cifArgTypes endInstruction |

	interpreter libFFI: LibFFI new.
	interpreter libFFI interpreter: interpreter.
	
	functionAddress := self compile: [ cogit MoveR: Arg0Reg R: TempReg .cogit RetN: 0 ]. "mov rdi, rax. ret"

	primitiveAddress := self compile: [
		                    cogit objectRepresentation
			                    genPrimitiveSameThreadCalloutUint64Uint64.
		                    "If the primitive fails it continues, so we need to have an instruction to detect the end"
		                    endInstruction := cogit Stop ].


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
	memory storePointer: 0 ofObject: cifArgTypes withValue: cifArrayOfArgTypes.					"Array"
	memory storePointer: 1 ofObject: cifArgTypes withValue: (memory integerObjectOf: 0).     "offset"
	
	"The CIF itself:"
	cif := self newObjectWithSlots: 8.
	memory storePointer: 0 ofObject: cif withValue: (memory integerObjectOf: 1).       "address"
	memory storePointer: 1 ofObject: cif withValue: (memory nilObject).		 	         "libFFI"
	memory storePointer: 2 ofObject: cif withValue: (memory nilObject).						"abi"
	memory storePointer: 3 ofObject: cif withValue: (memory integerObjectOf: 1).			"nargs"
	memory storePointer: 4 ofObject: cif withValue: cifArgTypes.                    	"arg_types"
	memory storePointer: 5 ofObject: cif withValue: (memory integerObjectOf: 16rA).  	"rtype"       "<---- Bad CIF! The returnType should be just 11 = ."
	memory storePointer: 6 ofObject: cif withValue: (memory nilObject).              	"bytes"
	memory storePointer: 7 ofObject: cif withValue: (memory nilObject).              	"flags"
	 
	
	cifExternalAddress := self newExternalAddress: cif.
	
	
	memory storePointer: 0 ofObject: tfExternalFunction withValue: functionExternalAddress.
	memory storePointer: 1 ofObject: tfExternalFunction withValue: tfFunctionDefinition.
	memory storePointer: 0 "HANDLE" ofObject: tfFunctionDefinition withValue: cifExternalAddress.

	
	self prepareStackForSendReceiver: memory nilObject arguments: {
			tfExternalFunction.
			(memory integerObjectOf: 8888).														
			 }.

	"We assert that the primitive failed so it will not return, so it will arrive to the endInstruction"
		
	self runFrom: primitiveAddress until: endInstruction address.
	
]

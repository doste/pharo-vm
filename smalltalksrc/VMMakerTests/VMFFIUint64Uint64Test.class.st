Class {
	#name : 'VMFFIUint64Uint64Test',
	#superclass : 'VMAbstractFFITest',
	#category : 'VMMakerTests',
	#package : 'VMMakerTests'
}

{ #category : 'tests' }
VMFFIUint64Uint64Test >> testFunctionReturnsSameValue [
	| tfExternalFunction anUint64 |
	tfExternalFunction := self 
		createExternalFunctionFor:  [ :anArgument | anArgument ] 
		withArgumentTypes: { interpreter libFFI uint64} 
		withReturnType: interpreter libFFI uint64.
	
	anUint64 := memory integerObjectOf: 77777.

	interpreter push: memory nilObject.
	interpreter push: tfExternalFunction.
	interpreter push: anUint64. 

	interpreter argumentCount: 2.
	interpreter primitiveSameThreadCalloutUint64Uint64.
	
	self assert: interpreter successful.
	self assert: interpreter stackTop equals: anUint64
	
]

{ #category : 'tests' }
VMFFIUint64Uint64Test >> testPrimitiveRejectsIntegerNegativeArgument [
	| tfExternalFunction  |
	tfExternalFunction := self 
		createExternalFunctionFor:  [ :anArgument | self fail. ] 
		withArgumentTypes: { interpreter libFFI uint64} 
		withReturnType: interpreter libFFI uint64.
	
	interpreter push: memory nilObject.
	interpreter push: tfExternalFunction.
	interpreter push: (memory integerObjectOf: -42). 

	interpreter argumentCount: 2.
	interpreter primitiveSameThreadCalloutUint64Uint64.
	
	self deny: interpreter successful
]

{ #category : 'tests' }
VMFFIUint64Uint64Test >> testPrimitiveRejectsNonIntegerArgument [
	| tfExternalFunction  |
	tfExternalFunction := self 
		createExternalFunctionFor:  [ :anArgument | self fail. ] 
		withArgumentTypes: { interpreter libFFI uint64} 
		withReturnType: interpreter libFFI uint64.
	
	interpreter push: memory nilObject.
	interpreter push: tfExternalFunction.
	interpreter push: memory trueObject. 

	interpreter argumentCount: 2.
	interpreter primitiveSameThreadCalloutUint64Uint64.
	
	self deny: interpreter successful
]

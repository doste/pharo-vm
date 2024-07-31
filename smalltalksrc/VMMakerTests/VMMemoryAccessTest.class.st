Class {
	#name : 'VMMemoryAccessTest',
	#superclass : 'VMSpurInitializedOldSpaceTest',
	#category : 'VMMakerTests-MemoryTests',
	#package : 'VMMakerTests',
	#tag : 'MemoryTests'
}

{ #category : 'tests' }
VMMemoryAccessTest >> testSigned32BitInteger [

	self
		assert: (memory signed32BitValueOf: (memory integerObjectOf: -1))
		equals: -1.
	self
		assert: (memory integerValueOf: (memory signed32BitIntegerFor: -1))
		equals: -1.
	self
		assert:
		(memory signed32BitValueOf: (memory signed32BitIntegerFor: -1))
		equals: -1.

	self
		assert:
		(memory signed32BitValueOf:
			 (memory signed32BitIntegerFor: 2147483647))
		equals: 2147483647.
	self
		assert: (memory signed32BitValueOf:
				 (memory signed32BitIntegerFor: -2147483647))
		equals: -2147483647.
	self
		assert: (memory signed32BitValueOf:
				 (memory signed32BitIntegerFor: -2147483648))
		equals: -2147483648.
	self
		assert: (memory signed32BitValueOf:
				 (memory signed32BitIntegerFor: -2147483649))
		equals: 2147483647
]

"
Please describe the package using the class comment of the included manifest class. The manifest class also includes other additional metadata for the package. These meta data are used by other tools such as the SmalllintManifestChecker and the critics Browser
"
Class {
	#name : #ManifestVMMaker,
	#superclass : #PackageManifest,
	#category : #'VMMaker-Manifest'
}

{ #category : #'code-critics' }
ManifestVMMaker class >> ruleUtilityMethodsRuleV1FalsePositive [

	<ignoreForCoverage>
	^ #(#(#(#RGMethodDefinition #(#StackToRegisterMappingCogit #needsFrameIfExtBGT2: #false)) #'2024-06-06T14:33:08.917674+02:00') )
]

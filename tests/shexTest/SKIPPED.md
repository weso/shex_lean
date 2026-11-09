# Skipped tests

`tests/tools/gen_shextest.py` writes this file.
The 2025 formalism, or the translation, cannot express these tests.

| Test | Reason |
|---|---|
| `1inversedot_fail-empty` | inverse triple constraints |
| `1inversedot_fail-missing` | inverse triple constraints |
| `1inversedot_pass-noOthers` | inverse triple constraints |
| `1inversedot_pass-over_lexicallyEarlier` | inverse triple constraints |
| `1inversedot_pass-over_lexicallyLater` | inverse triple constraints |
| `1inversedotIRI_fail-Bnode` | inverse triple constraints |
| `1inversedotIRI_pass` | inverse triple constraints |
| `1inversedotBNODE_pass` | inverse triple constraints |
| `1inversedotBNODE_fail-Iri` | inverse triple constraints |
| `1inversedotRef1_pass` | inverse triple constraints |
| `1inversedotRef1_fail` | inverse triple constraints |
| `1inversedotCard2_pass` | inverse triple constraints |
| `1inversedotCard2_fail` | inverse triple constraints |
| `1inversedotValueSet_pass` | inverse triple constraints |
| `1inversedotValueSet_fail-Bnode` | inverse triple constraints |
| `1inversedotValueSet_fail-Iri` | inverse triple constraints |
| `1inversedotLITERAL_fail` | inverse triple constraints |
| `inverseBnodeCoref_pass` | inverse triple constraints |
| `inverseBnodeCoref_fail-noP2` | inverse triple constraints |
| `inverseBnodeCoref_fail-noX` | inverse triple constraints |
| `inverseClosedDiscrim_pass` | inverse triple constraints |
| `inverseClosedDiscrim_fail` | inverse triple constraints |
| `1dotExtendsInverse_pass` | inverse triple constraints |
| `1dotExtendsInverse_fail` | inverse triple constraints |
| `1dotInverseExtends_pass` | inverse triple constraints |
| `1dotInverseExtends_fail` | inverse triple constraints |
| `1datatypePattern_fail` | the pattern facet |
| `1datatypePattern_pass` | the pattern facet |
| `1datatype_langString` | a literal with a language tag in the data |
| `1datatype_wrongDatatype` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1datatype_pass` | a literal with the datatype <http://a.example/dt1> in the data |
| `1datatypelangString_pass` | a literal with a language tag in the data |
| `integer-n1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedByte> in the data |
| `integer-0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#int> in the data |
| `integer-1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedByte> in the data |
| `integer-p1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedInt> in the data |
| `integer-empty_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#nonNegativeInteger> in the data |
| `integer-n1.0_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `integer-p1.0_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedLong> in the data |
| `integer-1E0_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#byte> in the data |
| `integer-NaN_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `integer-INF_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `decimal-n1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `decimal-0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#positiveInteger> in the data |
| `decimal-1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#long> in the data |
| `decimal-p1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedLong> in the data |
| `decimal-n1.0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#nonPositiveInteger> in the data |
| `decimal-p1.0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedInt> in the data |
| `decimal-empty_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#nonPositiveInteger> in the data |
| `decimal-1E0_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `decimal-NaN_fail` | an xsd:integer literal that is not canonical in the data |
| `decimal-INF_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `float-n1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `float-0_pass` | an xsd:integer literal that is not canonical in the data |
| `float-1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `float-p1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#short> in the data |
| `float-n1.0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedLong> in the data |
| `float-p1.0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedLong> in the data |
| `float-1elowercase0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `float-1E0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `float-NaN_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `float-INF_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `float-nINF_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#byte> in the data |
| `float-empty_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `float-pINF_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#short> in the data |
| `double-n1_pass` | an xsd:integer literal that is not canonical in the data |
| `double-0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedByte> in the data |
| `double-1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `double-p1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `double-n1.0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `double-p1.0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `double-1E0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#nonNegativeInteger> in the data |
| `double-1e0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `double-NaN_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#byte> in the data |
| `double-INF_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `double-nINF_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `double-empty_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#byte> in the data |
| `double-pINF_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedShort> in the data |
| `nonPositiveInteger-n1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedByte> in the data |
| `nonPositiveInteger-0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `nonPositiveInteger-p0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `nonPositiveInteger-n0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `nonPositiveInteger-1_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#nonNegativeInteger> in the data |
| `nonPositiveInteger-p1_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#byte> in the data |
| `nonPositiveInteger-1a_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedByte> in the data |
| `nonPositiveInteger-a1_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `negativeInteger-n1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `negativeInteger-0_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `negativeInteger-p0_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `negativeInteger-n0_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#long> in the data |
| `negativeInteger-1_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `long-n1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `long-0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedByte> in the data |
| `long-1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `long-p1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#byte> in the data |
| `int-n1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#short> in the data |
| `int-0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#int> in the data |
| `int-1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#short> in the data |
| `int-p1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `short-n32768_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedLong> in the data |
| `short-0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedByte> in the data |
| `short-32767_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedLong> in the data |
| `short-n32769_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `short-32768_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#long> in the data |
| `byte-n128_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#int> in the data |
| `byte-0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#byte> in the data |
| `byte-127_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#long> in the data |
| `byte-empty_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `byte-n129_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#nonNegativeInteger> in the data |
| `byte-128_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `nonNegativeInteger-0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#int> in the data |
| `nonNegativeInteger-n0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `nonNegativeInteger-p0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#nonNegativeInteger> in the data |
| `nonNegativeInteger-1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `nonNegativeInteger-p1_pass` | an xsd:integer literal that is not canonical in the data |
| `nonNegativeInteger-n1_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#byte> in the data |
| `unsignedLong-0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#nonPositiveInteger> in the data |
| `unsignedLong-1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedInt> in the data |
| `unsignedLong-n1_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `unsignedInt-0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#long> in the data |
| `unsignedInt-1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedByte> in the data |
| `unsignedInt-n1_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#byte> in the data |
| `unsignedShort-0_pass` | an xsd:integer literal that is not canonical in the data |
| `unsignedShort-65535_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#byte> in the data |
| `unsignedShort-n1_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#nonNegativeInteger> in the data |
| `unsignedShort-65536_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `unsignedByte-0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `unsignedByte-255_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `unsignedByte-n1_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#nonNegativeInteger> in the data |
| `unsignedByte-256_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#negativeInteger> in the data |
| `positiveInteger-1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#byte> in the data |
| `positiveInteger-n1_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `positiveInteger-0_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `string-empty_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedInt> in the data |
| `string-a_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedShort> in the data |
| `string-0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `boolean-true_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `boolean-false_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#positiveInteger> in the data |
| `boolean-0_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `boolean-1_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#unsignedInt> in the data |
| `boolean-empty_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `boolean-TRUE_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#negativeInteger> in the data |
| `boolean-FALSE_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `boolean-tRuE_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `boolean-fAlSe_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#nonPositiveInteger> in the data |
| `boolean-n1_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#long> in the data |
| `boolean-2_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#byte> in the data |
| `boolean-10_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `boolean-01_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#nonNegativeInteger> in the data |
| `dateTime-dt_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `dateTime-empty_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#byte> in the data |
| `dateTime-dT_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `dateTime-d_fail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `3circRefS123` | imports |
| `1iriRef1_pass-iri` | a shape reference as a shape expression |
| `1iriRef1_fail-bnode` | a shape reference as a shape expression |
| `1bnodeRef1_fail-iri` | a shape reference as a shape expression |
| `1bnodeRef1_pass-bnode` | a shape reference as a shape expression |
| `1val1INTEGER_00` | an xsd:integer literal that is not canonical in the data |
| `1val1DECIMAL_00` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1val1DECIMAL_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1val1DOUBLE_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1val1DOUBLE_0_0e0` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1val1DOUBLElowercase_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1val1DOUBLElowercase_fail-0E0` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1val1DOUBLElowercase_0_0e0` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1val1LANGTAG_pass` | a literal with a language tag in the data |
| `1val1LANGTAG_LabLTen` | a literal with a language tag in the data |
| `1val1LANGTAG_LabLTen-fr-jura` | rudof cannot read the data (DataError) |
| `1val1LANGTAG_LaLTen-fr` | a literal with a language tag in the data |
| `1val1IRIREFDatatype_pass` | a literal with the datatype <http://a.example/bloodType> in the data |
| `1val1IRIREFDatatype_LabDTbloodType999` | a literal with the datatype <http://a.example/bloodType999> in the data |
| `1val1IRIREFDatatype_LaDTbloodType` | a literal with the datatype <http://a.example/bloodType> in the data |
| `1val1true_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `1val1true_false` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `1val1false_pass` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `1val1false_true` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#boolean> in the data |
| `1datatypeLength_fail-wrongDatatype` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalFractiondigits_pass-decimal-short` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalFractiondigits_pass-decimal-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalFractiondigits_fail-decimal-long` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalFractiondigits_pass-decimal-equalLead` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalFractiondigits_fail-decimal-longLead` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalFractiondigits_pass-decimal-equalTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalFractiondigits_fail-decimal-longTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalFractiondigits_pass-decimal-equalLeadTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalFractiondigits_fail-decimal-longLeadTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalFractiondigits_fail-float-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1literalFractiondigits_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1literalFractiondigits_fail-malformedxsd_decimal-1_23ab` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalFractiondigits_fail-malformedxsd_decimal-1_2345ab` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalFractiondigits_fail-malformedxsd_integer-1_2345` | an xsd:integer literal that is not canonical in the data |
| `1literalTotaldigits_pass-decimal-short` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalTotaldigits_pass-decimal-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalTotaldigits_fail-decimal-long` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalTotaldigits_pass-decimal-equalLead` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalTotaldigits_fail-decimal-longLead` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalTotaldigits_pass-decimal-equalTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalTotaldigits_fail-decimal-longTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalTotaldigits_pass-decimal-equalLeadTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalTotaldigits_fail-decimal-longLeadTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalTotaldigits_pass-integer-equalLead` | an xsd:integer literal that is not canonical in the data |
| `1literalTotaldigits_fail-integer-longLead` | an xsd:integer literal that is not canonical in the data |
| `1literalTotaldigits_pass-integer-equalLeadTrail` | an xsd:integer literal that is not canonical in the data |
| `1literalTotaldigits_fail-integer-longLeadTrail` | an xsd:integer literal that is not canonical in the data |
| `1literalTotaldigits_pass-byte-short` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#byte> in the data |
| `1literalTotaldigits_pass-byte-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#byte> in the data |
| `1literalTotaldigits_fail-byte-long` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#byte> in the data |
| `1literalTotaldigits_fail-float-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1literalTotaldigits_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1literalTotaldigits_fail-malformedxsd_decimal-1_23ab` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalTotaldigits_fail-malformedxsd_decimal-1_2345ab` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1literalTotaldigits_fail-malformedxsd_integer-1_2345` | an xsd:integer literal that is not canonical in the data |
| `1floatMininclusiveINTEGER_fail-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveINTEGER_pass-equalLead` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveINTEGER_pass-equalTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveINTEGER_pass-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1integerMininclusiveINTEGER_pass-equalLead` | an xsd:integer literal that is not canonical in the data |
| `1floatMininclusiveINTEGERLead_pass-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1integerMininclusiveINTEGERLead_pass-integer-equalLead` | an xsd:integer literal that is not canonical in the data |
| `1integerMininclusiveDECIMALLeadTrail_pass-integer-equalLead` | an xsd:integer literal that is not canonical in the data |
| `1integerMininclusiveDECIMALintLeadTrail_pass-integer-equalLead` | an xsd:integer literal that is not canonical in the data |
| `1integerMininclusiveDOUBLELeadTrail_pass-integer-equalLead` | an xsd:integer literal that is not canonical in the data |
| `1integerMininclusiveDOUBLEintLeadTrail_pass-integer-equalLead` | an xsd:integer literal that is not canonical in the data |
| `1integerMininclusiveINTEGER_fail-decimal-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1integerMininclusiveINTEGER_fail-float-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1integerMininclusiveINTEGER_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1integerMininclusiveINTEGER_fail-dateTime-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#dateTime> in the data |
| `1integerMininclusiveINTEGER_fail-byte-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#byte> in the data |
| `1decimalMininclusiveINTEGER_fail-decimal-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveINTEGER_pass-decimal-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveINTEGERLead_fail-decimal-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveINTEGERLead_pass-decimal-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDECIMAL_fail-decimal-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDECIMAL_pass-decimal-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDECIMAL_pass-decimal-equalLeadTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDECIMAL_pass-decimal-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDECIMALLeadTrail_fail-decimal-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDECIMALLeadTrail_pass-decimal-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDECIMALLeadTrail_pass-decimal-equalLeadTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDECIMALLeadTrail_pass-decimal-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDECIMALintLeadTrail_fail-decimal-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDECIMALintLeadTrail_pass-decimal-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDOUBLE_fail-decimal-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDOUBLE_pass-decimal-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDOUBLE_pass-decimal-equalLeadTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDOUBLELeadTrail_fail-decimal-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDOUBLELeadTrail_pass-decimal-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDOUBLELeadTrail_pass-decimal-equalLeadTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDOUBLELeadTrail_pass-decimal-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDOUBLEintLeadTrail_fail-decimal-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDOUBLEintLeadTrail_pass-decimal-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMininclusiveDECIMAL_fail-float-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1decimalMininclusiveDECIMAL_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1floatMininclusiveINTEGERLead_fail-float-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveINTEGERLead_pass-float-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveDECIMAL_pass-float-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveDECIMAL_pass-float-equalLeadTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveDECIMALLeadTrail_fail-float-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveDECIMALLeadTrail_pass-float-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveDECIMALLeadTrail_pass-float-equalLeadTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveDECIMALLeadTrail_pass-float-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveDECIMALintLeadTrail_fail-float-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveDECIMALintLeadTrail_pass-float-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveDOUBLE_pass-float-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveDOUBLE_pass-float-equalLeadTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveDOUBLELeadTrail_fail-float-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveDOUBLELeadTrail_pass-float-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveDOUBLELeadTrail_pass-float-equalLeadTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveDOUBLELeadTrail_pass-float-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveDOUBLEintLeadTrail_fail-float-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMininclusiveDOUBLEintLeadTrail_pass-float-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1doubleMininclusiveINTEGERLead_fail-double-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMininclusiveINTEGERLead_pass-double-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMininclusiveDECIMAL_pass-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMininclusiveDECIMAL_pass-double-equalLeadTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMininclusiveDECIMALLeadTrail_fail-double-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMininclusiveDECIMALLeadTrail_pass-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMininclusiveDECIMALLeadTrail_pass-double-equalLeadTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMininclusiveDECIMALLeadTrail_pass-double-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMininclusiveDECIMALintLeadTrail_fail-double-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMininclusiveDECIMALintLeadTrail_pass-double-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMininclusiveDOUBLE_pass-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMininclusiveDOUBLE_pass-double-equalLeadTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMininclusiveDOUBLELeadTrail_fail-double-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMininclusiveDOUBLELeadTrail_pass-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMininclusiveDOUBLELeadTrail_pass-double-equalLeadTrail` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMininclusiveDOUBLELeadTrail_pass-double-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMininclusiveDOUBLEintLeadTrail_fail-double-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMininclusiveDOUBLEintLeadTrail_pass-double-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1decimalMinexclusiveINTEGER_fail-decimal-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMinexclusiveINTEGER_pass-decimal-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMinexclusiveDECIMAL_fail-decimal-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMinexclusiveDECIMAL_fail-decimal-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMinexclusiveDECIMAL_pass-decimal-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMinexclusiveDOUBLE_fail-decimal-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMinexclusiveDOUBLE_fail-decimal-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMinexclusiveDOUBLE_pass-decimal-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMinexclusiveDECIMAL_fail-float-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1decimalMinexclusiveDECIMAL_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1floatMinexclusiveINTEGER_fail-float-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMinexclusiveINTEGER_pass-float-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMinexclusiveDECIMAL_fail-float-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMinexclusiveDECIMAL_fail-float-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMinexclusiveDECIMAL_pass-float-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMinexclusiveDOUBLE_fail-float-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMinexclusiveDOUBLE_fail-float-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMinexclusiveDOUBLE_pass-float-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1doubleMinexclusiveINTEGER_fail-double-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMinexclusiveINTEGER_pass-double-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMinexclusiveDECIMAL_fail-double-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMinexclusiveDECIMAL_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMinexclusiveDECIMAL_pass-double-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMinexclusiveDOUBLE_fail-double-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMinexclusiveDOUBLE_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMinexclusiveDOUBLE_pass-double-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMinexclusiveDECIMAL_fail-float-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1decimalMaxinclusiveINTEGER_pass-decimal-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMaxinclusiveINTEGER_fail-decimal-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMaxinclusiveDECIMAL_pass-decimal-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMaxinclusiveDECIMAL_pass-decimal-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMaxinclusiveDECIMAL_fail-decimal-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMaxinclusiveDOUBLE_pass-decimal-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMaxinclusiveDOUBLE_pass-decimal-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMaxinclusiveDOUBLE_fail-decimal-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMaxinclusiveDECIMAL_fail-float-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1decimalMaxinclusiveDECIMAL_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1floatMaxinclusiveINTEGER_pass-float-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMaxinclusiveINTEGER_fail-float-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMaxinclusiveDECIMAL_pass-float-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMaxinclusiveDECIMAL_pass-float-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMaxinclusiveDECIMAL_fail-float-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMaxinclusiveDOUBLE_pass-float-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMaxinclusiveDOUBLE_pass-float-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMaxinclusiveDOUBLE_fail-float-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1doubleMaxinclusiveINTEGER_pass-double-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxinclusiveINTEGER_fail-double-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxinclusiveDECIMAL_pass-double-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxinclusiveDECIMAL_pass-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxinclusiveDECIMAL_fail-double-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxinclusiveDOUBLE_pass-double-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxinclusiveDOUBLE_pass-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxinclusiveDOUBLE_fail-double-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxinclusiveDECIMAL_fail-float-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1decimalMaxexclusiveINTEGER_pass-decimal-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMaxexclusiveINTEGER_fail-decimal-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMaxexclusiveDECIMAL_pass-decimal-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMaxexclusiveDECIMAL_fail-decimal-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMaxexclusiveDECIMAL_fail-decimal-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMaxexclusiveDOUBLE_pass-decimal-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMaxexclusiveDOUBLE_fail-decimal-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMaxexclusiveDOUBLE_fail-decimal-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#decimal> in the data |
| `1decimalMaxexclusiveDECIMAL_fail-float-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1decimalMaxexclusiveDECIMAL_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1decimalMaxexclusivexsd-byte_fail-byte-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#byte> in the data |
| `1floatMaxexclusiveINTEGER_pass-float-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMaxexclusiveINTEGER_fail-float-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMaxexclusiveDECIMAL_pass-float-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMaxexclusiveDECIMAL_fail-float-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMaxexclusiveDOUBLE_pass-float-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1floatMaxexclusiveDOUBLE_fail-float-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#float> in the data |
| `1doubleMaxexclusiveINTEGER_pass-double-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxexclusiveINTEGER_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxexclusiveINTEGER_fail-double-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxexclusiveINTEGERLead_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxexclusiveDECIMAL_pass-double-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxexclusiveDECIMAL_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxexclusiveDECIMAL_fail-double-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxexclusiveDECIMALLeadTrail_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxexclusiveDECIMALint_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxexclusiveDECIMALintLeadTrail_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxexclusiveDOUBLE_pass-double-low` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxexclusiveDOUBLE_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxexclusiveDOUBLE_fail-double-high` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxexclusiveDOUBLELeadTrail_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxexclusiveDOUBLEint_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1doubleMaxexclusiveDOUBLEintLeadTrail_fail-double-equal` | a literal with the datatype <http://www.w3.org/2001/XMLSchema#double> in the data |
| `1iriRefLength1_fail-iri-short` | a shape reference as a shape expression |
| `1iriRefLength1_pass-iri-equal` | a shape reference as a shape expression |
| `1iriRefLength1_fail-iri-long` | a shape reference as a shape expression |
| `1iriRefLength1_fail-lit-equal` | a shape reference as a shape expression |
| `1iriRefLength1_fail-bnode-equal` | a shape reference as a shape expression |
| `1literalPattern_pass-lit-match` | the pattern facet |
| `1literalPattern_fail-lit-short` | the pattern facet |
| `1literalPattern_fail-ab` | the pattern facet |
| `1literalPattern_fail-cd` | the pattern facet |
| `1literalPatterni_pass-lit-match` | the pattern facet |
| `1literalPatterni_pass-lit-BC` | the pattern facet |
| `1literalPatterni_pass-lit-blowercaseC` | the pattern facet |
| `1literalPattern_pass-lit-into` | the pattern facet |
| `1literalPattern19_fail-iri-match` | the pattern facet |
| `1literalPattern_fail-bnode-match` | the pattern facet |
| `1literalPattern_with_all_controls_pass` | the pattern facet |
| `1literalPattern_with_all_controls_fail` | the pattern facet |
| `1literalPattern_with_all_punctuation_pass` | the pattern facet |
| `1literalPattern_with_all_punctuation_fail` | the pattern facet |
| `1literalPattern_with_ascii_boundaries_pass` | the pattern facet |
| `1literalPattern_with_ascii_boundaries_fail` | the pattern facet |
| `1literalPattern_with_UTF8_boundaries_pass` | the pattern facet |
| `1literalPattern_with_UTF8_boundaries_fail` | the pattern facet |
| `1literalPattern_with_REGEXP_escapes_pass` | the pattern facet |
| `1literalPattern_with_REGEXP_escapes_fail` | the pattern facet |
| `1literalPattern_with_REGEXP_escapes_fail_escaped` | the pattern facet |
| `1literalPattern_with_REGEXP_escapes_escaped_pass` | the pattern facet |
| `1literalPattern_with_REGEXP_escapes_escaped_fail_escapes` | the pattern facet |
| `1literalPattern_with_REGEXP_escapes_escaped_fail_escapes_bare` | the pattern facet |
| `1literalPattern_with_REGEXP_escapes_bare_pass` | the pattern facet |
| `1literalPattern_with_REGEXP_escapes_bare_fail_escaped` | the pattern facet |
| `1literalPattern_with_REGEXP_escapes_pass_bare` | the pattern facet |
| `1literalPattern_with_REGEXP_escapes_bare_pass_escapes` | the pattern facet |
| `1literalPatternEnd_fail-litEnd` | the pattern facet |
| `1literalPatternDollar_pass-litDollar-match` | the pattern facet |
| `1literalPattern_pass-StartlitEnd-match` | the pattern facet |
| `1literalStartPatternEnd_CarrotbcDollar` | the pattern facet |
| `1literalCarrotPatternDollar_pass-bc` | the pattern facet |
| `1literalCarrotPatternDollar_pass-CarrotbcDollar` | the pattern facet |
| `1literalPatternabEnd_fail-bnode-match` | the pattern facet |
| `1literalStartPattern_pass-bc` | the pattern facet |
| `1literalStartPattern_fail-CarrotbcDollar` | the pattern facet |
| `1literalPatternEnd_pass-bc` | the pattern facet |
| `1literalPatternEnd_pass-CarrotbcDollar` | the pattern facet |
| `1literalPattern_pass-bcDollar` | the pattern facet |
| `1literalStarPatternEnd_pass-bc` | the pattern facet |
| `1literalPattern_pass-CarrotbcDollar` | the pattern facet |
| `1literalPattern_with_all_meta_pass` | the pattern facet |
| `1literalPattern_with_all_meta_pass-NA` | the pattern facet |
| `1iriPattern_pass-iri-match` | the pattern facet |
| `1iriPattern_fail-iri-short` | the pattern facet |
| `1iriPattern_fail-iri-long` | the pattern facet |
| `1iriPattern_fail-lit-match` | the pattern facet |
| `1iriPattern_fail-bnode-match` | the pattern facet |
| `1bnodePattern_pass-bnode-match` | the pattern facet |
| `1bnodePattern_fail-bnode-short` | the pattern facet |
| `1bnodePattern_fail-bnode-long` | the pattern facet |
| `1bnodePattern_fail-lit-match` | the pattern facet |
| `1bnodePattern_fail-iri-match` | the pattern facet |
| `1nonliteralPattern_pass-iri-match` | the pattern facet |
| `1nonliteralPattern_fail-iri-short` | the pattern facet |
| `1nonliteralPattern_pass-iri-long` | the pattern facet |
| `1nonliteralPattern_fail-lit-match` | the pattern facet |
| `1nonliteralPattern_pass-bnode-match` | the pattern facet |
| `1nonliteralPattern_fail-bnode-short` | the pattern facet |
| `1nonliteralPattern_pass-bnode-long` | the pattern facet |
| `1val1language_passLAtfr` | a literal with a language tag in the data |
| `1val1language_failLAtfr-be` | a literal with a language tag in the data |
| `1val1emptylanguageStem_passLAtfr` | a literal with a language tag in the data |
| `1val1emptylanguageStemMinuslanguage3_passLAtfr` | a literal with a language tag in the data |
| `1val1emptylanguageStemMinuslanguage3_failLAtfr-be` | a literal with a language tag in the data |
| `1val1emptylanguageStemMinuslanguage3_passLAtfr-be-fbcl` | rudof cannot read the data (DataError) |
| `1val1emptylanguageStemMinuslanguageStem3_LAtfr` | a literal with a language tag in the data |
| `1val1emptylanguageStemMinuslanguageStem3_failLAtfr-be` | a literal with a language tag in the data |
| `1val1emptylanguageStemMinuslanguageStem3_LAtfr-be-fbcl` | rudof cannot read the data (DataError) |
| `1val1emptylanguageStemMinuslanguageStem3_LAtfrc` | a literal with a language tag in the data |
| `1val1languageStem_passLAtfr` | a literal with a language tag in the data |
| `1val1languageStem_failLAtfrc` | a literal with a language tag in the data |
| `1val1languageStem_passLAtfr-be` | a literal with a language tag in the data |
| `1val1languageStem_passLAtfr-be-fbcl` | rudof cannot read the data (DataError) |
| `1val1literallanguageStem_failLAtfr` | a literal with a language tag in the data |
| `1val1languageStemMinuslanguage3_passLAtfr` | a literal with a language tag in the data |
| `1val1languageStemMinuslanguage3_passLAtfr-FR` | a literal with a language tag in the data |
| `1val1literallanguageStemMinusliterallanguage3_failLAtfr-FR` | a literal with a language tag in the data |
| `1val1languageStemMinuslanguage3_failLAtfr-be` | a literal with a language tag in the data |
| `1val1literallanguageStemMinusliterallanguage3_failLAtfr-BE` | a literal with a language tag in the data |
| `1val1languageStemMinuslanguage3_failLAtfr-cd` | a literal with a language tag in the data |
| `1val1languageStemMinuslanguage3_failLAtfr-ch` | a literal with a language tag in the data |
| `1val1languageStemMinuslanguage3_passLAtfr-be-fbcl` | rudof cannot read the data (DataError) |
| `1val1languageStemMinuslanguageStem3_passLAtfr` | a literal with a language tag in the data |
| `1val1languageStemMinuslanguageStem3_LAtfrc` | a literal with a language tag in the data |
| `1val1languageStemMinuslanguageStem3_passLAtfr-FR` | a literal with a language tag in the data |
| `1val1languageStemMinuslanguageStem3_LAtfr-be` | a literal with a language tag in the data |
| `1val1languageStemMinuslanguageStem3_LAtfr-cd` | a literal with a language tag in the data |
| `1val1languageStemMinuslanguageStem3_LAtfr-ch` | a literal with a language tag in the data |
| `1val1languageStemMinuslanguageStem3_passLAtfr-bel` | a literal with a language tag in the data |
| `1val1languageStemMinuslanguageStem3_LAtfr-be-fbcl` | rudof cannot read the data (DataError) |
| `1dotRefAND3_failAll` | a shape reference as a shape expression |
| `1dotRefAND3_failShape2Shape3` | a shape reference as a shape expression |
| `1dotRefAND3_failShape1Shape3` | a shape reference as a shape expression |
| `1dotRefAND3_failShape1Shape2` | a shape reference as a shape expression |
| `1dotRefAND3_passShape1Shape2Shape3` | a shape reference as a shape expression |
| `1val1vExpr1AND1AND1Ref3_pass` | the pattern facet |
| `1val1vExpr1AND1AND1Ref3_failvc1` | the pattern facet |
| `1val1vExpr1AND1AND1Ref3_failvc2` | the pattern facet |
| `1val1vExpr1AND1AND1Ref3_failvc3` | the pattern facet |
| `1val1vExprRefAND3_pass` | the pattern facet |
| `1val1vExprRefAND3_failvc3` | the pattern facet |
| `1val1vExprRefAND3_failvc2` | the pattern facet |
| `1val1vExprRefAND3_failvc1` | the pattern facet |
| `1val1vExprAND3_pass` | the pattern facet |
| `1val1vExprAND3_failvc1` | the pattern facet |
| `1val1vExprAND3_failvc2` | the pattern facet |
| `1val1vExprAND3_failvc3` | the pattern facet |
| `refBNodeORrefIRI_ReflexiveIRI` | a shape reference as a shape expression |
| `refBNodeORrefIRI_ReflexiveShortIRI` | a shape reference as a shape expression |
| `refBNodeORrefIRI_IntoReflexiveIRI` | a shape reference as a shape expression |
| `refBNodeORrefIRI_IntoReflexiveBNode` | a shape reference as a shape expression |
| `refBNodeORrefIRI_CyclicIRI_IRI` | a shape reference as a shape expression |
| `refBNodeORrefIRI_CyclicIRI_BNode` | a shape reference as a shape expression |
| `refBNodeORrefIRI_CyclicIRI_ShortIRI` | a shape reference as a shape expression |
| `1dotRefOR3_fail` | a shape reference as a shape expression |
| `1dotRefOR3_passShape1` | a shape reference as a shape expression |
| `1dotRefOR3_passShape2` | a shape reference as a shape expression |
| `1dotRefOR3_passShape3` | a shape reference as a shape expression |
| `1dotRefOR3_passShape1Shape2Shape3` | a shape reference as a shape expression |
| `1val1vExpr1OR1OR1Ref3_fail` | the pattern facet |
| `1val1vExpr1OR1OR1Ref3_passvc1` | the pattern facet |
| `1val1vExpr1OR1OR1Ref3_passvc2` | the pattern facet |
| `1val1vExpr1OR1OR1Ref3_passvc3` | the pattern facet |
| `1val1vExpr1OR1OR1Ref3_passvc1vc2vc3` | the pattern facet |
| `1val1vExprRefOR3_passvc1vc2vc3` | the pattern facet |
| `1val1vExprRefOR3_passvc3` | the pattern facet |
| `1val1vExprRefOR3_passvc2` | the pattern facet |
| `1val1vExprRefOR3_passvc1` | the pattern facet |
| `1val1vExprRefOR3_fail` | the pattern facet |
| `1val1vExprOR3_fail` | the pattern facet |
| `1val1vExprOR3_passvc1` | the pattern facet |
| `1val1vExprOR3_passvc2` | the pattern facet |
| `1val1vExprOR3_passvc3` | the pattern facet |
| `1val1vExprOR3_passvc1vc2vc3` | the pattern facet |
| `1val1vExpr1AND1OR1Ref3_pass-vc1vc2` | the pattern facet |
| `1val1vExpr1AND1OR1Ref3_pass-vc1vc2vc3` | the pattern facet |
| `1val1vExpr1AND1OR1Ref3_pass-vc1vc3` | the pattern facet |
| `1val1vExpr1AND1OR1Ref3_failvc1vc3` | the pattern facet |
| `1val1vExpr1AND1OR1Ref3_failvc2vc3` | the pattern facet |
| `1val1vExpr1AND1OR1Ref3_failvc1vc2vc3` | the pattern facet |
| `1val1vExpr1OR1AND1Ref3_pass-vc1` | the pattern facet |
| `1val1vExpr1OR1AND1Ref3_pass-vc1vc3` | the pattern facet |
| `1val1vExpr1OR1AND1Ref3_pass-vc2vc3` | the pattern facet |
| `1val1vExpr1OR1AND1Ref3_failvc1vc2` | the pattern facet |
| `1val1vExpr1OR1AND1Ref3_failvc1vc3` | the pattern facet |
| `1val1vExpr1OR1AND1Ref3_failvc1vc2vc3` | the pattern facet |
| `1val1vShapeANDRef3_pass` | the pattern facet |
| `FocusIRI2EachBnodeNested2EachIRIRef_pass` | the pattern facet |
| `FocusIRI2EachBnodeNested2EachIRIRef_fail` | the pattern facet |
| `startRefIRIREF_pass-noOthers` | the start shape |
| `startRefIRIREF_pass-others_lexicallyEarlier` | the start shape |
| `startRefIRIREF_fail-missing` | the start shape |
| `startRefbnode_pass-noOthers` | the start shape |
| `startRefbnode_fail-missing` | the start shape |
| `startInline_pass-noOthers` | the start shape |
| `startEqualSpaceInline_pass-noOthers` | the start shape |
| `startSpaceEqualInline_pass-noOthers` | the start shape |
| `startInline_fail-missing` | the start shape |
| `2EachInclude1_pass` | triple expression references |
| `2EachInclude1-after_pass` | triple expression references |
| `2OneInclude1_pass` | triple expression references |
| `2OneInclude1-after_pass` | triple expression references |
| `openEachInclude1dotclosecardPlusc1IRI_pass-b1c1d1aI1` | triple expression references |
| `openEachInclude1dotclosecardPlusc1IRI_pass-b2c2d2aI1` | triple expression references |
| `openEachInclude1dotclosecardPlusc1IRI_fail-b1c1d1a1` | triple expression references |
| `openEachInclude1dotclosecardPlusc1IRI_fail-aI1` | triple expression references |
| `openOneInclude1dotclosecardPlusc1IRI_pass-d1aI1` | triple expression references |
| `openOneInclude1dotclosecardPlusc1IRI_pass-b1c1d1aI1` | triple expression references |
| `openOneInclude1dotclosecardPlusc1IRI_fail-d1a1` | triple expression references |
| `openOneInclude1dotclosecardPlusc1IRI_fail-b1d1aI1` | triple expression references |
| `1inversedotAnnot3_pass` | inverse triple constraints |
| `1inversedotAnnot3_missing` | inverse triple constraints |
| `1dotCode1_pass` | semantic actions |
| `1dotNoCode1_pass` | semantic actions |
| `1inversedotCode1_pass` | semantic actions |
| `1dotCode3_pass` | semantic actions |
| `1dotNoCode3_pass` | semantic actions |
| `1dotCode3fail_abort` | semantic actions |
| `1dotCodeWithEscapes1_pass` | semantic actions |
| `1dotCode1_with_backslash_pass` | semantic actions |
| `1dotShapeCode1_pass` | semantic actions |
| `1dotShapeNoCode1_pass` | semantic actions |
| `open3EachdotcloseCode1-p1p2p3` | semantic actions |
| `1dotShapeCode1fail_abort` | semantic actions |
| `open3EachdotcloseCode1fail_abort` | semantic actions |
| `open2OnedotcloseCode1fail_abort` | semantic actions |
| `startCode1_pass` | semantic actions |
| `startNoCode1_pass` | semantic actions |
| `startCode1fail_abort` | semantic actions |
| `startCode1startRef_pass` | semantic actions |
| `startCode1startReffail_abort` | semantic actions |
| `startCode3_pass` | semantic actions |
| `startCode3fail_abort` | semantic actions |
| `2val1refvsCode_pass` | semantic actions |
| `open3Eachdotclosecard23Annot3Code2-p1p2p3X3` | semantic actions |
| `0focusIRI_empty_fail-bnodeFocusLabel` | a blank node focus that is not in the data |
| `0focusBNODE_empty` | a blank node focus that is not in the data |
| `focusdatatype_pass` | a literal with the datatype <http://a.example/bloodType> in the data |
| `focusdatatype_fail` | a literal with the datatype <http://a.example/bloodType999> in the data |
| `focusdatatype_pass-empty` | a literal with the datatype <http://a.example/bloodType> in the data |
| `focusdatatype_fail-empty` | a literal with the datatype <http://a.example/bloodType999> in the data |
| `1focusvsORdatatype_pass-dt` | a literal with the datatype <http://a.example/dt1> in the data |
| `1focusvsORdatatype_fail-dt` | a literal with the datatype <http://a.example/dt2> in the data |
| `focusNOTRefOR1dot_pass-inOR` | a shape reference as a shape expression |
| `focusNOTRefOR1dot_fail-inNOT` | a shape reference as a shape expression |
| `focusNOTRefOR1dot_pass-other` | a shape reference as a shape expression |
| `1focusPattern-dot_fail-iri-match` | the pattern facet |
| `1focusPattern-dot_fail-iri-short` | the pattern facet |
| `1focusPattern-dot_pass-iri-match` | the pattern facet |
| `1focusPattern-dot_fail-iri-long` | the pattern facet |
| `1focusPatternB-dot_fail-iri-match` | the pattern facet |
| `1focusPatternB-dot_fail-bnode-short` | the pattern facet |
| `1focusPatternB-dot_pass-bnode-match` | the pattern facet |
| `1focusPatternB-dot_pass-bnode-long` | the pattern facet |
| `1NOTRefOR1dot_pass-inOR` | a shape reference as a shape expression |
| `1NOTRefOR1dot_fail-inNOT` | a shape reference as a shape expression |
| `1NOTRefOR1dot_pass-other` | a shape reference as a shape expression |
| `shapeExtern_pass` | external shapes |
| `shapeExtern_fail` | external shapes |
| `shapeExternRef_pass` | external shapes |
| `shapeExternRef_fail` | external shapes |
| `1dot-relative_pass-short-shape` | relative shape labels |
| `1dot-relative_pass-relative-shape` | relative shape labels |
| `2RefS1-IS2` | imports |
| `2RefS1-IS2_fail-p2` | imports |
| `2RefS2-IS1` | imports |
| `2RefS1-Icirc` | imports |
| `2RefS1-Icirc_fail-p2` | imports |
| `3circRefS1-IS23` | imports |
| `3circRefS1-IS23_pass-p1` | imports |
| `3circRefS1-IS2-IS3` | imports |
| `3circRefS3-IS12` | imports |
| `3circRefS123-Icirc` | imports |
| `3circRefS1-Icirc` | imports |
| `3circRefS1-IS2-IS3-IS3` | imports |
| `start2RefS1-IstartS2` | imports |
| `start2RefS2-IstartS1` | imports |
| `1valExprRef-IV1_fail-lit-short` | imports |
| `1valExprRef-IV1_pass-lit-equal` | imports |
| `1valExprRefbnode-IV1_fail-lit-short` | imports |
| `1valExprRefbnode-IV1_pass-lit-equal` | imports |
| `2EachInclude1-IS2_pass` | imports |
| `1list0PlusDot-empty_pass` | imports |
| `1list0PlusDot-list_Iv1,Iv2,Iv3_pass` | imports |
| `1list0PlusDot-list_Iv1,Iv2,Lx_pass` | imports |
| `1list0PlusDot-manualList_Iv1,Iv2,Iv3_pass` | imports |
| `1list0PlusDot-manualList_extraArc_Iv1,Iv2,Iv3_fail` | imports |
| `1list0PlusDot-manualList_2firsts_Iv1,Iv2,Iv3_fail` | imports |
| `1list0PlusIri-empty_pass` | imports |
| `1list0PlusIri-list_Iv1,Iv2,Iv3_pass` | imports |
| `1list0PlusIri-list_Iv1,Iv2,Lx_fail` | imports |
| `1list1PlusIri-empty_pass` | imports |
| `1list1PlusIri-list_Iv1,Iv2,Iv3_pass` | imports |
| `1list1PlusIri-list_Iv1,Iv2,Lx_fail` | imports |
| `node_kind_example` | shape maps |
| `dependent_shape` | shape maps |
| `recursion_example` | shape maps |
| `ExtendsRepeatedP-pass` | a shape reference as a shape expression |
| `ExtendsRepeatedP-fail_vs` | a shape reference as a shape expression |
| `ANDAbstract-pass` | the pattern facet |
| `ANDAbstract-fail_G1pattern` | the pattern facet |
| `ANDAbstract-fail_pattern` | the pattern facet |
| `AND3G-pass` | the pattern facet |
| `AND3G-fail_G2pattern` | the pattern facet |
| `AND3G-fail_G1Bpattern` | the pattern facet |
| `ExtendAND3G-pass` | the pattern facet |
| `ExtendAND3G-fail_EXTG1` | the pattern facet |
| `ExtendAND3G-fail_ExtraP` | the pattern facet |
| `ExtendAND3G-fail_G3pattern` | the pattern facet |
| `ExtendAND3G-fail_EXTG1ANDG1` | the pattern facet |
| `ExtendAND3G-fail_EXTG1pattern` | the pattern facet |
| `ExtendAND3G-fail_G0` | the pattern facet |
| `Extend3G-pass` | the pattern facet |
| `Extend3G-t16` | the pattern facet |
| `Extend3G-t17` | the pattern facet |
| `Extend3G-t18` | the pattern facet |
| `Extend3G-t19` | the pattern facet |
| `Extend3G-t20` | the pattern facet |
| `Extend3G-t21` | the pattern facet |
| `ExtendANDExtend3GAND3G-pass` | the pattern facet |
| `ExtendANDExtend3GAND3G-t23` | the pattern facet |
| `ExtendANDExtend3GAND3G-t24` | the pattern facet |
| `ExtendANDExtend3GAND3G-t25` | the pattern facet |
| `ExtendANDExtend3GAND3G-t26` | the pattern facet |
| `ExtendANDExtend3GAND3G-t27` | the pattern facet |
| `ExtendANDExtend3GAND3G-t28` | the pattern facet |
| `ExtendANDExtend3GAND3G-t29` | the pattern facet |
| `ExtendANDExtend3GAND3G-t30` | the pattern facet |
| `ExtendANDExtend3GAND3G-t31` | the pattern facet |
| `ExtendANDExtend3GAND3G-t32` | the pattern facet |
| `ExtendANDExtend3GAND3G-t33` | the pattern facet |
| `ExtendANDExtend3GAND3G-t34` | the pattern facet |
| `ExtendANDExtend3GAND3G-t35` | the pattern facet |
| `vitals-RESTRICTS-pass_lie-Observation` | an extendable label whose definition is not a shape |
| `vitals-RESTRICTS-pass_lie-Vital` | an extendable label whose definition is not a shape |
| `vitals-RESTRICTS-pass_lie-BP` | an extendable label whose definition is not a shape |
| `vitals-RESTRICTS-pass_lie-PostureVital` | an extendable label whose definition is not a shape |
| `vitals-RESTRICTS-pass_lie-ReclinedVital` | an extendable label whose definition is not a shape |
| `vitals-RESTRICTS-pass_lie-PostureBP` | an extendable label whose definition is not a shape |
| `vitals-RESTRICTS-pass_lie-ReclinedBP` | an extendable label whose definition is not a shape |
| `vitals-RESTRICTS-pass_lie-Posture` | an extendable label whose definition is not a shape |
| `vitals-RESTRICTS-pass_lie-Reclined` | an extendable label whose definition is not a shape |
| `vitals-RESTRICTS-pass_sit-Observation` | an extendable label whose definition is not a shape |
| `vitals-RESTRICTS-pass_sit-Vital` | an extendable label whose definition is not a shape |
| `vitals-RESTRICTS-pass_sit-BP` | an extendable label whose definition is not a shape |
| `vitals-RESTRICTS-pass_sit-PostureVital` | an extendable label whose definition is not a shape |
| `vitals-RESTRICTS-fail_sit-ReclinedVital` | an extendable label whose definition is not a shape |
| `vitals-RESTRICTS-pass_sit-PostureBP` | an extendable label whose definition is not a shape |
| `vitals-RESTRICTS-fail_sit-ReclinedBP` | an extendable label whose definition is not a shape |
| `vitals-RESTRICTS-pass_sit-Posture` | an extendable label whose definition is not a shape |
| `vitals-RESTRICTS-fail_sit-Reclined` | an extendable label whose definition is not a shape |
| `extends-closed-or-each-each_pass-each-1` | an extendable label whose definition is not a shape |
| `extends-closed-or-each-each_pass-each-2` | an extendable label whose definition is not a shape |
| `extends-closed-or-each-each_fail-cross-each` | an extendable label whose definition is not a shape |
| `extends-open-or-each-each_pass-cross-each` | an extendable label whose definition is not a shape |
| `extends-abstract-or_fail-via-X` | a shape reference as a shape expression |
| `extends-abstract-or_fail-X-and-A` | a shape reference as a shape expression |
| `extends-abstract-or_pass-via-A` | a shape reference as a shape expression |
| `extends-abstract-or_pass-all` | a shape reference as a shape expression |
| `extends-abstract-or_pass-D-via-X` | a shape reference as a shape expression |

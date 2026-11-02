# A machine-checked round trip for Lean's `Float` printer

matthiasgoergens/lean4#10 gives `Float.toString` a logical model: the shortest decimal that reads back to the same double, laid out as Python's `repr` does.  This repository proves in Lean, against Lean's own `Float.Model`, that the digits this printer chooses do read back to the same double.

The main theorem, `FloatRoundtrip.floatOfScientific_printedDigits` in `FloatRoundtrip/FastPath.lean`: for every finite nonzero `x : Float`, reading the printed digits `c` and exponent `q` back with `Float.ofScientific`, and negating if `x` is negative, gives `x`.  `Float.ofScientific` is what Lean uses for float literals and what matthiasgoergens/lean4#9's `String.toFloat?` calls; the theorem covers its fast path (exact doubles multiplied or divided when `c < 2^53` and `|q| ≤ 22`) as well as its exact path through the model.  `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`.

The printer's definitions are copied unchanged from matthiasgoergens/lean4#10 into `FloatRoundtrip/Print.lean`, apart from the namespace.  `Float.Model` in Lean v4.36.0-rc2, which this builds on, is the same as at that PR's base.

## How the proof goes

- `Round.lean`: the model rounds every result through `roundWithAccuracy`.  If a rational lies within the rounding interval of a canonical float (`Near`), `roundWithAccuracy` returns exactly that float.
- `Parse.lean`: hence `UnpackedFloat.ofScientific c q` returns the float whenever `c * 10^q` is near it, on both its multiplication and its division path.
- `ReadsBack.lean`: the printer's own acceptance test `readsBack` decides exactly `Near`.
- `Shortest.lean`: the printer always returns digits that `readsBack` accepts.  Its exponent estimate is within seven of the decimal exponent in every binade (checked by the kernel), so the correction loop converges within its fuel, and seventeen digits always suffice because `2^53 < 10^16`.
- `Pack.lean`: `unpack` yields canonical floats, and `pack` and `unpack` invert each other.
- `RoundTrip.lean`, `FastPath.lean`: the round trip in the model, then for `Float` through `Float.ofScientific`.

## Not yet covered

The text layer: that matthiasgoergens/lean4#9's `String.toFloat?` reads `layoutDecimal`'s output back as the same digits and exponent, and the strings `"0.0"` and `"-0.0"`.  The compiled `Float.toString` calls C++ `std::to_chars`, which #10 keeps as its implementation; that it agrees with the model is tested there, not proved.

## Building

    lake exe cache get
    lake build

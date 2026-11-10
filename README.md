# A machine-checked round trip for Lean's `Float` printer

matthiasgoergens/lean4#10 gives `Float.toString` a logical model: the shortest decimal that reads back to the same double, laid out as Python's `repr` does.  matthiasgoergens/lean4#9 adds `String.toFloat?`, which parses such strings.  This repository proves in Lean, against Lean's own `Float.Model`, that the parser reads every string the printer writes back as the same float.

The main theorem, `FloatRoundtrip.toFloat?_modelToString` in `FloatRoundtrip/Text.lean`:

    theorem toFloat?_modelToString (x : Float) (hx : x.isFinite = true) :
        toFloat? (modelToString x.toModel).toSlice = some x

It covers every finite double: normal and subnormal, positive and negative, and both zeros.  `toFloat?` computes its result with `Float.ofScientific`, the function Lean uses for float literals.  The proof covers its fast path (exact doubles multiplied or divided when the digits are below `2^53` and the exponent is at most 22 in absolute value) as well as its exact path through the model.  `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`.

The printer's definitions are copied unchanged from matthiasgoergens/lean4#10 into `FloatRoundtrip/Print.lean`, and the parser's from matthiasgoergens/lean4#9 into `FloatRoundtrip/ToFloat.lean`.  The only changes are the namespace and, in the parser, dropping `private` so that the proofs can name its helpers.  `Float.Model` in Lean v4.36.0-rc2, which this builds on, is the same as at those PRs' base.

## How the proof goes

- `Round.lean`: the model rounds every result through `roundWithAccuracy`.  If a rational lies within the rounding interval of a canonical float (`Near`), `roundWithAccuracy` returns exactly that float.
- `Parse.lean`: hence `UnpackedFloat.ofScientific c q` returns the float whenever `c * 10^q` is near it, on both its multiplication and its division path.
- `ReadsBack.lean`: the printer's own acceptance test `readsBack` decides exactly `Near`.
- `Shortest.lean`: the printer always returns digits that `readsBack` accepts.  Its estimate of the decimal exponent is within seven of the true one in every binade (checked by the kernel), so the correction loop converges within its fuel.  Seventeen digits always suffice because `2^53 < 10^16`.
- `Pack.lean`: `unpack` yields canonical floats, `pack` after `unpack` is the identity, and `unpack` after `pack` is the identity on canonical finite floats and zeros.
- `RoundTrip.lean`, `FastPath.lean`: the digits and exponent the printer chooses read back through `Float.ofScientific` as the same float (`floatOfScientific_printedDigits`).
- `TextParse.lean`: what the parser's helpers make of runs of digits, and what it makes of positional (`[-]A.B`) and scientific (`[-]A[.B]e±K`) notation.
- `Text.lean`: each of the four layouts the printer writes (`d.ddde±XX`, `0.000ddd`, `ddd000.0` and `dd.ddd`) parses back to digits and an exponent with the value the printer chose, and the zeros parse as `0.0` and `-0.0`; with the above, that gives the main theorem.

## Not covered

The compiled `Float.toString` calls C++ `std::to_chars`, which #10 keeps as its implementation; that it agrees with the model is tested there, not proved.  `Float32` is not covered.

## Building

    lake exe cache get
    lake build

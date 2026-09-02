import TTN.Landscape.LocalMin

/-!
# Comparator solution side for Theorem 4.3

The declaration named in `config.json` is the production theorem imported from
`TTN.Landscape.LocalMin`.  This module intentionally introduces no replacement
statement or proof wrapper: Comparator exports the named declaration from this
module's transitive environment and compares it with the trusted challenge.
-/

#check TTN.Arch.minNorm_isLocalMin_isGlobalMin

import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.NotIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.TauOfRoots
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OkGOrb
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OkS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OkKValLt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OkDOrb

open UpperTheory.V.Z.Sym.Sig in
theorem UpperTheory.V.Z.Sym.Sig.sigMain : UpperTheory.V.Z.Sym.Sig.SigMain := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry hR χ hχ
  obtain ⟨hJ, hJf, hJ2, hJ2f, hcG, hcS, hreg⟩ := okLev k O hO h2 Δ s hs hs0 V Ry hR χ hχ
  exact ⟨hcG, hcS, hcS, hJ, hJf, hJ2, hJ2f, hreg,
    fun t ht => (okG k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).1,
    fun t ht => (okG k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).2.1,
    fun t ht => (okG k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).2.2,
    fun t ht => okGOrb k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht,
    fun t ht => (okS k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).1,
    fun t ht => (okS k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).2.1,
    fun t ht => (okS k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).2.2,
    fun t ht => (okK k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).1,
    fun t ht => (okK k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).2.1,
    fun t ht => (okK k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).2.2,
    fun t ht => okDOrb k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht⟩

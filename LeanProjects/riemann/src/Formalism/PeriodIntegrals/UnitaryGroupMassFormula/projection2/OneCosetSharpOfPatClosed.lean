import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.Assemble

namespace PI.OneCosetSharp.W

theorem oneCosetSharp_of (h1 : Claim1) (h2 : Claim2) : OneCosetSharp := by
  intro k _ _ ψ₀ χ k₀ m t j n' c n hk hm hm4 hj1 hj2 hc ha hb
  exact ⟨h1 k ψ₀ χ k₀ m t j n' c n ⟨hk, hm, hm4, hj1, hj2, hc, ha, hb⟩ ,
    h2 k ψ₀ χ k₀ m t j n' c n ⟨hk, hm, hm4, hj1, hj2, hc, ha, hb⟩⟩

theorem oneCosetSharp_of_patClosed (hP : PatClosed) (hK : KappaZero) (hN : NElem) (hG : GaStep) (h2 : Claim2) :
    OneCosetSharp :=
  oneCosetSharp_of (claim1_of hP hK hN hG) h2

end PI.OneCosetSharp.W

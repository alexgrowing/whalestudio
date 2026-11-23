import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasis
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LieDim

theorem length_le {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] [IsCommMonObj A] {n m : ℕ}
    {v : Fin n → (epsR k ⟶ A)} {v' : Fin m → (epsR k ⟶ A)} (hv : IsLieBasis v) (hv' : IsLieBasis v') : n ≤ m := by
  obtain ⟨M, hM⟩ := CM.DiffCoord.exists_linearMap (𝟙 A) hv hv'
  have a := LieComb.lieComb_algebra k A n v hv.1
  have a' := LieComb.lieComb_algebra k A m v' hv'.1
  have hi : Function.Injective M := fun c c' e => by
    obtain ⟨w, hw⟩ := (a.1 c).exists
    obtain ⟨w', hw'⟩ := (a.1 c').exists
    have h₁ := hM c w hw
    have h₂ := hM c' w' hw'
    rw [Category.comp_id] at h₁ h₂
    obtain rfl : w = w' := (a'.1 (M c')).unique (e ▸ h₁) h₂
    exact (hv.2 w (a.2.1 c w hw)).unique hw hw'
  simpa using LinearMap.finrank_le_finrank_of_injective hi

theorem dim_eq_length : ∀ (K : Type) [Field K] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (n : ℕ) (v : Fin n → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR K ⟶ P.A)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v → P.g = n := by
  intro K _ P n v hv
  have := P.isAb.comm
  obtain ⟨w, hw⟩ := KeyPow.exists_isLieBasis P.A P.smoothDim
  exact le_antisymm (length_le hw hv) (length_le hv hw)

end GlobalTheory.LieDim

import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FromBlocksMapIntCastMemSymplecticGroup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem theta_sq_transform_level_eight :
    ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ),
      γ ∈ Matrix.symplecticGroup (Fin g) ℤ →
      (∀ i j, (8 : ℤ) ∣ γ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ γ (Sum.inr i) (Sum.inl j)) →
      (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ,
        theta (halfVec 0) (halfVec 0) (zAct γ τ z) (spAct γ τ) ^ 2 =
          ((ZMod.χ₄ ((γ.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) * (jAut γ τ).det *
            eC (expArg γ τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2) := by
  intro g γ hγ h τ hτ z
  have h48 : (4 : ℤ) ∣ 8 := by norm_num
  exact theta_halfVec_sq_transform hγ (fun i j => h48.trans (h i j).1)
    (fun i j => h48.trans (h i j).2) (k := 0) (k' := 0) (m := 0) (m' := 0)
    (fun i => by rw [mulVec_zero]) (fun i => by rw [mulVec_zero]) hτ z

end GlobalTheory

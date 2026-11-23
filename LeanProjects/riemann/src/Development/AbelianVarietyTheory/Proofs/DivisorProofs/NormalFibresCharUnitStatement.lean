import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalFibresCharUnit
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_fibres_char_unit : ∀ (N : ℕ) (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))) (V : M.Opens),
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback s t)) →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback s t)),
      pullback.fst s t y ∉ V → 2 ≤ ringKrullDim ((pullback s t).presheaf.stalk y)) →
    ∀ (K : Type) [Field K], (N : K) ≠ 0 → ∀ (W : M.Opens) (hW : IsAffineOpen W),
      IsReduced (Γ(M, W) ⊗[ℤ] K) ∧ ∀ q (hq : q ∈ minimalPrimes (Γ(M, W) ⊗[ℤ] K)),
        hW.fromSpec (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := Γ(M, W)) (B := K)) ⟨q, hq.1.1⟩) ∈ V := by
  first | exact @GlobalTheory.RealMult.fibre_tensor_reduced_minimalPrimes | exact GlobalTheory.RealMult.fibre_tensor_reduced_minimalPrimes | (intros; apply GlobalTheory.RealMult.fibre_tensor_reduced_minimalPrimes <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertDiagonalRealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertDiagonalRealDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeRealMultiplicationIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeRealMultiplicationSpanStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRiem

theorem riemannForm_eq_two_trace : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∃ P : u.Λ → u.Λ → F, (∀ l l' : u.Λ, P l l' = -P l' l) ∧ (∀ l₁ l₂ l' : u.Λ, P (l₁ + l₂) l' = P l₁ l' + P l₂ l') ∧
      (∀ (a : 𝓞 F) (l l' al : u.Λ), (al : Fin (Module.finrank ℚ F) → ℂ) = (fun j ↦ (e j (a : F) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) →
        P al l' = (a : F) * P l l') ∧
      (∀ l l' : u.Λ, (∑ j, (h j : ℂ) * ((l : Fin (Module.finrank ℚ F) → ℂ) j * starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im =
        2 * ((Algebra.trace ℚ F ((c : F) * P l l') : ℚ) : ℝ)) ∧
      (∀ l l' : u.Λ, P l l' ∈ dualLat 𝔠) ∧
      (∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 F) {t | ∃ l l' : u.Λ, t = P l l'}) := by
  intro F _ _ _ 𝔠 X c hc u e hu h χ hAH
  have hΛa : ∀ (a : 𝓞 F) (l : Fin (Module.finrank ℚ F) → ℂ), l ∈ u.Λ →
      (fun j ↦ (e j (a : F) : ℂ) * l j) ∈ u.Λ := by
    intro a l hl
    rw [← u.ker, hu, (u.ker l).2 hl]
    haveI := X.rm.hom a
    simp
  have hpos : ∀ j, 0 < h j := by
    intro j
    have := hAH.2.1 (Pi.single j 1) (by simp)
    simpa [Matrix.mulVec_diagonal, dotProduct, Pi.single_apply] using this
  obtain ⟨P, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.lattice_real_multiplication_integral F 𝔠 c hc u.Λ e h hΛa (GlobalTheory.T.appell_humbert_diagonal_real F 𝔠 X c hc u e hu h χ hAH)
  exact ⟨P, h1, h2, h3, h4, h5, GlobalTheory.T.lattice_real_multiplication_span F 𝔠 c hc u.Λ e h hΛa u.discrete u.full hpos P h1 h2 h3 h4 h5
    (fun x hx a ha => GlobalTheory.T.appell_humbert_diagonal_real_dual F 𝔠 X c hc u e hu h χ hAH x hx a ha)⟩

end GlobalTheory.TorusRiem

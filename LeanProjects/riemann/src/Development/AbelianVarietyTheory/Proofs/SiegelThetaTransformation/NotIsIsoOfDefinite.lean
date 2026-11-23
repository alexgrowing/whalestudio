import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsExpansionOfEqSumThFr
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaCharacteristicsIffTestFunctionThetaSeries

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.CuspClass

private theorem hermC_mulVec_mulVec_eq_sum_gram {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    FD.hermC τ G (P *ᵥ w) (P *ᵥ w) = ∑ a, ∑ b, w a * FD.gram τ G P a b * conj (w b) := by
  simp only [FD.hermC, FD.gram, FD.col, Matrix.of_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem not_isIso_of_definite {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (h0 : X.p0 = r) (ξ : Fin r → E) : ¬ X.IsIso ξ := by
  rintro ⟨-, hξ0, hne⟩
  have τ0 : E →+* ℂ := Classical.choice inferInstance
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
    by_cases h : τ0 ∈ X.Ψ
    · exact ⟨τ0, h⟩
    · exact ⟨_, not_not.mp (mt (X.cmType τ0).mpr h)⟩
  obtain ⟨P, hPdet, hP⟩ := X.signature ⟨τ, hτ⟩
  have hherm : FD.hermC τ X.Gm (fun a => τ (ξ a)) (fun a => τ (ξ a)) = 0 := by
    have h1 := congrArg τ hξ0
    rw [map_zero] at h1
    rw [← h1]
    simp [FD.herm, FD.hermC, FD.cc, map_sum, map_mul, NumberField.IsCMField.complexEmbedding_complexConj]
  obtain ⟨w, hw⟩ : ∃ w, P *ᵥ w = fun a => τ (ξ a) :=
    ⟨P⁻¹ *ᵥ (fun a => τ (ξ a)), by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hPdet), Matrix.one_mulVec]⟩
  have hsum : ∑ a, ((Complex.normSq (w a) : ℝ) : ℂ) = 0 := by
    rw [← hherm, ← hw, hermC_mulVec_mulVec_eq_sum_gram, hP]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · simp [Matrix.diagonal_apply_eq, FD.sgn, h0, Complex.mul_conj]
    · intro b _ hb
      simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    · simp
  have hsum' : ∑ a, Complex.normSq (w a) = 0 := by exact_mod_cast hsum
  have hw0 : w = 0 := by
    funext a
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg (w a))).mp hsum' a
      (Finset.mem_univ a)
    simpa using this
  apply hne
  funext a
  have := congrFun hw a
  rw [hw0, Matrix.mulVec_zero] at this
  exact (map_eq_zero τ).mp this.symm

theorem mem_SS_of_eq_thP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ((∃ τ, ∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ k τ i) ∨ q0 = 0) → r ≤ n → ∀ φ : TF n g, IsSB φ → ∀ P ∈ Harm.rowHighest ℂ k k', ∀ Q : Frame X.Ψ r → ℂ, (∀ x ∈ X.dom, Q x = thP X hr bas idx φ P x) → (∀ ga ∈ X.Γ, ∀ x ∈ X.dom, Q (lact ga x) = X.χ (wtOf X hr k k' n) ga * Q x) → Q ∈ X.SS (wtOf X hr k k' n) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn k k' hk hrn φ hφ P hP Q hQ hΓ
  obtain ⟨-, hlink⟩ := GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic E r X g q0 hr bas idx n hs hn
  obtain ⟨m, a, b, t, hab⟩ := hlink φ hφ
  refine GlobalTheory.ThFr.mem_SS_of_eq_sum_thFr (idx := idx) (hr := hr) (s := Finset.univ) (t := t)
    (a := fun j k i => (a j k i : ℝ)) (b := fun j k i => (b j k i : ℝ)) (P := fun _ => P) hs hn ?_
    (fun _ _ => hP) ?_ hΓ
  · rcases hk with ⟨τ, i, hi, hki⟩ | hq
    · exact Or.inl ⟨by omega, τ, Or.inl ⟨i, hi, hki⟩⟩
    · exact Or.inr (not_isIso_of_definite X (by omega))
  · intro x hx
    exact (hQ x hx).trans (hab P x hx)

end GlobalTheory.Dict.CuspClass

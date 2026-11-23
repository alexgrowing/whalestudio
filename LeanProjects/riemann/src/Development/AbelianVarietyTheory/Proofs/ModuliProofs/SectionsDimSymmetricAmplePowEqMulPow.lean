import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphismStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MulAPullbackIsoPowSqSymmetricAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankSectionsPullbackMulByNTwistsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwistAmpleBundleTranslationBundleIsoTranslateStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarizedAbelianAmpleExistsPositiveVolumeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.SymAmpleCount

theorem eq_of_scaling {h : ℕ → ℕ} {g q : ℕ} {v : ℝ} (hq : 2 ≤ q)
    (hs : ∀ e, 1 ≤ e → h (e * q) = q ^ g * h e)
    (ht : Filter.Tendsto (fun e : ℕ => (h e : ℝ) / (e : ℝ) ^ g) Filter.atTop (nhds v)) {e : ℕ} (he : 1 ≤ e) :
    (h e : ℝ) = v * (e : ℝ) ^ g := by
  have h₁ : ∀ i, h (e * q ^ i) = (q ^ i) ^ g * h e := fun i => by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, ← Nat.mul_assoc, hs _ (Nat.mul_pos he (by positivity)), ih, mul_pow]
      ring
  have h₂ : Filter.Tendsto (fun i : ℕ => e * q ^ i) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun i => Nat.le_mul_of_pos_left _ he) (tendsto_pow_atTop_atTop_of_one_lt hq)
  have he' : (e : ℝ) ^ g ≠ 0 := by positivity
  have h₃ : ((fun e : ℕ => (h e : ℝ) / (e : ℝ) ^ g) ∘ fun i : ℕ => e * q ^ i) =
      fun _ => (h e : ℝ) / (e : ℝ) ^ g := by
    funext i
    have : ((q : ℝ) ^ i) ^ g ≠ 0 := by positivity
    simp only [Function.comp, h₁]
    push_cast
    rw [mul_pow]
    field_simp
  have h₄ := ht.comp h₂
  rw [h₃] at h₄
  rw [← tendsto_nhds_unique tendsto_const_nhds h₄]
  field_simp

theorem exists_two_le_cast_ne_zero (K : Type) [Field K] : ∃ l : ℕ, 2 ≤ l ∧ (l : K) ≠ 0 := by
  by_cases h : ((2 : ℕ) : K) = 0
  · refine ⟨3, by norm_num, ?_⟩
    rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, h]
    simp
  · exact ⟨2, le_rfl, h⟩

theorem isIso_translation {S : Scheme.{0}} (A : Over S) [GrpObj A] (x : 𝟙_ (Over S) ⟶ A) :
    IsIso ((toUnit A ≫ x) * 𝟙 A) := by
  refine ⟨(toUnit A ≫ x)⁻¹ * 𝟙 A, ?_, ?_⟩
  · rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit, Category.comp_id, inv_mul_cancel_left]
  · rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, mul_inv_cancel_left]

theorem sectionsDim_symmetricAmple_pow_sq (hL : Out.Laws) (hL' : Out.Laws2) (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K))
    (M : LB P.A.left) (hM : M.IsLB) (ha : Out.RelAmple P.A M) (hs : SymB M) {k : ℕ} (hk : (k : K) ≠ 0) {r : ℕ}
    (hr : SectionsHaveFiniteDimension P.A.hom M r) : SectionsHaveFiniteDimension P.A.hom (lbPow M (k ^ 2)) (k ^ (2 * P.g) * r) := by
  refine ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K _ P.A.hom _ (LB.isLB_pull hM _)).2.1 _ (GlobalTheory.isLB_lbPow hM _)
    (GlobalTheory.T.mulA_pullback_iso_pow_sq_symmetric_abelianVariety K P M k hM hs)).1 _ (GlobalTheory.T.sectionsHaveFiniteDimension_lbDiv_linComb hL hL' K P M k r hM hk fun y _ => ?_)
  obtain ⟨x, hx⟩ := GlobalTheory.T.twist_ampleBundle_translationBundle_iso_translate hL hL' K P M y hM ha
  refine ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K _ P.A.hom _ (LB.isLB_pull hM _)).2.1 _
    (LB.isLB_div hM (LB.isLB_linComb P.isLB _ _)) hx.symm).1 _ ?_
  have := isIso_translation P.A x
  have H := ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K _ P.A.hom M hM).2.2.2.2.2 _
    ((Over.forget _).mapIso (asIso ((toUnit P.A ≫ x) * 𝟙 P.A))) r).1 hr
  have e : ((Over.forget _).mapIso (asIso ((toUnit P.A ≫ x) * 𝟙 P.A))).hom ≫ P.A.hom = P.A.hom := Over.w _
  exact (congrArg (fun q => SectionsHaveFiniteDimension q _ r) e).mp H

end GlobalTheory.SymAmpleCount

namespace GlobalTheory

theorem sectionsDim_symmetricAmple_pow_eq_mul_pow : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left), M.IsLB → Out.RelAmple P.A M → SymB M → ∃ δ : ℕ, 1 ≤ δ ∧ Vol P.A.hom M P.g δ ∧ ∀ e ≥ 1, SectionsHaveFiniteDimension P.A.hom (lbPow M e) (δ * e ^ P.g) := by
  intro hL hL' K _ _ P M hM ha hs
  obtain ⟨v, hv, h, hh, ht⟩ := GlobalTheory.T.polarizedAbelian_ample_exists_positive_volume hL hL' K P M hM ha
  obtain ⟨l, hl, hlK⟩ := SymAmpleCount.exists_two_le_cast_ne_zero K
  have B := GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K _ P.A.hom M hM
  have sc : ∀ e, 1 ≤ e → h (e * l ^ 2) = (l ^ 2) ^ P.g * h e := fun e he => by
    have hMe := GlobalTheory.isLB_lbPow hM e
    have hae : Out.RelAmple P.A (lbPow M e) :=
      (GlobalTheory.relAmple_finite_pow_iso _ P.A P.A (𝟙 _) M e he P.isAb P.isAb hM
        (inferInstanceAs (IsFinite (𝟙 P.A.left)))).2.1.2 ha
    have hse : SymB (lbPow M e) :=
      LBIso.trans hMe (GlobalTheory.isLB_lbPow (LB.isLB_pull hM _) e) (LB.isLB_pull hMe _)
        ((B.2.1 _ (LB.isLB_pull hM _) hs).2 e) (B.2.2.2.2.1 _ _ e)
    have H := SymAmpleCount.sectionsDim_symmetricAmple_pow_sq hL hL' K P _ hMe hae hse hlK (hh e)
    have H' := ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K _ P.A.hom _ (GlobalTheory.isLB_lbPow hMe _)).2.1 _ (GlobalTheory.isLB_lbPow hM _)
      (B.2.2.1 e (l ^ 2))).1 _ H
    rw [← pow_mul]
    exact (GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K _ P.A.hom _ (GlobalTheory.isLB_lbPow hM _)).1 _ _ (hh _) H'
  have key : ∀ e, 1 ≤ e → (h e : ℝ) = v * (e : ℝ) ^ P.g := fun e he =>
    SymAmpleCount.eq_of_scaling (q := l ^ 2) (by nlinarith) sc ht he
  have h₁ : (h 1 : ℝ) = v := by simpa using key 1 le_rfl
  refine ⟨h 1, ?_, ⟨h, hh, h₁ ▸ ht⟩, fun e he => ?_⟩
  · have : (0 : ℝ) < h 1 := h₁ ▸ hv
    exact_mod_cast this
  · have : h e = h 1 * e ^ P.g := by
      have := key e he
      rw [← h₁] at this
      exact_mod_cast this
    exact this ▸ hh e

end GlobalTheory

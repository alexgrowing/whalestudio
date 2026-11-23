import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDivStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsGrowthBasicPropertiesAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HilbertFunctionVanishingIdealVeryAmpleSystemStatement
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsBasisOfIsField
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV Filter Topology

namespace GlobalTheory.VolEx

theorem tendsto_pow_div_pow {i k : ℕ} (h : i ≤ k) :
    Tendsto (fun e : ℕ => (e : ℝ) ^ i / (e : ℝ) ^ k) atTop (𝓝 (if i = k then 1 else 0)) := by
  split_ifs with hik
  · subst hik
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with e he
    rw [div_self (by positivity)]
  · exact (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) (lt_of_le_of_ne h hik)).comp tendsto_natCast_atTop_atTop

theorem tendsto_eval_div_pow (Q : Polynomial ℚ) {k : ℕ} (h : Q.natDegree ≤ k) :
    Tendsto (fun e : ℕ => ((Q.eval (e : ℚ) : ℚ) : ℝ) / (e : ℝ) ^ k) atTop (𝓝 (Q.coeff k : ℝ)) := by
  have h1 : Tendsto (fun e : ℕ => ∑ i ∈ Finset.range (k + 1), (Q.coeff i : ℝ) * ((e : ℝ) ^ i / (e : ℝ) ^ k)) atTop
      (𝓝 (∑ i ∈ Finset.range (k + 1), (Q.coeff i : ℝ) * (if i = k then 1 else 0))) :=
    tendsto_finsetSum _ fun i hi =>
      (tendsto_pow_div_pow (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).const_mul _
  simp only [mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_self, if_true] at h1
  refine h1.congr fun e => ?_
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le h)]
  push_cast
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => (mul_div_assoc _ _ _).symm

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem vAmp_of_veryAmpleBy {p : X ⟶ Sp K} {M : LB X} {m : ℕ} {s : Fin (m + 1) → M.Sec}
    (h : AbLaw.VeryAmpleBy p M s) : VAmp p M s := by
  refine ⟨h.1, fun i => ⟨(h.2 i).1, ?_⟩⟩
  obtain ⟨r, hr, hs⟩ := (h.2 i).2
  refine ⟨r, hr, fun f => ?_⟩
  obtain ⟨F, hF⟩ := hs f
  exact ⟨F, hF.symm⟩

theorem vol_of_eventually {p : X ⟶ Sp K} {M : LB X} (hex : ∀ e, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r) (φ : ℕ → ℝ)
    (hφ : ∀ᶠ e : ℕ in atTop, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℝ) = φ e) {k : ℕ} {δ : ℝ}
    (hδ : Tendsto (fun e : ℕ => φ e / (e : ℝ) ^ k) atTop (𝓝 δ)) : Vol p M k δ := by
  have : ∀ e, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ ((∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℝ) = φ e) → (r : ℝ) = φ e) := by
    intro e
    by_cases h : ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℝ) = φ e
    · obtain ⟨r, h1, h2⟩ := h
      exact ⟨r, h1, fun _ => h2⟩
    · obtain ⟨r, h1⟩ := hex e
      exact ⟨r, h1, fun h' => absurd h' h⟩
  choose h h1 h2 using this
  refine ⟨h, h1, hδ.congr' ?_⟩
  filter_upwards [hφ] with e he
  rw [h2 e he]

theorem vol_nonneg {p : X ⟶ Sp K} {M : LB X} {k : ℕ} {δ : ℝ} (h : Vol p M k δ) : 0 ≤ δ := by
  obtain ⟨h, -, hh⟩ := h
  exact ge_of_tendsto' hh fun e => by positivity

theorem exists_vol : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left), M.IsLB → Out.RelAmple P.A M → ∃ δ : ℝ, 0 < δ ∧ Vol P.A.hom M P.g δ := by
  intro hL _ K _ _ P M hM hA
  have hex : ∀ (N : LB P.A.left), N.IsLB → ∀ e, ∃ r, SectionsHaveFiniteDimension P.A.hom (lbPow N e) r := fun N hN e =>
    (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P (lbPow N e) 0 (LB.isLB_linComb hN _ _)).1
  have : IsProper P.A.hom := P.isAb.proper
  obtain ⟨d, hd, m, s, hs⟩ :=
    ((relAmple_iff_isAmpleLB_of_isAffine P.A hM).1 hA).exists_veryAmpleBy (R := K) P.A.hom
  have hH : (lbPow M d).IsLB := LB.isLB_linComb hM _ _
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.hilbertFunction_vanishingIdeal_veryAmpleSystem K (Fin (m + 1)) _ P.A.hom (lbPow M d) s hH (vAmp_of_veryAmpleBy hs)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have volM : ∀ k, Q.natDegree ≤ k → Vol P.A.hom M k ((Q.coeff k : ℝ) / (d : ℝ) ^ k) := by
    intro k hk
    refine (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P M k hM).2.2.2.2.1 d _ hd hA ?_
    rw [mul_div_cancel₀ _ (by positivity)]
    refine vol_of_eventually (hex _ hH) _ ?_ (tendsto_eval_div_pow Q hk)
    filter_upwards [hQ] with e ⟨r, h1, h2, _⟩
    exact ⟨r, h1, by rw [← h2]; norm_cast⟩
  have volL : ∀ k, P.g ≤ k → Vol P.A.hom P.L k (if P.g = k then 1 else 0) := by
    intro k hk
    refine vol_of_eventually (hex _ P.isLB) (fun e => (e : ℝ) ^ P.g) ?_ (tendsto_pow_div_pow hk)
    filter_upwards [eventually_ge_atTop 1] with e he
    exact ⟨e ^ P.g, PowSec.exists_basis_sections hL.globalSectionsRank K P e he, by push_cast; rfl⟩
  have dom : ∀ (A B : LB P.A.left), A.IsLB → B.IsLB → Out.RelAmple P.A A → ∃ c : ℕ, ∀ k δ δ',
      Vol P.A.hom B k δ → Vol P.A.hom A k δ' → δ ≤ (c : ℝ) ^ k * δ' := by
    intro A B hA hB ha
    obtain ⟨c, ⟨⟨t, ht⟩, -⟩, hc⟩ := ((GlobalTheory.T.eventually_section_and_relAmple_pow_div K P A B hA hB ha).and (eventually_ge_atTop 1)).exists
    refine ⟨c, fun k δ δ' h1 h2 => ?_⟩
    exact ((GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P B k hB).2.2.2.2.2 (lbPow A c) t (LB.isLB_linComb hA _ _) ht).2 _ _ h1
      ((GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P A k hA).2.2.2.1 c δ' hc h2)
  have hdeg : Q.natDegree ≤ P.g := by
    by_contra hlt
    push Not at hlt
    obtain ⟨c, hc⟩ := dom P.L M P.isLB hM P.ample
    have h1 := hc _ _ _ (volM _ le_rfl) (volL _ hlt.le)
    rw [if_neg hlt.ne, mul_zero] at h1
    have h2 := le_antisymm h1 (vol_nonneg (volM _ le_rfl))
    rw [div_eq_zero_iff] at h2
    rcases h2 with h2 | h2
    · have h3 : Q.leadingCoeff = 0 := by exact_mod_cast h2
      rw [Polynomial.leadingCoeff_eq_zero] at h3
      rw [h3] at hlt
      simp at hlt
    · exact absurd h2 (by positivity)
  refine ⟨_, ?_, volM _ hdeg⟩
  obtain ⟨c, hc⟩ := dom M P.L hM P.isLB hA
  have h1 := hc _ _ _ (volL _ le_rfl) (volM _ hdeg)
  rw [if_pos rfl] at h1
  refine lt_of_le_of_ne (vol_nonneg (volM _ hdeg)) fun h => ?_
  rw [← h, mul_zero] at h1
  exact absurd h1 (by norm_num)

end GlobalTheory.VolEx

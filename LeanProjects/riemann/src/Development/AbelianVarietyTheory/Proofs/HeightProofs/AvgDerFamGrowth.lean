import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSubLeOfDerivIcc

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.KAvgDeriv

variable {n : ℕ} {ε : Fin n → Bool}

theorem hs_nonneg' (g : GlobalTheory.TypeSum.Mx n) : 0 ≤ hs g := by
  show 0 ≤ ∑ i, ∑ j, ‖g i j‖ ^ 2
  positivity

theorem continuous_hs' : Continuous (fun g : GlobalTheory.TypeSum.Mx n => hs g) := by
  show Continuous (fun g : GlobalTheory.TypeSum.Mx n => ∑ i, ∑ j, ‖g i j‖ ^ 2)
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (((continuous_apply j).comp (continuous_apply i)).norm).pow 2

theorem mul_exp_conj {P : GlobalTheory.TypeSum.Mx n} (hP : IsUnit P) (X : GlobalTheory.TypeSum.Mx n) (t : ℝ) :
    P * NormedSpace.exp (t • (P⁻¹ * X * P)) = NormedSpace.exp (t • X) * P := by
  rw [← GlobalTheory.TypeSum.GrowthAtPlace.conj_exp hP X t, ← mul_assoc, ← mul_assoc,
    Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP), one_mul]

theorem bound_K (ε : Fin n → Bool) : ∃ M : ℝ, ∀ k : ↥(Formalism.REAL.KG ε), 1 + hs (Formalism.REAL.toMK k) ≤ M := by
  have hc : Continuous fun k : ↥(Formalism.REAL.KG ε) => 1 + hs (Formalism.REAL.toMK k) :=
    continuous_const.add (continuous_hs'.comp
      (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)))
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun k => ?_⟩
  have h := hC k (Set.mem_univ _)
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

theorem bound_e (e : ↥(Formalism.REAL.KG ε) → ℂ) (he : Continuous e) : ∃ E : ℝ, 0 ≤ E ∧ ∀ k, ‖e k‖ ≤ E := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn he.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun k => (hC k (Set.mem_univ _)).trans (le_max_left _ _)⟩

theorem bound_line (y X : GlobalTheory.TypeSum.Mx n) :
    ∃ M : ℝ, ∀ t ∈ Set.Icc (-1 : ℝ) 1, 1 + hs (y * NormedSpace.exp (t • X)) ≤ M := by
  have hs1 : Continuous fun t : ℝ => t • X := continuous_id.smul continuous_const
  have hexp : Continuous fun t : ℝ => NormedSpace.exp (t • X) := by
    have h : Continuous (NormedSpace.exp : GlobalTheory.TypeSum.Mx n → GlobalTheory.TypeSum.Mx n) := by
      open Matrix.Norms.Operator in exact NormedSpace.exp_continuous
    exact h.comp hs1
  have hc : Continuous fun t : ℝ => 1 + hs (y * NormedSpace.exp (t • X)) :=
    continuous_const.add (continuous_hs'.comp (continuous_const.mul hexp))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun t ht => ?_⟩
  have h := hC t ht
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

private theorem isUnit_toMK (k : ↥(Formalism.REAL.KG ε)) : IsUnit (Formalism.REAL.toMK k) :=
  Units.isUnit _

private theorem toMK_conjTranspose_mul_Jm_mul_toMK_eq_Jm (k : ↥(Formalism.REAL.KG ε)) :
    (Formalism.REAL.toMK k)ᴴ * Formalism.REAL.Jm ε * Formalism.REAL.toMK k = Formalism.REAL.Jm ε :=
  (k : Formalism.REAL.UJ ε).2

private theorem toMK_mem_UJset (k : ↥(Formalism.REAL.KG ε)) : Formalism.REAL.toMK k ∈ UJset ε :=
  toMK_conjTranspose_mul_Jm_mul_toMK_eq_Jm k

private theorem mul_mem_UJset_height {g h : GlobalTheory.TypeSum.Mx n} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) :
    g * h ∈ UJset ε := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have hh' : hᴴ * Formalism.REAL.Jm ε * h = Formalism.REAL.Jm ε := hh
  show (g * h)ᴴ * Formalism.REAL.Jm ε * (g * h) = Formalism.REAL.Jm ε
  rw [Matrix.conjTranspose_mul,
    show hᴴ * gᴴ * Formalism.REAL.Jm ε * (g * h) = hᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * h by
      simp only [mul_assoc], hg', hh']

private theorem exp_smul_mem_UJset_of_mem_lieSet' {X : GlobalTheory.TypeSum.Mx n} (hX : X ∈ lieSet ε) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ UJset ε := by
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have hG : Formalism.REAL.inG ε (t • X) := by
    show (t • X)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (t • X) = 0
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX',
      smul_zero]
  exact Formalism.REAL.f1alg_exp_inUJ ε (t • X) hG

private theorem toMK_inv_mul_mul_toMK_mem_lieSet (k : ↥(Formalism.REAL.KG ε)) {X : GlobalTheory.TypeSum.Mx n} (hX : X ∈ lieSet ε) :
    (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k ∈ lieSet ε :=
  GlobalTheory.TypeSum.GrowthAtPlace.conj_lie (isUnit_toMK k) (toMK_conjTranspose_mul_Jm_mul_toMK_eq_Jm k) hX

private theorem mem_lieSet_of_mem_map_toMK_conj (k : ↥(Formalism.REAL.KG ε)) {l : List (GlobalTheory.TypeSum.Mx n)}
    (hl : ∀ Y ∈ l, Y ∈ lieSet ε) :
    ∀ Y ∈ l.map (fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k), Y ∈ lieSet ε := by
  intro Y hY
  obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hY
  exact toMK_inv_mul_mul_toMK_mem_lieSet k (hl Z hZ)

private theorem one_add_hs_nonneg (g : GlobalTheory.TypeSum.Mx n) : 0 ≤ 1 + hs g := by
  have := hs_nonneg' g
  linarith

private theorem mul_one_add_hs_mul_pow_le_abs_mul_pow {N : ℕ} {C MK ML : ℝ} {z k : GlobalTheory.TypeSum.Mx n}
    (hMK : 1 + hs k ≤ MK) (hML : 1 + hs z ≤ ML) :
    C * (1 + hs (z * k)) ^ N ≤ |C| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * ML) ^ N := by
  have a0 := one_add_hs_nonneg (1 : GlobalTheory.TypeSum.Mx n)
  have k0 := one_add_hs_nonneg k
  have z0 := one_add_hs_nonneg z
  have h1 : 1 + hs (z * k) ≤ (1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * ML := by
    have h := GlobalTheory.TypeSum.GrowthAtPlace.one_add_hs_conj_le (1 : GlobalTheory.TypeSum.Mx n) z k
    rw [one_mul] at h
    exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_left hMK a0) hML z0 (mul_nonneg a0 (k0.trans hMK)))
  calc C * (1 + hs (z * k)) ^ N ≤ |C| * (1 + hs (z * k)) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (one_add_hs_nonneg _) N)
    _ ≤ |C| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * ML) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (one_add_hs_nonneg _) h1 N) (abs_nonneg C)

theorem avg_derFam_growth : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ),
    GlobalTheory.TypeSum.IsDerFam ε F →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∃ C : ℝ, ∀ k : ↥(Formalism.REAL.KG ε), ∀ g ∈ UJset ε,
      ‖F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k) g‖ ≤ C * (1 + hs g) ^ N) →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ z ∈ UJset ε,
      MeasureTheory.AEStronglyMeasurable (fun k : ↥(Formalism.REAL.KG ε) =>
        F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k) (z * Formalism.REAL.toMK k)) (Formalism.REAL.muK ε)) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    GlobalTheory.TypeSum.IsDerFam ε (fun l y => ∫ k, e k * F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)
                 (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) ∧
    GlobalTheory.TypeSum.FamGrowth ε N (fun l y => ∫ k, e k * F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)
                 (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) := by
  intro n ε N F hF hG hM e he
  obtain ⟨E, hE0, hE⟩ := bound_e e he
  obtain ⟨MK, hMK⟩ := bound_K (n := n) ε
  refine ⟨?_, ?_⟩
  · intro l hl X hX g hg
    have hXl : ∀ Y ∈ X :: l, Y ∈ lieSet ε := by
      intro Y hY
      rcases List.mem_cons.mp hY with rfl | hY
      · exact hX
      · exact hl Y hY
    obtain ⟨C, hC⟩ := hG (X :: l) hXl
    obtain ⟨C0, hC0⟩ := hG l hl
    obtain ⟨ML, hML⟩ := bound_line g X
    have hgt : ∀ t : ℝ, g * NormedSpace.exp (t • X) ∈ UJset ε := fun t => mul_mem_UJset_height hg (exp_smul_mem_UJset_of_mem_lieSet' hX t)
    have hb : ∀ (L : List (GlobalTheory.TypeSum.Mx n)) (C : ℝ),
        (∀ k : ↥(Formalism.REAL.KG ε), ∀ z ∈ UJset ε,
          ‖F (L.map fun Y => (Formalism.REAL.toMK k)⁻¹ * Y * Formalism.REAL.toMK k) z‖ ≤ C * (1 + hs z) ^ N) →
        ∀ k : ↥(Formalism.REAL.KG ε), ∀ t ∈ Set.Icc (-1 : ℝ) 1,
          ‖e k * F (L.map fun Y => (Formalism.REAL.toMK k)⁻¹ * Y * Formalism.REAL.toMK k)
            (g * NormedSpace.exp (t • X) * Formalism.REAL.toMK k)‖
            ≤ E * (|C| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * ML) ^ N) := by
      intro L C hC k t ht
      rw [norm_mul]
      exact mul_le_mul (hE k)
        ((hC k _ (mul_mem_UJset_height (hgt t) (toMK_mem_UJset k))).trans (mul_one_add_hs_mul_pow_le_abs_mul_pow (hMK k) (hML t ht)))
        (norm_nonneg _) hE0
    have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := Formalism.REAL.muK ε) (x₀ := (0 : ℝ))
      (F := fun (t : ℝ) (k : ↥(Formalism.REAL.KG ε)) =>
        e k * F (l.map fun Y => (Formalism.REAL.toMK k)⁻¹ * Y * Formalism.REAL.toMK k)
          (g * NormedSpace.exp (t • X) * Formalism.REAL.toMK k))
      (F' := fun (t : ℝ) (k : ↥(Formalism.REAL.KG ε)) =>
        e k * F ((X :: l).map fun Y => (Formalism.REAL.toMK k)⁻¹ * Y * Formalism.REAL.toMK k)
          (g * NormedSpace.exp (t • X) * Formalism.REAL.toMK k))
      (bound := fun _ => E * (|C| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * ML) ^ N))
      (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
      (Filter.Eventually.of_forall fun t => he.aestronglyMeasurable.mul (hM l hl _ (hgt t)))
      (Integrable.mono' (integrable_const (E * (|C0| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * ML) ^ N)))
        (he.aestronglyMeasurable.mul (hM l hl _ (hgt 0)))
        (Filter.Eventually.of_forall fun k => hb l C0 hC0 k 0 h0))
      (he.aestronglyMeasurable.mul (hM (X :: l) hXl _ (hgt 0)))
      (Filter.Eventually.of_forall fun k t ht => hb (X :: l) C hC k t ht)
      (integrable_const _)
      (Filter.Eventually.of_forall fun k t _ => by
        have hk := isUnit_toMK k
        have hm : ∀ s : ℝ, g * NormedSpace.exp (s • X) * Formalism.REAL.toMK k =
            g * Formalism.REAL.toMK k * NormedSpace.exp (s • ((Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)) := by
          intro s
          rw [mul_assoc g (Formalism.REAL.toMK k), mul_exp_conj hk X s, mul_assoc]
        have hd := GlobalTheory.TypeSum.IsDerFam.hasDerivAt_exp hF (mem_lieSet_of_mem_map_toMK_conj k hl) (toMK_inv_mul_mul_toMK_mem_lieSet k hX)
          (mul_mem_UJset_height hg (toMK_mem_UJset k)) t
        simp only [hm]
        exact hd.const_mul (e k))
    refine key.2.congr_deriv ?_
    simp only [zero_smul, NormedSpace.exp_zero, mul_one]
  · intro l hl
    obtain ⟨C, hC⟩ := hG l hl
    refine ⟨(Formalism.REAL.muK ε).real Set.univ * E * |C| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK) ^ N,
      fun g hg => ?_⟩
    have hk : ∀ k : ↥(Formalism.REAL.KG ε),
        ‖e k * F (l.map fun Y => (Formalism.REAL.toMK k)⁻¹ * Y * Formalism.REAL.toMK k) (g * Formalism.REAL.toMK k)‖
          ≤ E * (|C| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * (1 + hs g)) ^ N) := by
      intro k
      rw [norm_mul]
      exact mul_le_mul (hE k)
        ((hC k _ (mul_mem_UJset_height hg (toMK_mem_UJset k))).trans (mul_one_add_hs_mul_pow_le_abs_mul_pow (hMK k) le_rfl))
        (norm_nonneg _) hE0
    refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hk)).trans (le_of_eq ?_)
    rw [mul_pow, mul_pow]
    ring

end GlobalTheory.KAvgDeriv

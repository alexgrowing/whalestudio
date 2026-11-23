import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompact
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelUnitaryGroupOpNormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselConstantBoundsOfGeTwoNPowFiveStatement

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf

theorem integrable_opn_rpow_neg {k r : ℕ} (μ : Measure (Mt k r)) (A : ℝ)
    (hc : Continuous fun x : Mat k r => opn x) (h : normInt μ A < ⊤) :
    Integrable (fun x : Mt k r => opn (Matrix.of x) ^ (-A)) μ := by
  have hm : Measurable fun x : Mt k r => opn (Matrix.of x) ^ (-A) :=
    (show Continuous fun x : Mt k r => opn (Matrix.of x) from hc).measurable.pow_const _
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (opn_nonneg _) _)).2 h

theorem rpow_fubini_ineq {x y t a : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (ht : 0 < t) (hyt : t / x ≤ y)
    (ha : 0 ≤ a) : x ^ (-a) * y ^ (-a) ≤ x ^ (-(a / 2)) * t ^ (-(a / 2)) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have h1 : y ^ (-a) ≤ y ^ (-(a / 2)) := Real.rpow_le_rpow_of_exponent_le hy (by linarith)
  have h2 : y ^ (-(a / 2)) ≤ (t / x) ^ (-(a / 2)) :=
    Real.rpow_le_rpow_of_nonpos (div_pos ht hx0) hyt (by linarith)
  have h3 : (t / x) ^ (-(a / 2)) = t ^ (-(a / 2)) / x ^ (-(a / 2)) := Real.div_rpow ht.le hx0.le _
  have h4 : x ^ (-a) = x ^ (-(a / 2)) * x ^ (-(a / 2)) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hxp : 0 < x ^ (-(a / 2)) := Real.rpow_pos_of_pos hx0 _
  calc x ^ (-a) * y ^ (-a) ≤ x ^ (-a) * ((t / x) ^ (-(a / 2))) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (Real.rpow_nonneg hx0.le _)
    _ = x ^ (-(a / 2)) * t ^ (-(a / 2)) := by
        rw [h3, h4]; field_simp

theorem fubini_bound : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ v₁ ∈ DD σ w, Integrable (fun p : Mt k r × Mt k r => coef σ u v (Matrix.of p.1) * star (coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1))) (μG.prod μS) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv v₁ hv₁
  obtain ⟨hk, hrep, -, -, hHG, -, ha, hdec, -⟩ := hStd
  obtain ⟨hz, hT, -, hHS, -⟩ := hSide
  obtain ⟨hGc, -, -, hSc, -⟩ := GlobalTheory.SgInf.closedSub_groups k r z hz hT
  obtain ⟨hN1, -, hNc, -, -, -, hN7, -⟩ := GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r
  have hA := (GlobalTheory.T.bessel_constant_bounds_of_ge_two_n_pow_five k r a hk ha).1
  have hIG := GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r (GG k r) μG (a / 2) hGc hHG hA
  have hIS := GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r (Sset k r z) μS (a / 2) hSc hHS hA
  obtain ⟨C, hC⟩ := hdec u hu v hv
  obtain ⟨C₁, hC₁⟩ := hdec u₁ hu₁ v₁ hv₁
  haveI := hHG.1
  haveI := hHS.1
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  set T : Set (Mt k r × Mt k r) := {p | Matrix.of p.1 ∈ GG k r ∧ Matrix.of p.2 ∈ Sset k r z} with hTdef
  have hTm : MeasurableSet T := by
    have h1 : IsClosed {p : Mt k r × Mt k r | Matrix.of p.1 ∈ GG k r} :=
      hGc.2.1.preimage continuous_fst
    have h2 : IsClosed {p : Mt k r × Mt k r | Matrix.of p.2 ∈ Sset k r z} :=
      hSc.2.1.preimage continuous_snd
    exact (h1.inter h2).measurableSet
  have hTae : ∀ᵐ p ∂(μG.prod μS), p ∈ T := by
    rw [ae_iff]
    refine measure_mono_null (t := ({x : Mt k r | Matrix.of x ∉ GG k r} ×ˢ Set.univ) ∪
      (Set.univ ×ˢ {x : Mt k r | Matrix.of x ∉ Sset k r z})) ?_ ?_
    · intro p hp
      simp only [Set.mem_setOf_eq, hTdef, not_and_or] at hp
      rcases hp with hp | hp
      · exact Or.inl ⟨hp, trivial⟩
      · exact Or.inr ⟨trivial, hp⟩
    · refine measure_union_null ?_ ?_
      · rw [Measure.prod_prod, hHG.2.2.1, zero_mul]
      · rw [Measure.prod_prod, hHS.2.2.1, mul_zero]
  have hg : Integrable (fun p : Mt k r × Mt k r => (|C| * |C₁|) *
      (opn (Matrix.of p.1) ^ (-(a / 2)) * opn (Matrix.of p.2) ^ (-(a / 2)))) (μG.prod μS) :=
    ((integrable_opn_rpow_neg μG _ hNc hIG).mul_prod (integrable_opn_rpow_neg μS _ hNc hIS)).const_mul _
  have hcont : ContinuousOn (fun p : Mt k r × Mt k r =>
      coef σ u v (Matrix.of p.1) * star (coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1))) T := by
    have c1 : ContinuousOn (fun p : Mt k r × Mt k r => σ (Matrix.of p.1) u) T :=
      (hrep.2.2 u).comp (continuous_fst.continuousOn) (fun p hp => hp.1)
    have hmul : Continuous fun p : Mt k r × Mt k r => (Matrix.of p.2 * Matrix.of p.1 : Mat k r) :=
      (continuous_snd (X := Mat k r) (Y := Mat k r)).matrix_mul continuous_fst
    have c2 : ContinuousOn (fun p : Mt k r × Mt k r => σ (Matrix.of p.2 * Matrix.of p.1) u₁) T :=
      (hrep.2.2 u₁).comp hmul.continuousOn
        (fun p hp => hGc.2.2.2.1 _ (hSc.1 hp.2) _ hp.1)
    exact (continuousOn_const.inner c1).mul (continuous_star.comp_continuousOn (continuousOn_const.inner c2))
  refine hg.mono' ?_ ?_
  · have := hcont.aestronglyMeasurable (μ := μG.prod μS) hTm
    rwa [Measure.restrict_eq_self_of_ae_mem hTae] at this
  · filter_upwards [hTae] with p hp
    obtain ⟨hpG, hpS⟩ := hp
    have hSG : Matrix.of p.2 ∈ GG k r := hSc.1 hpS
    have hyG : (Matrix.of p.2 * Matrix.of p.1 : Mat k r) ∈ GG k r := hGc.2.2.2.1 _ hSG _ hpG
    have hx1 := (hN1 _ hpG).2
    have ht1 := (hN1 _ hSG).2
    have hy1 := (hN1 _ hyG).2
    have hyt : opn (Matrix.of p.2 : Mat k r) / opn (Matrix.of p.1 : Mat k r) ≤
        opn (Matrix.of p.2 * Matrix.of p.1 : Mat k r) := (hN7 _ hSG _ hpG).1
    have e1 : ‖coef σ u v (Matrix.of p.1)‖ ≤ |C| * opn (Matrix.of p.1 : Mat k r) ^ (-a) :=
      (hC _ hpG).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (opn_nonneg _) _))
    have e2 : ‖coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1)‖ ≤
        |C₁| * opn (Matrix.of p.2 * Matrix.of p.1 : Mat k r) ^ (-a) :=
      (hC₁ _ hyG).trans (mul_le_mul_of_nonneg_right (le_abs_self C₁) (Real.rpow_nonneg (opn_nonneg _) _))
    have key := rpow_fubini_ineq hx1 hy1 (lt_of_lt_of_le one_pos ht1) hyt ha0
    rw [norm_mul, norm_star]
    calc ‖coef σ u v (Matrix.of p.1)‖ * ‖coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1)‖
        ≤ (|C| * opn (Matrix.of p.1 : Mat k r) ^ (-a)) *
            (|C₁| * opn (Matrix.of p.2 * Matrix.of p.1 : Mat k r) ^ (-a)) :=
          mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (opn_nonneg _) _))
      _ = (|C| * |C₁|) * (opn (Matrix.of p.1 : Mat k r) ^ (-a) *
            opn (Matrix.of p.2 * Matrix.of p.1 : Mat k r) ^ (-a)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left key (mul_nonneg (abs_nonneg _) (abs_nonneg _))

end GlobalTheory.SgInf

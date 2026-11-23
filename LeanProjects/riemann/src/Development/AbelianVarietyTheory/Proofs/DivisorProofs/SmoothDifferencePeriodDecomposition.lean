import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection

set_option autoImplicit false

noncomputable section

open Matrix Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm MeasureTheory
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm.Hadamard

theorem contDiff_setIntegral_nat {X P E : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K) {a : X → E} (ha : Continuous a)
    (m : ℕ) : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (Ψ : P × E → F),
      ContDiff ℝ ∞ Ψ → ContDiff ℝ m fun p => ∫ x in K, Ψ (p, a x) ∂μ := by
  have key : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (Ψ : P × E → F),
      ContDiff ℝ ∞ Ψ → ∀ p₀, HasFDerivAt (fun p => ∫ x in K, Ψ (p, a x) ∂μ)
        (∫ x in K, (fderiv ℝ Ψ (p₀, a x)).comp (ContinuousLinearMap.inl ℝ P E) ∂μ) p₀ := by
    intro F _ _ _ Ψ hΨ p₀
    have hc : Continuous fun z => (fderiv ℝ Ψ z).comp (ContinuousLinearMap.inl ℝ P E) :=
      (hΨ.continuous_fderiv (by simp)).clm_comp continuous_const
    have : ProperSpace P := FiniteDimensional.proper ℝ P
    obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ 1).prod (hK.image ha)).exists_bound_of_continuousOn
      hc.continuousOn
    have hi : ∀ p, IntegrableOn (fun x => Ψ (p, a x)) K μ := fun p =>
      (hΨ.continuous.comp (continuous_const.prodMk ha)).continuousOn.integrableOn_compact hK
    have hi' : IntegrableOn (fun x => (fderiv ℝ Ψ (p₀, a x)).comp (ContinuousLinearMap.inl ℝ P E)) K μ :=
      (hc.comp (continuous_const.prodMk ha)).continuousOn.integrableOn_compact hK
    have : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.closedBall p₀ 1)
      (F' := fun p x => (fderiv ℝ Ψ (p, a x)).comp (ContinuousLinearMap.inl ℝ P E)) (bound := fun _ => C)
      (Metric.closedBall_mem_nhds _ one_pos) (Filter.Eventually.of_forall fun p => (hi p).1) (hi p₀) hi'.1 ?_
      (integrable_const C) ?_
    · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx p hp
      exact hC (p, a x) ⟨hp, ⟨x, hx, rfl⟩⟩
    · refine Filter.Eventually.of_forall fun x p _ => ?_
      exact ((hΨ.differentiable (by simp)) (p, a x)).hasFDerivAt.comp p (hasFDerivAt_prodMk_left p (a x))
  induction m with
  | zero =>
    intro F _ _ _ Ψ hΨ
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun p => (key Ψ hΨ p).continuousAt)
  | succ m ih =>
    intro F _ _ _ Ψ hΨ
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨_, ih (fun z => (fderiv ℝ Ψ z).comp (ContinuousLinearMap.inl ℝ P E)) ?_, key Ψ hΨ⟩
    exact (hΨ.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const

def meanD {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : V → F) (p : V × V) : V →L[ℝ] F :=
  ∫ t in Icc (0 : ℝ) 1, fderiv ℝ f (p.1 + t • p.2)

theorem contDiff_meanD {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : V → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (meanD f) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  have hΨ : ContDiff ℝ ∞ (fun z : (V × V) × ℝ => fderiv ℝ f (z.1.1 + z.2 • z.1.2)) :=
    h1.comp (contDiff_fst.fst.add (contDiff_snd.smul contDiff_fst.snd))
  exact contDiff_infty.2 fun m =>
    contDiff_setIntegral_nat (volume : Measure ℝ) isCompact_Icc continuous_id m _ hΨ

theorem sub_eq_meanD {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : V → F} (hf : ContDiff ℝ ∞ f) (y δ : V) :
    f (y + δ) - f y = meanD f (y, δ) δ := by
  have hc : Continuous fun t : ℝ => fderiv ℝ f (y + t • δ) :=
    (hf.continuous_fderiv (by simp)).comp (by fun_prop)
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (y + t • δ)) (fderiv ℝ f (y + t • δ) δ) t := by
    intro t
    have h2 : HasDerivAt (fun t : ℝ => y + t • δ) δ t := by
      simpa using ((hasDerivAt_id t).smul_const δ).const_add y
    exact ((hf.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t h2
  have h3 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1) (fun t _ => hd t)
    ((hc.clm_apply continuous_const).intervalIntegrable _ _)
  simp only [one_smul, zero_smul, add_zero] at h3
  rw [← h3, meanD, ContinuousLinearMap.integral_apply (hc.continuousOn.integrableOn_compact isCompact_Icc),
    intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

theorem eq_sum_single {g : ℕ} (δ : Fin g → ℂ) :
    δ = ∑ a, (δ a).re • (Pi.single a 1 : Fin g → ℂ) + ∑ a, (δ a).im • (Pi.single a Complex.I : Fin g → ℂ) := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem hadamard : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ} [FiniteDimensional ℂ E] {B : Set E}, IsOpen B → ∀ {ψ : E → Fin g → ℂ}, ContDiffOn ℝ ∞ ψ B → ∀ {b : E}, b ∈ B → ∀ {m : ℕ} {f : (Fin g → ℂ) → Ext m}, ContDiff ℝ ∞ f → ∃ (φ : Fin g ⊕ Fin g → E → ℂ) (σ : Fin g ⊕ Fin g → Pt E g → Ext m), (∀ k, ContDiffOn ℝ ∞ (φ k) B ∧ φ k b = 0 ∧ ContDiffOn ℝ ∞ (σ k) (cov B g)) ∧ ∀ P ∈ cov B g, f (P.2 + ψ P.1) - f (P.2 + ψ b) = ∑ k, φ k P.1 • σ k P := by
  intro E _ _ g n _ B _ ψ hψ b _ m f hf
  have hM := contDiff_meanD hf
  have hδ : ContDiffOn ℝ ∞ (fun b' => ψ b' - ψ b) B := hψ.sub contDiffOn_const
  have hδa : ∀ a, ContDiffOn ℝ ∞ (fun b' => (ψ b' - ψ b) a) B := fun a => contDiffOn_pi.1 hδ a
  have hS : ContDiffOn ℝ ∞ (fun P : Pt E g => meanD f (P.2 + ψ b, ψ P.1 - ψ b)) (cov B g) :=
    hM.comp_contDiffOn ((contDiff_snd.contDiffOn.add contDiffOn_const).prodMk
      (hδ.comp contDiff_fst.contDiffOn fun P hP => hP.1))
  refine ⟨Sum.elim (fun a b' => (((ψ b' - ψ b) a).re : ℂ)) (fun a b' => (((ψ b' - ψ b) a).im : ℂ)),
    Sum.elim (fun a P => meanD f (P.2 + ψ b, ψ P.1 - ψ b) (Pi.single a 1))
      (fun a P => meanD f (P.2 + ψ b, ψ P.1 - ψ b) (Pi.single a Complex.I)), ?_, ?_⟩
  · rintro (a | a)
    · refine ⟨?_, by simp, hS.clm_apply contDiffOn_const⟩
      exact (Complex.ofRealCLM.contDiff.comp Complex.reCLM.contDiff).comp_contDiffOn (hδa a)
    · refine ⟨?_, by simp, hS.clm_apply contDiffOn_const⟩
      exact (Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff).comp_contDiffOn (hδa a)
  · intro P _
    have h := sub_eq_meanD hf (P.2 + ψ b) (ψ P.1 - ψ b)
    rw [show P.2 + ψ b + (ψ P.1 - ψ b) = P.2 + ψ P.1 by abel] at h
    rw [h, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    generalize meanD f (P.2 + ψ b, ψ P.1 - ψ b) = L
    generalize ψ P.1 - ψ b = δ
    conv_lhs => rw [eq_sum_single δ]
    simp only [map_add, map_sum, map_smul, Complex.coe_smul]

end GlobalTheory.TorsionForm.Hadamard

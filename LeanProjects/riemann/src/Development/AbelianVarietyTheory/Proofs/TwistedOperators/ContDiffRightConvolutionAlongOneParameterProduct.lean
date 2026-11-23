import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcGASmoothAndRderMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousSetIntegralConstTermOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff ComplexConjugate

noncomputable section

namespace GlobalTheory.ConvSmooth

section Param

variable {H : Type} [MeasurableSpace H] {ν : Measure H} {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X] {c : H → X} {S : Set X} {φ : H → ℂ}

theorem hasFDerivAt_integral_smul_param (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W} (hΘ : ContDiff ℝ ∞ Θ) (t₀ : P) :
    HasFDerivAt (fun t => ∫ y, φ y • Θ (t, c y) ∂ν) (∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t₀ ∂ν) t₀ := by
  have hΘs : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1 :=
    ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst)
      (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl
  have hΘ' := hΘs.continuous
  have hK : IsCompact (closedBall t₀ 1 ×ˢ S) := (isCompact_closedBall t₀ 1).prod hS
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΘ'.continuousOn
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hΘ.continuous.continuousOn
  have hm : ∀ t, AEStronglyMeasurable (fun y => φ y • Θ (t, c y)) ν := fun t =>
    hφ.1.smul ((hΘ.continuous.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (F' := fun t y => φ y • fderiv ℝ (fun s => Θ (s, c y)) t) (bound := fun y => ‖φ y‖ * C) (ball_mem_nhds t₀ one_pos)
    (.of_forall hm) ?_ ?_ ?_ (hφ.norm.mul_const C) ?_
  · refine Integrable.mono' (hφ.norm.mul_const C₀) (hm t₀) ?_
    filter_upwards [hcS] with y hy
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC₀ _ ⟨mem_closedBall_self zero_le_one, hy⟩) (norm_nonneg _)
  · exact hφ.1.smul ((hΘ'.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)
  · filter_upwards [hcS] with y hy t ht
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC (t, c y) ⟨ball_subset_closedBall ht, hy⟩) (norm_nonneg _)
  · refine .of_forall fun y t _ => ?_
    have hd : ContDiff ℝ ∞ fun s => Θ (s, c y) := hΘ.comp (contDiff_id.prodMk contDiff_const)
    exact ((hd.differentiable (by simp)) t).hasFDerivAt.const_smul (φ y)

theorem contDiff_integral_smul_param (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W} (hΘ : ContDiff ℝ ∞ Θ) :
    ContDiff ℝ ∞ fun t => ∫ y, φ y • Θ (t, c y) ∂ν := by
  rw [contDiff_infty]
  intro n
  induction n generalizing W with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t =>
      (hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t).continuousAt)
  | succ n ih =>
    have hΘ' : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1 :=
      ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst)
        (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl
    exact contDiff_succ_iff_hasFDerivAt.2 ⟨fun t => ∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t ∂ν,
      ih hΘ', fun t => hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t⟩

end Param

section Group

open GlobalTheory.AdelicU GlobalTheory.Orb NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] {u : P → GAd σ J} {ν μ : Measure (GAd σ J)} {φ : GAd σ J → ℂ} {K : Set (GAd σ J)}

omit [NumberField E] [FiniteDimensional ℝ P] in

theorem infFin_mul_smoothFam (hu : IsSmoothRealFam u) {a : GInf σ J → ℂ} {b : GFin σ J → ℂ}
    {Φ : (∀ w : InfinitePlace F, EmbOver E w → Fin n → Fin n → ℂ) → ℂ} (e : ∀ x, a x = Φ (infCoord σ J x))
    (z : GAd σ J) (t : P) :
    infFin σ J a b (z * u t) = Φ (fun w τ i j => ∑ k, infCoord σ J (projInf σ J z) w τ i k *
      archMat σ J τ (projArch σ J w (u t)) k j) * b (projFin σ J z) := by
  simp only [infFin, map_mul, hu.1, mul_one, e, infCoord_mul]

theorem integrable_conj_mul_of_mem (hφ : Integrable φ ν) {h : GAd σ J → ℂ}
    (hh : h ∈ CcAd σ J) (g : GAd σ J) (x : GAd σ J) :
    Integrable (fun y => conj (h (y⁻¹ * g * x)) * φ y) ν := by
  obtain ⟨h1, h2⟩ := continuous_of_mem_ccAd hh
  obtain ⟨M, hM⟩ := h1.bounded_above_of_compact_support h2
  refine Integrable.mono' (hφ.norm.const_mul M) ?_ (.of_forall fun y => ?_)
  · have hc : Continuous fun y : GAd σ J => conj (h (y⁻¹ * g * x)) :=
      Complex.continuous_conj.comp (h1.comp ((continuous_inv.mul continuous_const).mul continuous_const))
    exact hc.aestronglyMeasurable.mul hφ.1
  · rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)

theorem contDiff_integral_of_compact (hu : IsSmoothRealFam u) (hKc : IsCompact K) (hK : ∀ᵐ y ∂ν, y ∈ K)
    (hφ : Integrable φ ν) {h : GAd σ J → ℂ} (hh : h ∈ CcAd σ J) (g : GAd σ J) :
    ContDiff ℝ ∞ fun t => ∫ y, conj (h (y⁻¹ * g * u t)) * φ y ∂ν := by
  induction hh using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ⟨-, Φ, hΦ, e⟩, b, hb, rfl⟩ := hf
    have hcc : Continuous fun y : GAd σ J => infCoord σ J (projInf σ J (y⁻¹ * g)) :=
      (continuous_infCoord σ J).comp ((continuous_projInf σ J).comp (continuous_inv.mul continuous_const))
    obtain ⟨M, hM⟩ := hb.1.continuous.bounded_above_of_compact_support hb.2
    have hφ' : Integrable (fun y => conj (b (projFin σ J (y⁻¹ * g))) * φ y) ν := by
      refine Integrable.mono' (hφ.norm.const_mul M) ?_ (.of_forall fun y => ?_)
      · exact (Complex.continuous_conj.comp (hb.1.continuous.comp ((continuous_projFin σ J).comp
          (continuous_inv.mul continuous_const)))).aestronglyMeasurable.mul hφ.1
      · rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    have hΘ : ContDiff ℝ ∞ fun p : P × (∀ w : InfinitePlace F, EmbOver E w → Fin n → Fin n → ℂ) =>
        conj (Φ (fun w τ i j => ∑ k, p.2 w τ i k * archMat σ J τ (projArch σ J w (u p.1)) k j)) :=
      Complex.conjCLE.contDiff.comp (hΦ.comp (contDiff_pi.2 fun w => contDiff_pi.2 fun τ => contDiff_pi.2 fun i =>
        contDiff_pi.2 fun j => ContDiff.sum fun k _ =>
          (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_snd w) τ) i) k).mul
            ((hu.2 w τ k j).comp contDiff_fst)))
    have key := GlobalTheory.ConvSmooth.contDiff_integral_smul_param hcc.aestronglyMeasurable (hKc.image hcc)
      (hK.mono fun y hy => mem_image_of_mem _ hy) hφ' hΘ
    convert key using 1
    funext t
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [smul_eq_mul]
    rw [infFin_mul_smoothFam hu e, map_mul]
    ring
  | zero => simp only [Pi.zero_apply, map_zero, zero_mul, integral_zero]; exact contDiff_const
  | add f f' hf hf' h h' =>
    have e : (fun t => ∫ y, conj ((f + f') (y⁻¹ * g * u t)) * φ y ∂ν) =
        fun t => (∫ y, conj (f (y⁻¹ * g * u t)) * φ y ∂ν) + ∫ y, conj (f' (y⁻¹ * g * u t)) * φ y ∂ν :=
      funext fun t => by
        simp only [Pi.add_apply, map_add, add_mul]
        exact integral_add (integrable_conj_mul_of_mem hφ hf g _) (integrable_conj_mul_of_mem hφ hf' g _)
    rw [e]
    exact h.add h'
  | smul a f _ h =>
    have e : (fun t => ∫ y, conj ((a • f) (y⁻¹ * g * u t)) * φ y ∂ν) =
        fun t => conj a * ∫ y, conj (f (y⁻¹ * g * u t)) * φ y ∂ν :=
      funext fun t => by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun y => ?_)
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
        ring
    rw [e]
    exact contDiff_const.mul h

theorem contDiff_integral_conj_mul (hu : IsSmoothRealFam u) (hcu : Continuous u) (hφ : LocallyIntegrable φ μ)
    {h : GAd σ J → ℂ} (hh : h ∈ CcAd σ J) (g : GAd σ J) :
    ContDiff ℝ ∞ fun t => ∫ y, conj (h (y⁻¹ * g * u t)) * φ y ∂μ := by
  refine contDiff_iff_contDiffAt.2 fun t₀ => ?_
  obtain ⟨-, hs⟩ := continuous_of_mem_ccAd hh
  set K := (fun p : P × GAd σ J => g * u p.1 * p.2⁻¹) '' (closedBall t₀ 1 ×ˢ tsupport h) with hKdef
  have hKc : IsCompact K := ((isCompact_closedBall t₀ 1).prod hs.isCompact).image (by fun_prop)
  have key := contDiff_integral_of_compact (ν := μ.restrict K) hu hKc (ae_restrict_mem hKc.measurableSet)
    (hφ.integrableOn_isCompact hKc) hh g
  refine key.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds t₀ one_pos] with t ht
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
  have : y⁻¹ * g * u t ∉ tsupport h := fun hm =>
    hy ⟨(t, y⁻¹ * g * u t), ⟨ball_subset_closedBall ht, hm⟩, by simp [mul_assoc]⟩
  simp [image_eq_zero_of_notMem_tsupport this]

end Group

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta NumberField
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem continuous_ofFn_prod {G Q : Type} [Monoid G] [TopologicalSpace G] [ContinuousMul G] [TopologicalSpace Q]
    {k : ℕ} {v : Fin k → Q → G} (hv : ∀ i, Continuous (v i)) :
    Continuous fun t => (List.ofFn fun i => v i t).prod := by
  induction k with
  | zero => simpa using continuous_const
  | succ k ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (hv 0).mul (ih fun i => hv i.succ)

theorem contDiff_convR_lift_oneP : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ (F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ) (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g : GA D V, ContDiff ℝ ∞ fun t : Fin k → ℝ => GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  intro D V μ _ _ θ hθ f hf F k τs Xs hX g
  have hu := GlobalTheory.Orb.isSmoothRealFam_prod fun i =>
    (GlobalTheory.Orb.isSmoothRealFam_oneP hθ (hX i)).1.comp (contDiff_apply ℝ ℝ i)
  have hcu := continuous_ofFn_prod (v := fun i (t : Fin k → ℝ) => oneP θ V (τs i) (Xs i) (t i)) fun i =>
    (GlobalTheory.Orb.isSmoothRealFam_oneP hθ (hX i)).2.1.comp (continuous_apply i)
  have hφ : LocallyIntegrable (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) μ :=
    locallyIntegrable_iff.2 fun C hC => (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F C hC).2
  have key := contDiff_integral_conj_mul hu hcu hφ (GlobalTheory.Orb.starFn_mem_ccAd hf) g
  convert key using 1
  funext t
  rw [GlobalTheory.AutomorphicL2Unitary.convR_eq]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp [GlobalTheory.AutomorphicL2Unitary.starFn, mul_assoc]

end Record

end GlobalTheory.ConvSmooth

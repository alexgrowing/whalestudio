import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableConv
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableCartan
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableLaplacian
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableParabolic

open NumberField IsDedekindDomain Topology Filter Set MeasureTheory
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace IsExpLieAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

def GKModule.comap {K : Subgroup G} {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (M : h.GKModule K V) (j : W →ₗ[ℂ] V) (hj : Function.Injective j)
    (ρ : h.lieSubalgebra →ₗ⁅ℝ⁆ Module.End ℂ W) (σ : Representation ℂ K W)
    (hρ : ∀ X w, j (ρ X w) = M.ρ X (j w)) (hσ : ∀ k w, j (σ k w) = M.σ k (j w)) :
    h.GKModule K W where
  ρ := ρ
  σ := σ
  locallyFinite w := by
    have := M.locallyFinite (j w)
    have hle : (Submodule.span ℂ (range fun k : K => σ k w)).map j ≤
        Submodule.span ℂ (range fun k : K => M.σ k (j w)) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨k, rfl⟩
      rw [hσ]
      exact Submodule.subset_span ⟨k, rfl⟩
    have : FiniteDimensional ℂ ((Submodule.span ℂ (range fun k : K => σ k w)).map j) :=
      Submodule.finiteDimensional_of_le hle
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective j hj _).symm
  hasContinuousCoeff φ w := by
    obtain ⟨j', hj'⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.2 hj)
    have e : (fun k : K => φ (σ k w)) = fun k => (φ ∘ₗ j') (M.σ k (j w)) := by
      funext k
      rw [← hσ, LinearMap.comp_apply, ← LinearMap.comp_apply j' j, hj', LinearMap.id_apply]
    rw [e]
    exact M.hasContinuousCoeff _ _
  hasDerivAt_coeff X hX φ w := by
    obtain ⟨j', hj'⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.2 hj)
    have key : ∀ v, φ v = (φ ∘ₗ j') (j v) := fun v => by
      rw [LinearMap.comp_apply, ← LinearMap.comp_apply j' j, hj', LinearMap.id_apply]
    have := M.hasDerivAt_coeff X hX (φ ∘ₗ j') (j w)
    simp only [key, hσ, hρ]
    exact this
  map_ρ k X w := hj (by rw [hσ, hρ, hρ, hσ, M.map_ρ])

end IsExpLieAlgebra

namespace AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

open Reduction

instance : LocallyCompactSpace (ArchMatrix K n)ˣ :=
  Units.isOpenEmbedding_val.locallyCompactSpace

instance : LocallyCompactSpace (archGroup K n) :=
  (isOpen_univ : IsOpen (univ : Set (ArchMatrix K n)ˣ)).locallyCompactSpace

instance : SecondCountableTopology (ArchMatrix K n)ˣ :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

instance : SecondCountableTopology (archGroup K n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

theorem finAt_infEmb (v : HeightOneSpectrum (𝓞 K)) (y : archGroup K n) :
    finAt v (infEmb K n y) = 1 := by
  show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (infEmb K n y)).2) v = 1
  rw [prodEquiv_infEmb, map_one]
  rfl

theorem continuous_infAt_infEmb (w : InfinitePlace K) :
    Continuous fun y : archGroup K n => infAt w (infEmb K n y) :=
  (continuous_infAt w).comp continuous_infEmb

theorem exists_height_infEmb_le {S : Set (archGroup K n)} (hS : IsCompact S) :
    ∃ M : ℝ, ∀ y ∈ S, height (infEmb K n y) ≤ M := by
  classical
  set F : archGroup K n → ℝ := fun y => 1 + ∑ w : InfinitePlace K, ∑ i : Fin n, ∑ j : Fin n,
    (‖(infAt w (infEmb K n y) : Matrix (Fin n) (Fin n) w.Completion) i j‖ +
      ‖(((infAt w (infEmb K n y))⁻¹ : GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion) i j‖)
  have hF : Continuous F := continuous_const.add (continuous_finsetSum _ fun w _ =>
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (((continuous_GL_apply i j).comp (continuous_infAt_infEmb w)).norm).add
        (((continuous_GL_apply i j).comp (continuous_infAt_infEmb w).inv).norm))
  obtain ⟨c, hc⟩ := hS.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨∏ w : InfinitePlace K, (max 1 c) ^ w.mult, fun y hy => ?_⟩
  have hFy : F y ≤ max 1 c := (le_trans (le_abs_self _) (by simpa using hc y hy)).trans
    (le_max_right _ _)
  have hterm : ∀ w i j, ‖(infAt w (infEmb K n y) : Matrix (Fin n) (Fin n) w.Completion) i j‖ +
      ‖(((infAt w (infEmb K n y))⁻¹ : GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion) i j‖
        ≤ F y := by
    intro w i j
    have h1 := Finset.single_le_sum (f := fun j =>
      ‖(infAt w (infEmb K n y) : Matrix (Fin n) (Fin n) w.Completion) i j‖ +
      ‖(((infAt w (infEmb K n y))⁻¹ : GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion) i j‖)
      (fun _ _ => by positivity) (Finset.mem_univ j)
    have h2 := Finset.single_le_sum (f := fun i => ∑ j : Fin n,
      (‖(infAt w (infEmb K n y) : Matrix (Fin n) (Fin n) w.Completion) i j‖ +
      ‖(((infAt w (infEmb K n y))⁻¹ : GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion) i j‖))
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)
    have h3 := Finset.single_le_sum (f := fun w : InfinitePlace K => ∑ i : Fin n, ∑ j : Fin n,
      (‖(infAt w (infEmb K n y) : Matrix (Fin n) (Fin n) w.Completion) i j‖ +
      ‖(((infAt w (infEmb K n y))⁻¹ : GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion) i j‖))
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
      (Finset.mem_univ w)
    simp only [F]
    linarith
  have hloc : ∀ w, locHeight (infAt w (infEmb K n y)) ≤ max 1 c := fun w =>
    locHeight_le (le_max_left _ _)
      (fun i j => le_trans (le_add_of_nonneg_right (norm_nonneg _)) ((hterm w i j).trans hFy))
      (fun i j => le_trans (le_add_of_nonneg_left (norm_nonneg _)) ((hterm w i j).trans hFy))
  unfold height
  rw [finprod_eq_one_of_forall_eq_one (fun v => by rw [finAt_infEmb, locHeight_one]), mul_one]
  exact Finset.prod_le_prod (fun w _ => pow_nonneg (locHeight_pos _).le _)
    fun w _ => pow_le_pow_left₀ (locHeight_pos _).le (hloc w) _

section Integral

variable [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)]

theorem HasModerateGrowth.of_eq_integral {φ ψ : AdelicGLn.AdelicGL K n → ℂ}
    (hφ : HasModerateGrowth φ) (μ : Measure (archGroup K n)) [μ.IsHaarMeasure]
    {D : archGroup K n → ℂ} (hD : Continuous D) (hDc : HasCompactSupport D)
    (hψ : ∀ g, ψ g = ∫ y, φ (g * infEmb K n y) * D y ∂μ) : HasModerateGrowth ψ := by
  obtain ⟨C, N, hC⟩ := hφ
  obtain ⟨M, hM⟩ := exists_height_infEmb_le (K := K) (n := n) hDc.isCompact
  set M' := max M 1
  have hc0 : 0 ≤ heightConst K n := le_trans zero_le_one one_le_heightConst
  refine ⟨|C| * (heightConst K n * M') ^ N * ∫ y, ‖D y‖ ∂μ, N, fun g => ?_⟩
  rw [hψ]
  have hb : ∀ y, ‖φ (g * infEmb K n y) * D y‖ ≤
      |C| * (heightConst K n * M') ^ N * height g ^ N * ‖D y‖ := by
    intro y
    by_cases hy : y ∈ tsupport D
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have hhg := height_pos g
      calc ‖φ (g * infEmb K n y)‖ ≤ C * height (g * infEmb K n y) ^ N := hC _
        _ ≤ |C| * height (g * infEmb K n y) ^ N :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (height_pos _).le _)
        _ ≤ |C| * (heightConst K n * height g * M') ^ N := by
            refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le ?_ _) (abs_nonneg _)
            calc height (g * infEmb K n y)
                ≤ heightConst K n * height g * height (infEmb K n y) := height_mul_le _ _
              _ ≤ heightConst K n * height g * M' :=
                  mul_le_mul_of_nonneg_left ((hM y hy).trans (le_max_left _ _))
                    (mul_nonneg hc0 hhg.le)
        _ = |C| * (heightConst K n * M') ^ N * height g ^ N := by ring
    · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, norm_zero, mul_zero]
  have hint : Integrable (fun y => ‖D y‖) μ := hD.norm.integrable_of_hasCompactSupport hDc.norm
  calc ‖∫ y, φ (g * infEmb K n y) * D y ∂μ‖
      ≤ ∫ y, |C| * (heightConst K n * M') ^ N * height g ^ N * ‖D y‖ ∂μ :=
        norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall hb)
    _ = |C| * (heightConst K n * M') ^ N * (∫ y, ‖D y‖ ∂μ) * height g ^ N := by
        rw [integral_const_mul]; ring

theorem IsCuspidal.of_eq_integral {φ ψ : AdelicGLn.AdelicGL K n → ℂ} (hφc : Continuous φ)
    (hφ : IsCuspidal φ) (μ : Measure (archGroup K n)) [μ.IsHaarMeasure]
    {D : archGroup K n → ℂ} (hD : Continuous D) (hDc : HasCompactSupport D)
    (hψ : ∀ g, ψ g = ∫ y, φ (g * infEmb K n y) * D y ∂μ) : IsCuspidal ψ := by
  intro r hr hrn g
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  set F : (UPos n r → 𝔸[K]) × archGroup K n → ℂ :=
    fun p => φ (unipGL p.1 * g * infEmb K n p.2) * D p.2 with hF
  have hFc : Continuous F :=
    (hφc.comp ((continuous_unipGL.comp continuous_fst).mul continuous_const |>.mul
      (continuous_infEmb.comp continuous_snd))).mul (hD.comp continuous_snd)
  have hint : Integrable F ((unipMeasure K n r).restrict (unipFundamentalDomain K n r) |>.prod μ) := by
    have e : ((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod μ =
        ((unipMeasure K n r).prod μ).restrict (unipFundamentalDomain K n r ×ˢ univ) := by
      rw [← Measure.restrict_univ (μ := μ), Measure.prod_restrict, Measure.restrict_univ]
    rw [e]
    refine IntegrableOn.of_forall_sdiff_eq_zero
      (hFc.continuousOn.integrableOn_compact (hC.prod hDc.isCompact))
      (measurableSet_unipFundamentalDomain.prod MeasurableSet.univ) fun p hp => ?_
    have hy : p.2 ∉ tsupport D := fun hy => hp.2 ⟨hDC hp.1.1, hy⟩
    simp [hF, image_eq_zero_of_notMem_tsupport hy]
  show ∫ X in unipFundamentalDomain K n r, ψ (unipGL X * g) ∂unipMeasure K n r = 0
  simp_rw [hψ]
  have := integral_integral_swap (f := fun X y => F (X, y)) hint
  simp only [hF] at this
  rw [this]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
  show ∫ x in unipFundamentalDomain K n r, φ (unipGL x * g * infEmb K n y) * D y ∂unipMeasure K n r = 0
  rw [integral_mul_const]
  have h0 := hφ r hr hrn (g * infEmb K n y)
  simp only [constantTerm, ← mul_assoc] at h0
  simp [h0]

end Integral

theorem exists_integral_uAction_ι [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)]
    {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsSmoothKZ φ) (μ : Measure (archGroup K n))
    [μ.IsHaarMeasure] (X : (isExpLieAlgebra K n).lieSubalgebra) :
    ∃ D : archGroup K n → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g,
      (AutomorphicForm.uAction (UniversalEnvelopingAlgebra.ι ℝ X) ⟨φ, hφ.isSmooth.1⟩ :
        AdelicGLn.AdelicGL K n → ℂ) g = ∫ y, φ (g * infEmb K n y) * D y ∂μ := by
  obtain ⟨d, b, ε, B, hε, horth, hsymm, hinv, hK⟩ := exists_archCartanData K n
  obtain ⟨P, hPm, hPd, hP⟩ := hφ.exists_aeval_laplacian_sliceL_eq_zero b ε B hε horth hsymm hinv hK
  obtain ⟨κ, hκs, hκc, -, hκ⟩ := (isExpLieAlgebra K n).exists_kernel_eq_conv_of_aeval_laplacian μ b P
    hPm hPd Filter.univ_mem
  refine ⟨(isExpLieAlgebra K n).convDeriv ((isExpLieAlgebra K n).ofLie X) κ,
    IsExpLieAlgebra.continuous_convDeriv hκs _, IsExpLieAlgebra.hasCompactSupport_convDeriv hκc _,
    fun g => ?_⟩
  rw [uAction_ι_apply]
  have hconv : ∀ x, archSlice φ g x = ∫ y, archSlice φ g (x * y) * κ y ∂μ :=
    fun x => hκ (sliceL g ⟨φ, hφ.isSmooth.1⟩) (hP g) x
  rw [IsExpLieAlgebra.rightDeriv_eq_integral_convDeriv hκs hκc (hφ.isSmooth.1 g) hconv]
  simp only [archSlice_apply, one_mul]

theorem IsAutomorphicForm.uAction_ι {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsAutomorphicForm φ)
    (X : (isExpLieAlgebra K n).lieSubalgebra) :
    IsAutomorphicForm (AutomorphicForm.uAction (UniversalEnvelopingAlgebra.ι ℝ X)
      ⟨φ, hφ.isSmooth.1⟩ : AdelicGLn.AdelicGL K n → ℂ) := by
  let _ : MeasurableSpace (archGroup K n) := borel _
  have _ : BorelSpace (archGroup K n) := ⟨rfl⟩
  obtain ⟨D, hD, hDc, hrep⟩ := exists_integral_uAction_ι hφ.isSmoothKZ Measure.haar X
  rw [isAutomorphicForm_iff]
  exact ⟨hφ.isSmoothKZ.uAction _, hφ.hasModerateGrowth.of_eq_integral Measure.haar hD hDc hrep⟩

theorem mem_cuspForms_uAction_ι {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : φ ∈ cuspForms K n)
    (X : (isExpLieAlgebra K n).lieSubalgebra) :
    (AutomorphicForm.uAction (UniversalEnvelopingAlgebra.ι ℝ X) ⟨φ, hφ.1.isSmooth.1⟩ :
      AdelicGLn.AdelicGL K n → ℂ) ∈ cuspForms K n := by
  let _ : MeasurableSpace (archGroup K n) := borel _
  have _ : BorelSpace (archGroup K n) := ⟨rfl⟩
  obtain ⟨D, hD, hDc, hrep⟩ := exists_integral_uAction_ι hφ.1.isSmoothKZ Measure.haar X
  exact ⟨hφ.1.uAction_ι X, IsCuspidal.of_eq_integral hφ.1.continuous hφ.2 Measure.haar hD hDc hrep⟩

theorem coe_uAction_algebraMap (r : ℝ) (φ : archSmooth K n) :
    ((AutomorphicForm.uAction (algebraMap ℝ (UEnv K n) r) φ : archSmooth K n) :
      AdelicGLn.AdelicGL K n → ℂ) = (r : ℂ) • (φ : AdelicGLn.AdelicGL K n → ℂ) := by
  rw [AlgHom.commutes, Module.algebraMap_end_apply]
  funext g
  simp [Complex.real_smul]

theorem coe_uAction_mul (a b : UEnv K n) (φ : archSmooth K n) :
    ((AutomorphicForm.uAction (a * b) φ : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) =
      ((AutomorphicForm.uAction a (AutomorphicForm.uAction b φ) : archSmooth K n) :
        AdelicGLn.AdelicGL K n → ℂ) := by
  rw [map_mul, Module.End.mul_apply]

theorem IsAutomorphicForm.uAction (u : UEnv K n) :
    ∀ {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsAutomorphicForm φ),
      IsAutomorphicForm (AutomorphicForm.uAction u ⟨φ, hφ.isSmooth.1⟩ :
        AdelicGLn.AdelicGL K n → ℂ) := by
  induction u using UEnv.induction with
  | halg r =>
    intro φ hφ
    rw [coe_uAction_algebraMap]
    exact hφ.smul _
  | hι X => exact fun hφ => hφ.uAction_ι X
  | hmul a b ha hb =>
    intro φ hφ
    rw [coe_uAction_mul]
    exact ha (hb hφ)
  | hadd a b ha hb =>
    intro φ hφ
    rw [map_add, LinearMap.add_apply, Submodule.coe_add]
    exact (ha hφ).add (hb hφ)

theorem mem_cuspForms_uAction (u : UEnv K n) :
    ∀ {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : φ ∈ cuspForms K n),
      (AutomorphicForm.uAction u ⟨φ, hφ.1.isSmooth.1⟩ : AdelicGLn.AdelicGL K n → ℂ) ∈
        cuspForms K n := by
  induction u using UEnv.induction with
  | halg r =>
    intro φ hφ
    rw [coe_uAction_algebraMap]
    exact (cuspForms K n).smul_mem _ hφ
  | hι X => exact fun hφ => mem_cuspForms_uAction_ι hφ X
  | hmul a b ha hb =>
    intro φ hφ
    rw [coe_uAction_mul]
    exact ha (hb hφ)
  | hadd a b ha hb =>
    intro φ hφ
    rw [map_add, LinearMap.add_apply, Submodule.coe_add]
    exact (cuspForms K n).add_mem (ha hφ) (hb hφ)

theorem automorphicForms_le_archSmooth : automorphicForms K n ≤ archSmooth K n :=
  fun _ hφ => hφ.isSmooth.1

variable (K n) in

def uActionAF : UEnv K n →ₐ[ℝ] Module.End ℂ (automorphicForms K n) where
  toFun u := LinearMap.codRestrict (automorphicForms K n)
    ((archSmooth K n).subtype ∘ₗ AutomorphicForm.uAction u ∘ₗ
      Submodule.inclusion automorphicForms_le_archSmooth) fun φ => φ.2.uAction u
  map_one' := LinearMap.ext fun φ => Subtype.ext (by
    show ((AutomorphicForm.uAction 1 _ : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) = φ
    rw [map_one]; rfl)
  map_mul' u v := LinearMap.ext fun φ => Subtype.ext (by
    show ((AutomorphicForm.uAction (u * v) _ : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) =
      ((AutomorphicForm.uAction u (AutomorphicForm.uAction v _) : archSmooth K n) :
        AdelicGLn.AdelicGL K n → ℂ)
    rw [map_mul]; rfl)
  map_zero' := LinearMap.ext fun φ => Subtype.ext (by
    show ((AutomorphicForm.uAction 0 _ : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) = 0
    rw [map_zero]; rfl)
  map_add' u v := LinearMap.ext fun φ => Subtype.ext (by
    show ((AutomorphicForm.uAction (u + v) _ : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) = _
    rw [map_add]; rfl)
  commutes' r := LinearMap.ext fun φ => Subtype.ext (by
    show ((AutomorphicForm.uAction (algebraMap ℝ (UEnv K n) r) _ : archSmooth K n) :
      AdelicGLn.AdelicGL K n → ℂ) = _
    rw [AlgHom.commutes]; rfl)

@[simp] theorem coe_uActionAF (u : UEnv K n) (φ : automorphicForms K n) :
    ((uActionAF K n u φ : automorphicForms K n) : AdelicGLn.AdelicGL K n → ℂ) =
      ((AutomorphicForm.uAction u ⟨φ, φ.2.isSmooth.1⟩ : archSmooth K n) :
        AdelicGLn.AdelicGL K n → ℂ) := rfl

variable (K n) in

def uActionCusp : UEnv K n →ₐ[ℝ] Module.End ℂ (cuspForms K n) where
  toFun u := LinearMap.codRestrict (cuspForms K n)
    ((archSmooth K n).subtype ∘ₗ AutomorphicForm.uAction u ∘ₗ
      Submodule.inclusion (cuspForms_le_automorphicForms.trans automorphicForms_le_archSmooth))
    fun φ => mem_cuspForms_uAction u φ.2
  map_one' := LinearMap.ext fun φ => Subtype.ext (by
    show ((AutomorphicForm.uAction 1 _ : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) = φ
    rw [map_one]; rfl)
  map_mul' u v := LinearMap.ext fun φ => Subtype.ext (by
    show ((AutomorphicForm.uAction (u * v) _ : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) =
      ((AutomorphicForm.uAction u (AutomorphicForm.uAction v _) : archSmooth K n) :
        AdelicGLn.AdelicGL K n → ℂ)
    rw [map_mul]; rfl)
  map_zero' := LinearMap.ext fun φ => Subtype.ext (by
    show ((AutomorphicForm.uAction 0 _ : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) = 0
    rw [map_zero]; rfl)
  map_add' u v := LinearMap.ext fun φ => Subtype.ext (by
    show ((AutomorphicForm.uAction (u + v) _ : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) = _
    rw [map_add]; rfl)
  commutes' r := LinearMap.ext fun φ => Subtype.ext (by
    show ((AutomorphicForm.uAction (algebraMap ℝ (UEnv K n) r) _ : archSmooth K n) :
      AdelicGLn.AdelicGL K n → ℂ) = _
    rw [AlgHom.commutes]; rfl)

@[simp] theorem coe_uActionCusp (u : UEnv K n) (φ : cuspForms K n) :
    ((uActionCusp K n u φ : cuspForms K n) : AdelicGLn.AdelicGL K n → ℂ) =
      ((AutomorphicForm.uAction u ⟨φ, φ.2.1.isSmooth.1⟩ : archSmooth K n) :
        AdelicGLn.AdelicGL K n → ℂ) := rfl

theorem uActionAF_finRep (u : UEnv K n) (h : AdelicGLn.FiniteAdelicGL K n)
    (φ : automorphicForms K n) :
    uActionAF K n u (finRep K n h φ) = finRep K n h (uActionAF K n u φ) := by
  apply Subtype.ext
  exact congrArg (fun ψ : archSmooth K n => (ψ : AdelicGLn.AdelicGL K n → ℂ))
    (uAction_rtFin u h ⟨φ, φ.2.isSmooth.1⟩)

theorem uActionCusp_finRepCusp (u : UEnv K n) (h : AdelicGLn.FiniteAdelicGL K n)
    (φ : cuspForms K n) :
    uActionCusp K n u (finRepCusp K n h φ) = finRepCusp K n h (uActionCusp K n u φ) := by
  apply Subtype.ext
  exact congrArg (fun ψ : archSmooth K n => (ψ : AdelicGLn.AdelicGL K n → ℂ))
    (uAction_rtFin u h ⟨φ, φ.2.1.isSmooth.1⟩)

section GK

variable (K n) in

def lieActionAF : (isExpLieAlgebra K n).lieSubalgebra →ₗ⁅ℝ⁆ Module.End ℂ (automorphicForms K n) where
  toFun X := uActionAF K n (UniversalEnvelopingAlgebra.ι ℝ X)
  map_add' X Y := by rw [map_add, map_add]
  map_smul' r X := by rw [map_smul, map_smul]; rfl
  map_lie' {X Y} := by
    rw [LieHom.map_lie, Ring.lie_def, Ring.lie_def, map_sub, map_mul, map_mul]

variable (K n) in

def lieActionCusp : (isExpLieAlgebra K n).lieSubalgebra →ₗ⁅ℝ⁆ Module.End ℂ (cuspForms K n) where
  toFun X := uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ X)
  map_add' X Y := by rw [map_add, map_add]
  map_smul' r X := by rw [map_smul, map_smul]; rfl
  map_lie' {X Y} := by
    rw [LieHom.map_lie, Ring.lie_def, Ring.lie_def, map_sub, map_mul, map_mul]

variable (K n) in

def gkModuleAF : (isExpLieAlgebra K n).GKModule (archCompact K n) (automorphicForms K n) :=
  IsExpLieAlgebra.GKModule.comap (isExpLieAlgebra K n) (gkModule K n) (Submodule.inclusion automorphicForms_le_smoothKZ)
    (Submodule.inclusion_injective _) (lieActionAF K n) (archCompactRep K n)
    (fun _ _ => Subtype.ext rfl) (fun _ _ => Subtype.ext rfl)

variable (K n) in

def gkModuleCusp : (isExpLieAlgebra K n).GKModule (archCompact K n) (cuspForms K n) :=
  IsExpLieAlgebra.GKModule.comap (isExpLieAlgebra K n) (gkModule K n)
    (Submodule.inclusion (cuspForms_le_automorphicForms.trans automorphicForms_le_smoothKZ))
    (Submodule.inclusion_injective _) (lieActionCusp K n) (archCompactRepCusp K n)
    (fun _ _ => Subtype.ext rfl) (fun _ _ => Subtype.ext rfl)

@[simp] theorem gkModuleAF_ρ_apply (X : (isExpLieAlgebra K n).lieSubalgebra)
    (φ : automorphicForms K n) :
    (gkModuleAF K n).ρ X φ = uActionAF K n (UniversalEnvelopingAlgebra.ι ℝ X) φ := rfl

@[simp] theorem gkModuleAF_σ_apply (k : archCompact K n) (φ : automorphicForms K n) :
    (gkModuleAF K n).σ k φ = archCompactRep K n k φ := rfl

@[simp] theorem gkModuleCusp_ρ_apply (X : (isExpLieAlgebra K n).lieSubalgebra)
    (φ : cuspForms K n) :
    (gkModuleCusp K n).ρ X φ = uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ X) φ := rfl

@[simp] theorem gkModuleCusp_σ_apply (k : archCompact K n) (φ : cuspForms K n) :
    (gkModuleCusp K n).σ k φ = archCompactRepCusp K n k φ := rfl

theorem gkModuleAF_ρ_finRep (X : (isExpLieAlgebra K n).lieSubalgebra)
    (h : AdelicGLn.FiniteAdelicGL K n) (φ : automorphicForms K n) :
    (gkModuleAF K n).ρ X (finRep K n h φ) = finRep K n h ((gkModuleAF K n).ρ X φ) :=
  uActionAF_finRep _ h φ

theorem gkModuleAF_σ_finRep (k : archCompact K n) (h : AdelicGLn.FiniteAdelicGL K n)
    (φ : automorphicForms K n) :
    (gkModuleAF K n).σ k (finRep K n h φ) = finRep K n h ((gkModuleAF K n).σ k φ) :=
  (finRep_archCompactRep_comm h k φ).symm

theorem gkModuleCusp_ρ_finRepCusp (X : (isExpLieAlgebra K n).lieSubalgebra)
    (h : AdelicGLn.FiniteAdelicGL K n) (φ : cuspForms K n) :
    (gkModuleCusp K n).ρ X (finRepCusp K n h φ) = finRepCusp K n h ((gkModuleCusp K n).ρ X φ) :=
  uActionCusp_finRepCusp _ h φ

theorem gkModuleCusp_σ_finRepCusp (k : archCompact K n) (h : AdelicGLn.FiniteAdelicGL K n)
    (φ : cuspForms K n) :
    (gkModuleCusp K n).σ k (finRepCusp K n h φ) = finRepCusp K n h ((gkModuleCusp K n).σ k φ) := by
  apply Subtype.ext
  funext g
  simp only [gkModuleCusp_σ_apply]
  show (φ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n k * finEmb K n h) =
    (φ : AdelicGLn.AdelicGL K n → ℂ) (g * finEmb K n h * infEmb K n k)
  rw [mul_assoc, mul_assoc, infEmb_mul_finEmb_comm]

end GK

end AutomorphicForm

end

end GroundTheory.Automorphic

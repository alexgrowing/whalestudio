import Mathlib
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SigmaFiniteQuotients.Exists
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc

open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff Manifold Convolution

noncomputable section

namespace CompanionTheory.D.Upq.Sm

open PI CompanionTheory.D.Upq.ModEx

theorem SmOn.exists_contDiff {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] {A : Set E} {f : E → V}
    (hf : SmOn A f) (hA : IsClosed A) : ∃ F : E → V, ContDiff ℝ ∞ F ∧ ∀ a ∈ A, F a = f a := by
  obtain ⟨F, hF⟩ := exists_contMDiffMap_forall_mem_convex_of_local (n := ⊤) 𝓘(ℝ, E)
    (t := fun a => {v | a ∈ A → v = f a})
    (fun a v hv w hw s t _ _ hst ha => by rw [hv ha, hw ha, ← add_smul, hst, one_smul])
    (fun a => by
      by_cases ha : a ∈ A
      · obtain ⟨U, F, hU, haU, hF, hfF⟩ := hf a ha
        exact ⟨U, hU.mem_nhds haU, F, hF.contMDiffOn, fun y hy hyA => (hfF y hy hyA).symm⟩
      · exact ⟨Aᶜ, hA.isOpen_compl.mem_nhds ha, fun _ => 0, contMDiffOn_const,
          fun y hy hyA => absurd hyA hy⟩)
  exact ⟨F, F.contMDiff.contDiff, fun a ha => hF a ha⟩

theorem contDiff_integral_param {P E V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] {f : E → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    {F : P × E → V} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ fun p => ∫ t, f t • F (p, t) ∂μ := by
  obtain ⟨R, hR0, hR⟩ := hc.isCompact.isBounded.subset_closedBall_lt 0 (0 : E)
  let χ : ContDiffBump (0 : E) := ⟨R, R + 1, hR0, by linarith⟩
  have h := contDiffOn_convolution_right_with_param_comp (𝕜 := ℝ) (μ := μ) (n := ⊤)
    (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] V →L[ℝ] V) (s := (univ : Set P))
    (v := fun _ => (0 : E)) contDiffOn_const (f := f) (g := fun p x => χ x • F (p, -x))
    (k := Metric.closedBall 0 (R + 1)) isOpen_univ (isCompact_closedBall _ _)
    (fun p x _ hx => by
      rw [χ.zero_of_le_dist (not_lt.1 fun h => hx (Metric.mem_closedBall.2 h.le)), zero_smul])
    (hf.integrable_of_hasCompactSupport hc).locallyIntegrable
    (((χ.contDiff.comp contDiff_snd).smul
      (hF.comp (contDiff_fst.prodMk contDiff_snd.neg))).contDiffOn)
  rw [contDiffOn_univ] at h
  convert h using 2 with p
  rw [convolution_def]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [zero_sub, neg_neg, ContinuousLinearMap.lsmul_apply]
  by_cases ht : t ∈ tsupport f
  · rw [χ.one_of_mem_closedBall (by simpa using hR ht), one_smul]
  · rw [image_eq_zero_of_notMem_tsupport ht, zero_smul, zero_smul]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)} {hG : IsMatGroup G}

section Group

variable {μ : Measure (MG G hG)} [IsFiniteMeasureOnCompacts μ] {φ : MG G hG → ℂ}

theorem integrable_csmul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (hφ : Continuous φ)
    (hc : HasCompactSupport φ) {f : MG G hG → V} (hf : Continuous f) :
    Integrable (fun g => φ g • f g) μ :=
  (hφ.smul hf).integrable_of_hasCompactSupport hc.smul_right

theorem dsW_integral (h : RepOn G σ) {v : H} (hv : IsSm G σ v) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) : ∀ {W : List (Mat n)}, LieW G W →
    dsW σ W (∫ g, φ g • σ g.mat v ∂μ) = ∫ g, φ g • dsW σ W (σ g.mat v) ∂μ
  | [], _ => rfl
  | X :: W, hXW => by
    have hW : LieW G W := fun Y hY => hXW Y (List.mem_cons_of_mem _ hY)
    have hX := hXW X List.mem_cons_self
    rw [dsW_cons, dsW_integral h hv hφ hc hW]
    have e : ∀ t, σ (ex X t) (∫ g, φ g • dsW σ W (σ g.mat v) ∂μ) =
        ∫ g, φ g • σ (ex X t) (dsW σ W (σ g.mat v)) ∂μ := fun t => by
      rw [← (σ (ex X t)).integral_comp_comm (integrable_csmul hφ hc (continuous_orbit h hv hW))]
      simp only [map_smul]
    have := hasDerivAt_integral_cpt (μ := μ)
      (F := fun t g => φ g • σ (ex X t) (dsW σ W (σ g.mat v)))
      (F' := fun t g => φ g • σ (ex X t) (dsW σ (X :: W) (σ g.mat v)))
      (fun t => hφ.smul ((continuous_orbit₂ h hv hW hX).comp (Continuous.prodMk_right t)))
      ((hφ.comp continuous_snd).smul (continuous_orbit₂ h hv hXW hX))
      (fun t a => (((hv.apply h a.mem).dsW h hW).hasDerivAt h hX t).fun_const_smul _)
      hc.isCompact
      (fun a ha => by rw [image_eq_zero_of_notMem_tsupport ha, zero_smul])
      (fun t _ a ha => by rw [image_eq_zero_of_notMem_tsupport ha, zero_smul])
    unfold ds
    simp_rw [e]
    rw [this.deriv]
    simp [ex_zero, h.map_one]

theorem map_integral_of_bound (h : RepOn G σ) {v : H} (hv : IsSm G σ v) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hy : IsSm G σ (∫ g, φ g • σ g.mat v ∂μ)) {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {B : H → V}
    (hadd : ∀ x, IsSm G σ x → ∀ y, IsSm G σ y → B (x + y) = B x + B y)
    (hsmul : ∀ (a : ℂ) x, IsSm G σ x → B (a • x) = a • B x) {ι : Type} [Fintype ι]
    {W : ι → List (Mat n)} (hW : ∀ i, LieW G (W i)) {C : ℝ}
    (hB : ∀ x, IsSm G σ x → ‖B x‖ ≤ C * ∑ i, ‖dsW σ (W i) x‖) :
    B (∫ g, φ g • σ g.mat v ∂μ) = ∫ g, φ g • B (σ g.mat v) ∂μ := by
  let J : H → ι → H := fun v i => dsW σ (W i) v
  let S₀ : Submodule ℂ ((ι → H) × V) :=
    { carrier := {q | ∃ x, IsSm G σ x ∧ q = (J x, B x)}
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, ha.add hb, Prod.ext (funext fun i => (dsW_add h ha hb (hW i)).symm)
          (hadd a ha b hb).symm⟩
      zero_mem' := ⟨0, IsSm.zero, Prod.ext (funext fun i => by
          simpa using (dsW_smul h (IsSm.zero (G := G) (σ := σ)) 0 (hW i)).symm) (by
          simpa using (hsmul 0 0 IsSm.zero).symm)⟩
      smul_mem' := by
        rintro c _ ⟨a, ha, rfl⟩
        exact ⟨c • a, ha.smul c, Prod.ext (funext fun i => (dsW_smul h ha c (hW i)).symm)
          (hsmul c a ha).symm⟩ }
  have hbd : ∀ q ∈ S₀.topologicalClosure, ‖q.2‖ ≤ C * ∑ i, ‖q.1 i‖ := fun q hq =>
    closure_minimal (t := {q : (ι → H) × V | ‖q.2‖ ≤ C * ∑ i, ‖q.1 i‖})
      (by rintro _ ⟨a, ha, rfl⟩; exact hB a ha) (isClosed_le (by fun_prop) (by fun_prop)) hq
  have hJc : Continuous fun g : MG G hG => J (σ g.mat v) :=
    continuous_pi fun i => continuous_orbit h hv (hW i)
  have hBc : Continuous fun g : MG G hG => B (σ g.mat v) := by
    refine continuous_iff_continuousAt.2 fun g₀ => ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hT : Continuous fun g : MG G hG =>
        C * ∑ i, ‖dsW σ (W i) (σ g.mat v) - dsW σ (W i) (σ g₀.mat v)‖ :=
      continuous_const.mul (continuous_finset_sum _ fun i _ =>
        ((continuous_orbit h hv (hW i)).sub continuous_const).norm)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun g => ?_) (by simpa using hT.tendsto g₀)
    exact hbd ((J (σ g.mat v), B (σ g.mat v)) - (J (σ g₀.mat v), B (σ g₀.mat v)))
      (S₀.le_topologicalClosure
        (sub_mem ⟨_, hv.apply h g.mem, rfl⟩ ⟨_, hv.apply h g₀.mem, rfl⟩))
  have hi1 := integrable_csmul (μ := μ) hφ hc hJc
  have hi2 := integrable_csmul (μ := μ) hφ hc hBc
  have h1 : ∫ g, φ g • (J (σ g.mat v), B (σ g.mat v)) ∂μ ∈ S₀.topologicalClosure :=
    integral_mem_of_isClosed _ S₀.isClosed_topologicalClosure fun g =>
      Submodule.smul_mem _ _ (S₀.le_topologicalClosure ⟨_, hv.apply h g.mem, rfl⟩)
  simp only [Prod.smul_mk] at h1
  rw [integral_pair hi1 hi2] at h1
  have h2 : ∫ g, φ g • J (σ g.mat v) ∂μ = J (∫ g, φ g • σ g.mat v ∂μ) := by
    ext1 i
    have := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => H) i).integral_comp_comm hi1
    simp only [ContinuousLinearMap.proj_apply, Pi.smul_apply] at this
    rw [← this]
    exact (dsW_integral h hv hφ hc (hW i)).symm
  rw [h2] at h1
  have h3 := hbd _ (sub_mem (S₀.le_topologicalClosure ⟨_, hy, rfl⟩) h1)
  simpa [sub_eq_zero] using h3

end Group

theorem isSm_integral (hG : IsMatGroup G) (h : RepOn G σ) {v : H} (hv : IsSm G σ v)
    {μ : Measure (MtM n)} (hμ : IsHaarOnM G μ) {f : MtM n → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) : IsSm G σ (∫ g, f g • σ (Matrix.of g) v ∂μ) := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun _ hK => Quot.IsHaarOnM.lt_top_of_isCompact hG hμ hK⟩
  obtain ⟨F, hF, hFv⟩ := SmOn.exists_contDiff hv hG.1
  have hae : ∀ᵐ g ∂μ, Matrix.of g ∈ G := hμ.2.2.1
  have h1 := contDiff_integral_param (P := Mat n) (E := MtM n) (μ := μ) hf hc
    (F := fun q => F (q.1 * Matrix.of q.2)) (hF.comp contDiff_mul)
  refine (SmOn.of_contDiff h1).congr fun a ha => ?_
  have hi : Integrable (fun g : MtM n => f g • σ (Matrix.of g) v) μ := by
    have hFc : Continuous fun g : MtM n => F (Matrix.of g) := hF.continuous
    refine ((hf.smul hFc).integrable_of_hasCompactSupport hc.smul_right).congr ?_
    filter_upwards [hae] with g hg
    rw [← hFv _ hg]; rfl
  rw [← (σ a).integral_comp_comm hi]
  refine integral_congr_ae ?_
  filter_upwards [hae] with g hg
  rw [map_smul, hFv _ (h.mul_mem _ ha _ hg), h.apply_mul ha hg]

open PI.UpqRep in

theorem intertwiner_commute : Formalism.FourierDecayAlt.ThreeDimData.IntCommute := by
  intro k r ε lam H _ _ _ σ Wp _ _ _ _ μG B _ hσ hμ hadd hsmul ⟨C, Ws, hWs, hB⟩ x hx f hf hc
  obtain ⟨P, ⟨⟨hP, hPJ⟩, -⟩, -, -, ⟨⟨h1, hm⟩, -, -⟩, -⟩ := hσ
  have hG : PI.IsMatGroup (UH (Hpk k r)) := PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r
  have h : RepOn (UH (Hpk k r)) σ := repOn_of_conj hP hPJ h1 hm
  have hy := isSm_integral hG h hx hμ hf hc
  refine ⟨hy, ?_⟩
  have hι := MG.measurableEmbedding_toM (hG := hG)
  have hmap := Quot.map_comap_toM hG (μ := μG) hμ.2.2.1
  set μ' := μG.comap (MG.toM (hG := hG)) with hμ'
  haveI : IsFiniteMeasureOnCompacts μ' := ⟨fun K hK => by
    rw [hμ', hι.comap_apply]
    exact Quot.IsHaarOnM.lt_top_of_isCompact hG hμ (hK.image (MG.continuous_mat (hG := hG)))⟩
  rw [← hmap, hι.integral_map] at hy ⊢
  rw [hι.integral_map]
  refine map_integral_of_bound (hG := hG) (φ := fun g => f g.toM) h hx
    (hf.comp MG.continuous_mat) (hc.comp_isClosedEmbedding MG.isClosedEmbedding_mat) hy hadd hsmul
    (ι := Fin Ws.length) (W := Ws.get)
    (fun i X hX t => ex_mem_of_lie (hWs _ (List.get_mem _ _) X hX) t) (C := C) fun y hy => ?_
  refine (hB y hy).trans_eq ?_
  congr 1
  simp only [dsigW_eq', List.get_eq_getElem]
  exact (Fin.sum_univ_fun_getElem Ws fun W => ‖dsW σ W y‖).symm

end CompanionTheory.D.Upq.Sm

end

import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SecondCountableQuotients.ModExists
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothVec

open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff

noncomputable section

namespace CompanionTheory.D.Upq.Sm

open PI CompanionTheory.D.Upq.ModEx

section General

variable {α V : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [NormedAddCommGroup V] [NormedSpace ℝ V] {μ : Measure α}
  [IsFiniteMeasureOnCompacts μ]

theorem hasDerivAt_integral_cpt {F F' : ℝ → α → V} (hF : ∀ t, Continuous (F t))
    (hF' : Continuous fun p : ℝ × α => F' p.1 p.2) (hd : ∀ t a, HasDerivAt (F · a) (F' t a) t)
    {K : Set α} (hK : IsCompact K) (h0 : ∀ a ∉ K, F 0 a = 0)
    (h0' : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ a ∉ K, F' t a = 0) :
    HasDerivAt (fun t => ∫ a, F t a ∂μ) (∫ a, F' 0 a ∂μ) 0 := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK : IsCompact (Icc (-1 : ℝ) 1 ×ˢ K)).exists_bound_of_continuousOn
    hF'.continuousOn
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Icc (-1 : ℝ) 1)
    (bound := K.indicator fun _ => C) (Icc_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun t => (hF t).aestronglyMeasurable)
    ((hF 0).integrable_of_hasCompactSupport (HasCompactSupport.intro hK h0))
    (hF'.comp (Continuous.prodMk_right 0)).aestronglyMeasurable
    (Eventually.of_forall fun a t ht => ?_) ?_ (Eventually.of_forall fun a t _ => hd t a)).2
  · by_cases ha : a ∈ K
    · rw [indicator_of_mem ha]; exact hC (t, a) ⟨ht, ha⟩
    · rw [indicator_of_notMem ha, h0' t ht a ha, norm_zero]
  · exact (integrable_indicator_iff hK.measurableSet).2
      (continuous_const.continuousOn.integrableOn_compact hK)

end General

theorem integral_mem_of_isClosed {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] {μ : Measure α} (S : Submodule ℂ V)
    (hS : IsClosed (S : Set V)) {f : α → V} (hf : ∀ a, f a ∈ S) : ∫ a, f a ∂μ ∈ S := by
  haveI : CompleteSpace S := hS.completeSpace_coe
  have := S.subtypeₗᵢ.integral_comp_comm (μ := μ) (fun a => (⟨f a, hf a⟩ : S))
  simp only [Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype] at this
  rw [this]
  exact Subtype.property _

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem ex_add (X : Mat n) (s t : ℝ) : ex X (s + t) = ex X s * ex X t := by
  unfold ex
  rw [Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute]
  exact ((Commute.refl X).smul_left _).smul_right _

theorem hasDerivAt_ex (X : Mat n) (t : ℝ) : HasDerivAt (ex X) (ex X t * X) t := by
  have h1 : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have h2 := HasDerivAt.scomp_of_eq t (hasDerivAt_mul_ex (ex X t) X) h1 (sub_self t).symm
  have e : ex X = (fun s => ex X t * ex X s) ∘ fun s => s - t := by
    ext1 s
    rw [Function.comp, ← ex_add]
    congr 1; ring
  rw [one_smul, ← e] at h2
  exact h2

theorem continuous_ex (X : Mat n) : Continuous (ex X) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_ex X t).continuousAt

def mulR (g : Mat n) : Mat n →L[ℝ] Mat n := (LinearMap.mulRight ℝ g).toContinuousLinearMap

theorem mulR_apply (g x : Mat n) : mulR g x = x * g := rfl

theorem hasDerivAt_ex_neg_mul (X g : Mat n) (t : ℝ) :
    HasDerivAt (fun s => ex X (-s) * g) (-(X * (ex X (-t) * g))) t := by
  have h0 : HasDerivAt (ex X) X 0 := by simpa using hasDerivAt_mul_ex 1 X
  have h1 : HasDerivAt (fun s : ℝ => t - s) (-1) t := (hasDerivAt_id t).const_sub t
  have h2 : HasDerivAt (fun s => ex X (t - s)) ((-1 : ℝ) • X) t :=
    HasDerivAt.scomp_of_eq t h0 h1 (sub_self t).symm
  have h3 := (mulR (ex X (-t) * g)).hasFDerivAt.comp_hasDerivAt t h2
  have e : (fun s => ex X (-s) * g) = mulR (ex X (-t) * g) ∘ fun s => ex X (t - s) := by
    ext1 s
    rw [Function.comp, mulR_apply, ← Matrix.mul_assoc, ← ex_add]
    congr 2; ring
  rw [e]
  exact h3.congr_deriv ((mulR_apply _ _).trans (by simp))

def Lx (X : Mat n) (φ : Mat n → ℝ) : Mat n → ℝ := fun g => -(fderiv ℝ φ g (X * g))

def LW (W : List (Mat n)) (φ : Mat n → ℝ) : Mat n → ℝ := W.foldr Lx φ

theorem contDiff_Lx (X : Mat n) {φ : Mat n → ℝ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (Lx X φ) :=
  ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_mul' contDiff_const contDiff_id)).neg

theorem tsupport_Lx (X : Mat n) (φ : Mat n → ℝ) : tsupport (Lx X φ) ⊆ tsupport φ := by
  refine (closure_mono fun g hg => ?_).trans (tsupport_fderiv_subset ℝ (f := φ))
  intro h
  exact hg (by simp [Lx, h])

theorem contDiff_LW {φ : Mat n → ℝ} (hφ : ContDiff ℝ ∞ φ) : ∀ W, ContDiff ℝ ∞ (LW W φ)
  | [] => hφ
  | X :: W => contDiff_Lx X (contDiff_LW hφ W)

theorem tsupport_LW (φ : Mat n → ℝ) : ∀ W, tsupport (LW W φ) ⊆ tsupport φ
  | [] => subset_rfl
  | X :: W => (tsupport_Lx X _).trans (tsupport_LW φ W)

theorem hasCompactSupport_LW {φ : Mat n → ℝ} (hc : HasCompactSupport φ) (W : List (Mat n)) :
    HasCompactSupport (LW W φ) :=
  IsCompact.of_isClosed_subset hc (isClosed_tsupport _) (tsupport_LW φ W)

theorem hasDerivAt_Lx (X g : Mat n) {φ : Mat n → ℝ} (hφ : ContDiff ℝ ∞ φ) (t : ℝ) :
    HasDerivAt (fun s => φ (ex X (-s) * g)) (Lx X φ (ex X (-t) * g)) t := by
  have := ((hφ.differentiable (by simp)) (ex X (-t) * g)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_ex_neg_mul X g t)
  exact this.congr_deriv (map_neg _ _)

variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

theorem IsSm.hasDerivAt (h : RepOn G σ) {u : H} (hu : IsSm G σ u) {X : Mat n}
    (hX : ∀ t, ex X t ∈ G) (t : ℝ) :
    HasDerivAt (fun s => σ (ex X s) u) (σ (ex X t) (ds σ X u)) t := by
  have h0 := (hu.differentiableAt h hX).hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have h2 := HasDerivAt.scomp_of_eq t h0 h1 (sub_self t).symm
  have h3 := ((σ (ex X t)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h2
  have e : (fun s => σ (ex X s) u) = ((σ (ex X t)).restrictScalars ℝ) ∘
      ((fun t : ℝ => σ (ex X t) u) ∘ fun s => s - t) := by
    ext1 s
    simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars']
    rw [← h.apply_mul (hX t) (hX _), ← ex_add]
    congr 3; ring
  rw [e]
  simpa [ds] using h3

variable {hG : IsMatGroup G}

instance : T2Space (MG G hG) := MG.isClosedEmbedding_mat.isEmbedding.t2Space

theorem isCompact_supp {φ : Mat n → ℝ} (hc : HasCompactSupport φ) :
    IsCompact ((MG.mat : MG G hG → Mat n) ⁻¹' tsupport φ) :=
  MG.isClosedEmbedding_mat.isCompact_preimage hc

theorem integrable_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {φ : Mat n → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {f : MG G hG → V} (hf : Continuous f) :
    Integrable (fun g : MG G hG => φ g.mat • f g) haar :=
  ((hφ.comp MG.continuous_mat).smul hf).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_supp hc) fun g hg => by
      change φ g.mat • f g = 0
      rw [image_eq_zero_of_notMem_tsupport hg, zero_smul])

theorem continuous_orbit (h : RepOn G σ) {v : H} (hv : IsSm G σ v) {W : List (Mat n)}
    (hW : LieW G W) : Continuous fun g : MG G hG => dsW σ W (σ g.mat v) :=
  (continuousOn_dsW_orbit h hv hW).comp_continuous MG.continuous_mat fun g => g.mem

theorem continuous_orbit₂ (h : RepOn G σ) {v : H} (hv : IsSm G σ v) {W : List (Mat n)}
    (hW : LieW G W) {X : Mat n} (hX : ∀ t, ex X t ∈ G) :
    Continuous fun p : ℝ × MG G hG => σ (ex X p.1) (dsW σ W (σ p.2.mat v)) :=
  (smOn_dsW h (u := fun x => σ x v) (hv.smOn_mul h) hW).continuousOn.comp_continuous
    (f := fun p : ℝ × MG G hG => (ex X p.1, p.2.mat))
    (((continuous_ex X).comp continuous_fst).prodMk (MG.continuous_mat.comp continuous_snd))
    fun p => ⟨hX _, p.2.mem⟩

variable [CompleteSpace H]

theorem apply_integral (L : H →L[ℂ] H) {φ : Mat n → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) {f : MG G hG → H} (hf : Continuous f) :
    L (∫ g : MG G hG, φ g.mat • f g ∂haar) = ∫ g : MG G hG, φ g.mat • L (f g) ∂haar := by
  rw [← L.integral_comp_comm (integrable_smul hφ hc hf)]
  simp only [ContinuousLinearMap.map_smul_of_tower]

theorem hasDerivAt_A (h : RepOn G σ) {v : H} (hv : IsSm G σ v) {X : Mat n} (hX : ∀ t, ex X t ∈ G)
    {ψ : Mat n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    HasDerivAt (fun t => σ (ex X t) (∫ g : MG G hG, ψ g.mat • σ g.mat v ∂haar))
      (∫ g : MG G hG, Lx X ψ g.mat • σ g.mat v ∂haar) 0 := by
  have hf : Continuous fun g : MG G hG => σ g.mat v :=
    continuous_orbit h hv (W := []) fun _ h => by simp at h
  have e : ∀ t, σ (ex X t) (∫ g : MG G hG, ψ g.mat • σ g.mat v ∂haar) =
      ∫ g : MG G hG, ψ (ex X (-t) * g.mat) • σ g.mat v ∂haar := fun t => by
    rw [apply_integral _ hψ.continuous hc hf, ← integral_mul_left_eq_self
      (fun g : MG G hG => ψ (ex X (-t) * g.mat) • σ g.mat v) (MG.mk hG (ex X t) (hX t))]
    congr 1
    ext1 g
    rw [MG.mat_mul, MG.mat_mk, ← Matrix.mul_assoc, ← ex_add, neg_add_cancel, ex_zero,
      Matrix.one_mul, h.apply_mul (hX t) g.mem]
  simp_rw [e]
  have hγ : Continuous fun p : ℝ × MG G hG => ex X (-p.1) * p.2.mat :=
    ((continuous_ex X).comp continuous_fst.neg).matrix_mul (MG.continuous_mat.comp continuous_snd)
  let m : ℝ × MG G hG → MG G hG := fun p => MG.mk hG (ex X p.1) (hX _) * p.2
  have hm : Continuous m :=
    (MG.continuous_iff.2 ((continuous_ex X).comp continuous_fst)).mul continuous_snd
  have hK := (isCompact_Icc.prod (isCompact_supp (hG := hG) hc) :
    IsCompact (Icc (-1 : ℝ) 1 ×ˢ _)).image hm
  have hout : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ a : MG G hG,
      a ∉ m '' (Icc (-1 : ℝ) 1 ×ˢ (MG.mat ⁻¹' tsupport ψ)) → ex X (-t) * a.mat ∉ tsupport ψ := by
    intro t ht a ha hs
    refine ha ⟨(t, MG.mk hG (ex X (-t)) (hX _) * a), ⟨ht, hs⟩, MG.ext ?_⟩
    simp only [m, MG.mat_mul, MG.mat_mk]
    rw [← Matrix.mul_assoc, ← ex_add, add_neg_cancel, ex_zero, Matrix.one_mul]
  have := hasDerivAt_integral_cpt (μ := (haar : Measure (MG G hG)))
    (F := fun t g => ψ (ex X (-t) * g.mat) • σ g.mat v)
    (F' := fun t g => Lx X ψ (ex X (-t) * g.mat) • σ g.mat v)
    (fun t => (hψ.continuous.comp (hγ.comp (Continuous.prodMk_right t))).smul hf)
    (((contDiff_Lx X hψ).continuous.comp hγ).smul (hf.comp continuous_snd))
    (fun t a => (hasDerivAt_Lx X a.mat hψ t).smul_const _) hK
    (fun a ha => by
      rw [image_eq_zero_of_notMem_tsupport (hout 0 (by norm_num) a ha), zero_smul])
    (fun t ht a ha => by
      rw [image_eq_zero_of_notMem_tsupport (fun hs => hout t ht a ha (tsupport_Lx X ψ hs)),
        zero_smul])
  simpa [ex_zero] using this

theorem hasDerivAt_B (h : RepOn G σ) {v : H} (hv : IsSm G σ v) {X : Mat n} (hX : ∀ t, ex X t ∈ G)
    {W : List (Mat n)} (hW : LieW G W) {φ : Mat n → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) :
    HasDerivAt (fun t => σ (ex X t) (∫ g : MG G hG, φ g.mat • dsW σ W (σ g.mat v) ∂haar))
      (∫ g : MG G hG, φ g.mat • dsW σ (X :: W) (σ g.mat v) ∂haar) 0 := by
  have hXW : LieW G (X :: W) := fun Y hY => by
    rcases List.mem_cons.1 hY with rfl | hY
    exacts [hX, hW Y hY]
  simp_rw [apply_integral _ hφ hc (continuous_orbit h hv hW)]
  have hφ' : Continuous fun g : MG G hG => φ g.mat := hφ.comp MG.continuous_mat
  have := hasDerivAt_integral_cpt (μ := (haar : Measure (MG G hG)))
    (F := fun t g => φ g.mat • σ (ex X t) (dsW σ W (σ g.mat v)))
    (F' := fun t g => φ g.mat • σ (ex X t) (dsW σ (X :: W) (σ g.mat v)))
    (fun t => hφ'.smul ((continuous_orbit₂ h hv hW hX).comp (Continuous.prodMk_right t)))
    ((hφ'.comp continuous_snd).smul (continuous_orbit₂ h hv hXW hX))
    (fun t a => (((hv.apply h a.mem).dsW h hW).hasDerivAt h hX t).fun_const_smul _)
    (isCompact_supp hc)
    (fun a ha => by rw [image_eq_zero_of_notMem_tsupport ha, zero_smul])
    (fun t _ a ha => by rw [image_eq_zero_of_notMem_tsupport ha, zero_smul])
  simpa [ex_zero, h.map_one] using this

theorem integral_dsW (h : RepOn G σ) {v : H} (hv : IsSm G σ v) {φ : Mat n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) : ∀ {W : List (Mat n)}, LieW G W →
    ∫ g : MG G hG, φ g.mat • dsW σ W (σ g.mat v) ∂haar =
      ∫ g : MG G hG, LW W φ g.mat • σ g.mat v ∂haar
  | [], _ => rfl
  | X :: W, hXW => by
    have hW : LieW G W := fun Y hY => hXW Y (List.mem_cons_of_mem _ hY)
    have hX := hXW X List.mem_cons_self
    have h1 := hasDerivAt_B (hG := hG) h hv hX hW hφ.continuous hc
    rw [integral_dsW h hv hφ hc hW] at h1
    exact h1.unique (hasDerivAt_A h hv hX (contDiff_LW hφ W) (hasCompactSupport_LW hc W))

theorem norm_integral_dsW_le (h : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) {v : H}
    (hv : IsSm G σ v) {φ : Mat n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    {W : List (Mat n)} (hW : LieW G W) :
    ‖∫ g : MG G hG, φ g.mat • dsW σ W (σ g.mat v) ∂haar‖ ≤
      (∫ g : MG G hG, ‖LW W φ g.mat‖ ∂haar) * ‖v‖ := by
  rw [integral_dsW h hv hφ hc hW, ← integral_mul_const]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  congr 1
  ext1 g
  rw [norm_smul, hiso _ g.mem]

def orbSpan (G : Set (Mat n)) (σ : Mat n → (H →L[ℂ] H)) (w : H) : Submodule ℂ H :=
  Submodule.span ℂ ((fun g => σ g w) '' G)

omit [CompleteSpace H] in
theorem isSm_of_mem_orbSpan (h : RepOn G σ) {w : H} (hw : IsSm G σ w) {y : H}
    (hy : y ∈ orbSpan G σ w) : IsSm G σ y := by
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨g, hg, rfl⟩ := hx; exact hw.apply h hg
  | zero => exact IsSm.zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

omit [CompleteSpace H] in
theorem apply_mem_orbSpan (h : RepOn G σ) {w : H} {a : Mat n} (ha : a ∈ G) {y : H}
    (hy : y ∈ orbSpan G σ w) : σ a y ∈ orbSpan G σ w := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact Submodule.subset_span ⟨a * g, h.mul_mem _ ha _ hg, h.apply_mul ha hg w⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem exists_approx (hG : IsMatGroup G) (h : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖)
    {w : H} (hw : IsSm G σ w) (hd : Dense (orbSpan G σ w : Set H)) {x : H} (hx : IsSm G σ x)
    {ι : Type} [Fintype ι] {W : ι → List (Mat n)} (hW : ∀ i, LieW G (W i)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ y ∈ orbSpan G σ w, ∀ i, ‖dsW σ (W i) (x - y)‖ < δ := by
  let J : H → ι → H := fun v i => dsW σ (W i) v
  let S₀ : Submodule ℂ (ι → H) :=
    { carrier := J '' orbSpan G σ w
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, add_mem ha hb, funext fun i => dsW_add h (isSm_of_mem_orbSpan h hw ha)
          (isSm_of_mem_orbSpan h hw hb) (hW i)⟩
      zero_mem' := ⟨0, zero_mem _, funext fun i => by
        have := dsW_smul h (IsSm.zero (G := G) (σ := σ)) 0 (hW i)
        simpa using this⟩
      smul_mem' := by
        rintro c _ ⟨a, ha, rfl⟩
        exact ⟨c • a, Submodule.smul_mem _ c ha, funext fun i =>
          dsW_smul h (isSm_of_mem_orbSpan h hw ha) c (hW i)⟩ }
  let S := S₀.topologicalClosure
  have hS : IsClosed (S : Set (ι → H)) := S₀.isClosed_topologicalClosure
  have hJc : ∀ v, IsSm G σ v → Continuous fun g : MG G hG => J (σ g.mat v) := fun v hv =>
    continuous_pi fun i => continuous_orbit h hv (hW i)
  have key : ∀ φ : Mat n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ g : MG G hG, φ g.mat • J (σ g.mat x) ∂haar ∈ S := by
    intro φ hφ hc
    let C : ℝ := ∑ i, ∫ g : MG G hG, ‖LW (W i) φ g.mat‖ ∂haar
    have hC0 : ∀ i, 0 ≤ ∫ g : MG G hG, ‖LW (W i) φ g.mat‖ ∂haar := fun i =>
      integral_nonneg fun _ => norm_nonneg _
    have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => hC0 i
    rw [← SetLike.mem_coe, ← hS.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 (hd x) (ε / (C + 1)) (by positivity)
    have hys := isSm_of_mem_orbSpan h hw hy
    refine ⟨∫ g : MG G hG, φ g.mat • J (σ g.mat y) ∂haar,
      integral_mem_of_isClosed S hS fun g => ?_, ?_⟩
    · exact S.smul_of_tower_mem _ (S₀.le_topologicalClosure ⟨_, apply_mem_orbSpan h g.mem hy, rfl⟩)
    · rw [dist_eq_norm, ← integral_sub (integrable_smul hφ.continuous hc (hJc x hx))
        (integrable_smul hφ.continuous hc (hJc y hys))]
      have e : (fun g : MG G hG => φ g.mat • J (σ g.mat x) - φ g.mat • J (σ g.mat y)) =
          fun g => φ g.mat • J (σ g.mat (x - y)) := by
        ext g i
        simp only [J, Pi.sub_apply, Pi.smul_apply, map_sub]
        rw [dsW_sub h (hx.apply h g.mem) (hys.apply h g.mem) (hW i), smul_sub]
      rw [e]
      have hle : ‖∫ g : MG G hG, φ g.mat • J (σ g.mat (x - y)) ∂haar‖ ≤ C * ‖x - y‖ := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
        have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => H) i).integral_comp_comm
          (integrable_smul hφ.continuous hc (hJc _ (hx.sub hys)))
        simp only [ContinuousLinearMap.proj_apply, Pi.smul_apply] at this
        rw [← this]
        refine (norm_integral_dsW_le h hiso (hx.sub hys) hφ hc (hW i)).trans ?_
        exact mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i)) (norm_nonneg _)
      rw [dist_eq_norm, lt_div_iff₀ (by positivity)] at hxy
      nlinarith [norm_nonneg (x - y)]
  have hJx : J x ∈ S := by
    rw [← SetLike.mem_coe, ← hS.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    have hc1 : ContinuousAt (fun g : MG G hG => J (σ g.mat x)) 1 := (hJc x hx).continuousAt
    have h1 : J (σ (1 : MG G hG).mat x) = J x := by
      change J (σ 1 x) = J x
      rw [h.map_one]; rfl
    have hnb : {g : MG G hG | dist (J (σ g.mat x)) (J x) < ε / 2} ∈ 𝓝 (1 : MG G hG) := by
      rw [← h1]
      exact Metric.tendsto_nhds.1 hc1 _ (by positivity)
    rw [MG.isClosedEmbedding_mat.isInducing.nhds_eq_comap, mem_comap] at hnb
    obtain ⟨U, hU, hUs⟩ := hnb
    obtain ⟨φ, hφU, hc, hφ, hr, hφ1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hU
    have hφ0 : ∀ g, 0 ≤ φ g := fun g => (hr ⟨g, rfl⟩).1
    have hφ' : Continuous fun g : MG G hG => φ g.mat := hφ.continuous.comp MG.continuous_mat
    have hc' : HasCompactSupport fun g : MG G hG => φ g.mat :=
      HasCompactSupport.intro (isCompact_supp hc) fun g hg => image_eq_zero_of_notMem_tsupport hg
    set c : ℝ := ∫ g : MG G hG, φ g.mat ∂haar with hcdef
    have hcpos : 0 < c := hφ'.integral_pos_of_hasCompactSupport_nonneg_nonzero hc'
      (fun g => hφ0 _) (x := 1) (by rw [hφ1]; exact one_ne_zero)
    refine ⟨c⁻¹ • ∫ g : MG G hG, φ g.mat • J (σ g.mat x) ∂haar,
      S.smul_of_tower_mem _ (key φ hφ hc), ?_⟩
    have e : J x - c⁻¹ • ∫ g : MG G hG, φ g.mat • J (σ g.mat x) ∂haar =
        c⁻¹ • ∫ g : MG G hG, φ g.mat • (J x - J (σ g.mat x)) ∂haar := by
      simp_rw [smul_sub]
      rw [integral_sub (integrable_smul hφ.continuous hc continuous_const)
        (integrable_smul hφ.continuous hc (hJc x hx)), integral_smul_const, smul_sub, smul_smul,
        inv_mul_cancel₀ hcpos.ne', one_smul]
    have hle : ‖∫ g : MG G hG, φ g.mat • (J x - J (σ g.mat x)) ∂haar‖ ≤ c * (ε / 2) := by
      rw [hcdef, ← integral_mul_const]
      refine norm_integral_le_of_norm_le
        ((hφ'.integrable_of_hasCompactSupport hc').mul_const _) (Eventually.of_forall fun g => ?_)
      rw [norm_smul, Real.norm_of_nonneg (hφ0 _)]
      by_cases hg : g.mat ∈ tsupport φ
      · refine mul_le_mul_of_nonneg_left ?_ (hφ0 _)
        have : dist (J (σ g.mat x)) (J x) < ε / 2 := hUs (hφU hg)
        rw [dist_comm, dist_eq_norm] at this
        exact this.le
      · rw [image_eq_zero_of_notMem_tsupport hg, zero_mul, zero_mul]
    rw [dist_eq_norm, e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hcpos.le)]
    calc c⁻¹ * _ ≤ c⁻¹ * (c * (ε / 2)) := mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hcpos.le)
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := Metric.mem_closure_iff.1
    (show J x ∈ closure (S₀ : Set (ι → H)) from hJx) δ hδ
  refine ⟨y, hy, fun i => ?_⟩
  rw [dsW_sub h hx (isSm_of_mem_orbSpan h hw hy) (hW i)]
  rw [dist_eq_norm] at hxy
  exact (norm_le_pi_norm (J x - J y) i).trans_lt hxy

end CompanionTheory.D.Upq.Sm

end

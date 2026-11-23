import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.HaarBumpFunctions.ExistsOpOfForm
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Garding
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.IntegralMemOfIsClosed

open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.Poul

open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {G : Set (Mat n)} {hG : IsMatGroup G}

structure IsBump (G : Set (Mat n)) (φ : Mat n → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  nonneg : 0 ≤ φ
  one : φ 1 ≠ 0
  symm : ∀ x ∈ G, φ x⁻¹ = φ x
  supp : ∃ S : Set (Mat n), IsCompact S ∧ (∀ B ∈ S, B.det ≠ 0) ∧ ∀ y, φ y ≠ 0 → y ∈ S

theorem IsBump.cpt {φ : Mat n → ℝ} (h : IsBump G φ) : HasCompactSupport φ := by
  obtain ⟨S, hS, -, hφ⟩ := h.supp
  exact HasCompactSupport.intro hS fun y hy => by by_contra h0; exact hy (hφ y h0)

theorem exists_isBump (hG : IsMatGroup G) (θ : Mat n →L[ℝ] Mat n) (hθ : ∀ x ∈ G, θ x = x⁻¹) {V : Set (MG G hG)}
    (hV : V ∈ 𝓝 (1 : MG G hG)) : ∃ φ, IsBump G φ ∧ ∀ x : MG G hG, φ x.mat ≠ 0 → x ∈ V := by
  rw [MG.isClosedEmbedding_mat.isInducing.nhds_eq_comap, mem_comap] at hV
  obtain ⟨W, hW, hWV⟩ := hV
  have hD : {y : Mat n | y.det ≠ 0} ∈ 𝓝 (1 : Mat n) :=
    (isOpen_ne_fun continuous_id.matrix_det continuous_const).mem_nhds (by simp)
  obtain ⟨f, S, hf, hf0, hf1, hS, hSW, hfS, -⟩ := exists_bump (inter_mem hW hD)
  refine ⟨fun y => f y * f (θ y), ⟨hf.mul (hf.comp θ.contDiff), fun y => mul_nonneg (hf0 _) (hf0 _), ?_,
    fun x hx => ?_, S, hS, fun B hB => (hSW hB).2, fun y hy => hfS _ (left_ne_zero_of_mul hy)⟩,
    fun x hx => hWV (hSW (hfS _ (left_ne_zero_of_mul hx))).1⟩
  · show f 1 * f (θ 1) ≠ 0
    rw [hθ 1 hG.2.1, inv_one]
    exact mul_ne_zero hf1 hf1
  · show f x⁻¹ * f (θ x⁻¹) = f x * f (θ x)
    have hu : IsUnit x.det := Matrix.isUnit_det_of_right_inverse (hG.2.2.2 x hx).2
    rw [hθ _ (hG.2.2.2 x hx).1, hθ x hx, Matrix.nonsing_inv_nonsing_inv x hu, mul_comm]

section One

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat n → (H →L[ℂ] H)}

def avg (hG : IsMatGroup G) (φ : Mat n → ℝ) (σ : Mat n → (H →L[ℂ] H)) (v : H) : H :=
  ∫ g : MG G hG, φ g.mat • σ g.mat v ∂haar

theorem isSm_avg (h : RepOn G σ) (hc : ∀ v, ContinuousOn (fun g => σ g v) G) {φ : Mat n → ℝ} (hφ : IsBump G φ)
    (u : H) : IsSm G σ (avg hG φ σ u) := by
  obtain ⟨S, hS, hd, hfS⟩ := hφ.supp
  have hρ : ∀ u, Continuous fun x : MG G hG => σ x.mat u := fun u =>
    (hc u).comp_continuous MG.continuous_mat fun g => g.mem
  have hq : Continuous fun x : MG G hG => ((x⁻¹).mat, σ x.mat u) :=
    (MG.continuous_mat.comp continuous_inv).prodMk (hρ u)
  have key := contDiff_integral_comp (haar : Measure (MG G hG)) _ (contDiff_Phi (H := H) hφ.smooth) _ hq fun g₀ => by
    refine ⟨Metric.closedBall g₀ 1, Metric.closedBall_mem_nhds _ one_pos, _,
      MG.isClosedEmbedding_mat.isCompact_preimage (isCompact_mul_inv (isCompact_closedBall g₀ 1) hS hd),
      fun g hg x hx => ?_⟩
    have : φ ((x⁻¹).mat * g) = 0 := by
      by_contra h0
      have hB := hfS _ h0
      refine hx ⟨(g, (x⁻¹).mat * g), ⟨hg, hB⟩, ?_⟩
      have hu : IsUnit ((x⁻¹).mat * g).det := isUnit_iff_ne_zero.2 (hd _ hB)
      have e : g = x.mat * ((x⁻¹).mat * g) := by
        rw [← Matrix.mul_assoc, ← MG.mat_mul, mul_inv_cancel]
        exact (Matrix.one_mul g).symm
      show g * ((x⁻¹).mat * g)⁻¹ = x.mat
      calc g * ((x⁻¹).mat * g)⁻¹ = x.mat * ((x⁻¹).mat * g) * ((x⁻¹).mat * g)⁻¹ := by rw [← e]
        _ = x.mat := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    simp only [this, zero_smul]
  refine (SmOn.of_contDiff key).congr fun g hg => ?_
  have hw : Continuous fun x : MG G hG => φ x.mat := hφ.smooth.continuous.comp MG.continuous_mat
  have hcs : HasCompactSupport fun x : MG G hG => φ x.mat :=
    HasCompactSupport.intro (isCompact_supp hφ.cpt) fun x hx => image_eq_zero_of_notMem_tsupport hx
  have := apply_alt (haar : Measure (MG G hG)) (fun x : MG G hG => σ x.mat) hρ
    (fun x y u => h.apply_mul x.mem y.mem u) hw hcs (MG.mk hG g hg) u
  refine this.trans (integral_congr_ae (Eventually.of_forall fun x => ?_))
  show φ ((MG.mk hG g hg)⁻¹ * x).mat • _ = φ ((x⁻¹).mat * (MG.mk hG g hg).mat) • _
  rw [← hφ.symm _ (MG.mem _), ← MG.mat_inv, _root_.mul_inv_rev, inv_inv, MG.mat_mul]

theorem exists_avg_ne (hG : IsMatGroup G) (θ : Mat n →L[ℝ] Mat n) (hθ : ∀ x ∈ G, θ x = x⁻¹) (h : RepOn G σ)
    (hc : ∀ v, ContinuousOn (fun g => σ g v) G) {u : H} (hu : u ≠ 0) : ∃ φ, IsBump G φ ∧ avg hG φ σ u ≠ 0 := by
  have hρ : ∀ u, Continuous fun x : MG G hG => σ x.mat u := fun u =>
    (hc u).comp_continuous MG.continuous_mat fun g => g.mem
  obtain ⟨V, hV, hclose⟩ := exists_nhds_close (fun x : MG G hG => σ x.mat) hρ
    (fun u => by show σ 1 u = u; rw [h.map_one]; rfl) (Submodule.span ℂ {u})
  obtain ⟨φ, hφ, hφV⟩ := exists_isBump hG θ hθ hV
  refine ⟨φ, hφ, fun h0 => hu ?_⟩
  exact eq_zero_of_alt_alt (haar : Measure (MG G hG)) (fun x : MG G hG => σ x.mat) hρ
    (hφ.smooth.continuous.comp MG.continuous_mat)
    (HasCompactSupport.intro (isCompact_supp hφ.cpt) fun x hx => image_eq_zero_of_notMem_tsupport (f := φ) hx)
    (fun x => hφ.nonneg _) hφ.one u (fun x hx => hclose x (hφV x hx) u (Submodule.mem_span_singleton_self u)) h0

theorem dsW_avg (h : RepOn G σ) {v : H} (hv : IsSm G σ v) {φ : Mat n → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) {W : List (Mat n)} (hW : LieW G W) :
    dsW σ W (avg hG φ σ v) = ∫ g : MG G hG, φ g.mat • dsW σ W (σ g.mat v) ∂haar := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hW' : LieW G W := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    rw [dsW_cons, ih hW']
    exact (hasDerivAt_B h hv (hW X List.mem_cons_self) hW' hφ hc).deriv

structure IsSmForm (G : Set (Mat n)) (σ : Mat n → (H →L[ℂ] H)) {ι : Type} [Fintype ι] (W : ι → List (Mat n)) (C : ℝ)
    (l : H → ℂ) : Prop where
  add : ∀ x y, IsSm G σ x → IsSm G σ y → l (x + y) = l x + l y
  smul : ∀ (c : ℂ) x, IsSm G σ x → l (c • x) = c * l x
  bd : ∀ x, IsSm G σ x → ‖l x‖ ≤ C * ∑ i, ‖dsW σ (W i) x‖

variable {ι : Type} [Fintype ι] {W : ι → List (Mat n)} {C : ℝ} {l : H → ℂ}

omit [CompleteSpace H] in
theorem IsSmForm.sub (hl : IsSmForm G σ W C l) {x y : H} (hx : IsSm G σ x) (hy : IsSm G σ y) :
    l (x - y) = l x - l y := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ y, hl.add _ _ hx (hy.smul _), hl.smul _ _ hy]
  ring

omit [CompleteSpace H] in
theorem IsSmForm.continuous (hl : IsSmForm G σ W C l) (h : RepOn G σ) (hW : ∀ i, LieW G (W i)) {v : H}
    (hv : IsSm G σ v) : Continuous fun g : MG G hG => l (σ g.mat v) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous fun g : MG G hG => C * ∑ i, ‖dsW σ (W i) (σ g.mat v) - dsW σ (W i) (σ g₀.mat v)‖ :=
    continuous_const.mul (continuous_finsetSum _ fun i _ => ((continuous_orbit h hv (hW i)).sub continuous_const).norm)
  have ht := hc.tendsto g₀
  simp only [sub_self, norm_zero, Finset.sum_const_zero, mul_zero] at ht
  refine squeeze_zero (fun _ => norm_nonneg _) (fun g => ?_) ht
  rw [← hl.sub (hv.apply h g.mem) (hv.apply h g₀.mem)]
  refine (hl.bd _ ((hv.apply h g.mem).sub (hv.apply h g₀.mem))).trans (le_of_eq ?_)
  simp only [dsW_sub h (hv.apply h g.mem) (hv.apply h g₀.mem) (hW _)]

theorem IsSmForm.avg_bd (hl : IsSmForm G σ W C l) (h : RepOn G σ) (hW : ∀ i, LieW G (W i)) {v : H}
    (hv : IsSm G σ v) {φ : Mat n → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) {x : H} (hx : IsSm G σ x) :
    ‖(∫ g : MG G hG, φ g.mat • l (σ g.mat v) ∂haar) - l x‖ ≤
      C * ∑ i, ‖(∫ g : MG G hG, φ g.mat • dsW σ (W i) (σ g.mat v) ∂haar) - dsW σ (W i) x‖ := by
  let S₀ : Submodule ℂ ((ι → H) × ℂ) :=
    { carrier := {p | ∃ y, IsSm G σ y ∧ p = (fun i => dsW σ (W i) y, l y)}
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, ha.add hb, Prod.ext (funext fun i => (dsW_add h ha hb (hW i)).symm) (hl.add _ _ ha hb).symm⟩
      zero_mem' := ⟨0, IsSm.zero, Prod.ext (funext fun i => by
          simpa using (dsW_smul h (IsSm.zero (G := G) (σ := σ)) 0 (hW i)).symm)
        (by simpa using (hl.smul 0 0 IsSm.zero).symm)⟩
      smul_mem' := by
        rintro c _ ⟨a, ha, rfl⟩
        exact ⟨c • a, ha.smul c, Prod.ext (funext fun i => (dsW_smul h ha c (hW i)).symm) (hl.smul _ _ ha).symm⟩ }
  have hcl : IsClosed {p : (ι → H) × ℂ | ‖p.2‖ ≤ C * ∑ i, ‖p.1 i‖} :=
    isClosed_le continuous_snd.norm (continuous_const.mul (continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp continuous_fst).norm))
  have hsub : (S₀.topologicalClosure : Set ((ι → H) × ℂ)) ⊆ {p | ‖p.2‖ ≤ C * ∑ i, ‖p.1 i‖} :=
    closure_minimal (by rintro _ ⟨y, hy, rfl⟩; exact hl.bd y hy) hcl
  let F : MG G hG → (ι → H) × ℂ := fun g => (fun i => dsW σ (W i) (σ g.mat v), l (σ g.mat v))
  have hF : Continuous F := (continuous_pi fun i => continuous_orbit h hv (hW i)).prodMk (hl.continuous h hW hv)
  have hI := integrable_smul hφ hc hF
  have h1 : ∫ g : MG G hG, φ g.mat • F g ∂haar ∈ S₀.topologicalClosure :=
    integral_mem_of_isClosed _ S₀.isClosed_topologicalClosure fun g =>
      Submodule.smul_of_tower_mem _ _ (S₀.le_topologicalClosure ⟨_, hv.apply h g.mem, rfl⟩)
  have h2 := hsub (Submodule.sub_mem _ h1 (S₀.le_topologicalClosure ⟨x, hx, rfl⟩))
  have e2 := (ContinuousLinearMap.snd ℝ (ι → H) ℂ).integral_comp_comm hI
  have e1 := fun i => ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => H) i) ∘L
    ContinuousLinearMap.fst ℝ (ι → H) ℂ).integral_comp_comm hI
  refine le_of_eq_of_le (congrArg (fun t => ‖t - l x‖) e2) (h2.trans (le_of_eq ?_))
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (congrArg (fun t => ‖t - dsW σ (W i) x‖) (e1 i)).symm

theorem IsSmForm.map_avg (hl : IsSmForm G σ W C l) (h : RepOn G σ) (hW : ∀ i, LieW G (W i)) {v : H}
    (hv : IsSm G σ v) {φ : Mat n → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hs : IsSm G σ (avg hG φ σ v)) : l (avg hG φ σ v) = ∫ g : MG G hG, φ g.mat • l (σ g.mat v) ∂haar := by
  have := hl.avg_bd (hG := hG) h hW hv hφ hc hs
  simp only [dsW_avg h hv hφ hc (hW _), sub_self, norm_zero, Finset.sum_const_zero, mul_zero, norm_le_zero_iff,
    sub_eq_zero] at this
  exact this.symm

theorem IsSmForm.exists_bd (hl : IsSmForm G σ W C l) (h : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖)
    (hW : ∀ i, LieW G (W i)) {φ : Mat n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∃ D : ℝ, ∀ v, IsSm G σ v → ‖∫ g : MG G hG, φ g.mat • l (σ g.mat v) ∂haar‖ ≤ D * ‖v‖ := by
  refine ⟨|C| * ∑ i, ∫ g : MG G hG, ‖LW (W i) φ g.mat‖ ∂haar, fun v hv => ?_⟩
  have h1 := hl.avg_bd (hG := hG) h hW hv hφ.continuous hc IsSm.zero
  have h0 : l 0 = 0 := by simpa using hl.smul 0 0 IsSm.zero
  have h0' : ∀ i, dsW σ (W i) 0 = 0 := fun i => by
    simpa using dsW_smul h (IsSm.zero (G := G) (σ := σ)) 0 (hW i)
  simp only [h0, h0', sub_zero] at h1
  refine h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).trans ?_)
  rw [mul_assoc, Finset.sum_mul]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => norm_integral_dsW_le h hiso hv hφ hc (hW i))
    (abs_nonneg _)

theorem exists_riesz (ha : ∀ x y, IsSm G σ x → IsSm G σ y → l (x + y) = l x + l y)
    (hs : ∀ (c : ℂ) x, IsSm G σ x → l (c • x) = c * l x) {D : ℝ} (hD : ∀ x, IsSm G σ x → ‖l x‖ ≤ D * ‖x‖) :
    ∃ z : H, ∀ x, IsSm G σ x → l x = ⟪z, x⟫_ℂ := by
  let S : Submodule ℂ H :=
    { carrier := {x | IsSm G σ x}
      add_mem' := fun ha hb => ha.add hb
      zero_mem' := IsSm.zero
      smul_mem' := fun c _ hx => hx.smul c }
  let L : S →ₗ[ℂ] ℂ :=
    { toFun := fun x => l x
      map_add' := fun x y => ha _ _ x.2 y.2
      map_smul' := fun c x => hs c _ x.2 }
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq S (L.mkContinuous D fun x => hD _ x.2)
  refine ⟨(InnerProductSpace.toDual ℂ H).symm g, fun x hx => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  exact (hg ⟨x, hx⟩).symm

end One

section Two

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {σ : Mat n → (H →L[ℂ] H)} {σ' : Mat n → (H' →L[ℂ] H')}

structure IsInv (G : Set (Mat n)) (σ : Mat n → (H →L[ℂ] H)) (σ' : Mat n → (H' →L[ℂ] H')) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (W : ι → List (Mat n)) (W' : ι' → List (Mat n)) (C : ℝ) (B : H → H' → ℂ) : Prop where
  add_left : ∀ x x' y, IsSm G σ x → IsSm G σ x' → IsSm G σ' y → B (x + x') y = B x y + B x' y
  smul_left : ∀ (a : ℂ) x y, IsSm G σ x → IsSm G σ' y → B (a • x) y = a * B x y
  add_right : ∀ x y y', IsSm G σ x → IsSm G σ' y → IsSm G σ' y' → B x (y + y') = B x y + B x y'
  smul_right : ∀ (a : ℂ) x y, IsSm G σ x → IsSm G σ' y → B x (a • y) = star a * B x y
  inv : ∀ g ∈ G, ∀ x y, IsSm G σ x → IsSm G σ' y → B (σ g x) (σ' g y) = B x y
  bd : ∀ x y, IsSm G σ x → IsSm G σ' y → ‖B x y‖ ≤ C * (∑ i, ‖dsW σ (W i) x‖) * ∑ j, ‖dsW σ' (W' j) y‖

variable {ι ι' : Type} [Fintype ι] [Fintype ι'] {W : ι → List (Mat n)} {W' : ι' → List (Mat n)} {C : ℝ}
  {B : H → H' → ℂ}

omit [CompleteSpace H] [CompleteSpace H'] in
theorem IsInv.swap (hB : IsInv G σ σ' W W' C B) : IsInv G σ' σ W' W C fun y x => star (B x y) where
  add_left y y' x hy hy' hx := by rw [hB.add_right x y y' hx hy hy', star_add]
  smul_left a y x hy hx := by rw [hB.smul_right a x y hx hy, star_mul', star_star]
  add_right y x x' hy hx hx' := by rw [hB.add_left x x' y hx hx' hy, star_add]
  smul_right a y x hy hx := by rw [hB.smul_left a x y hx hy, star_mul']
  inv g hg y x hy hx := by rw [hB.inv g hg x y hx hy]
  bd y x hy hx := by rw [norm_star, mul_right_comm]; exact hB.bd x y hx hy

omit [CompleteSpace H] [CompleteSpace H'] in
theorem IsInv.left (hB : IsInv G σ σ' W W' C B) {y : H'} (hy : IsSm G σ' y) :
    IsSmForm G σ W (C * ∑ j, ‖dsW σ' (W' j) y‖) fun x => B x y where
  add x x' hx hx' := hB.add_left x x' y hx hx' hy
  smul a x hx := hB.smul_left a x y hx hy
  bd x hx := by rw [mul_right_comm]; exact hB.bd x y hx hy

theorem IsInv.exists_rep [(haar : Measure (MG G hG)).IsInvInvariant] (θ : Mat n →L[ℝ] Mat n)
    (hθ : ∀ x ∈ G, θ x = x⁻¹) (hB : IsInv G σ σ' W W' C B) (h : RepOn G σ) (h' : RepOn G σ')
    (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (hc' : ∀ v, ContinuousOn (fun g => σ' g v) G)
    (hW : ∀ i, LieW G (W i)) (hW' : ∀ j, LieW G (W' j)) [Nontrivial H'] :
    ∃ y₀ z₀, IsSm G σ' y₀ ∧ y₀ ≠ 0 ∧ ∀ x, IsSm G σ x → B x y₀ = ⟪z₀, x⟫_ℂ := by
  obtain ⟨u, hu⟩ := exists_ne (0 : H')
  obtain ⟨φ₁, hφ₁, hy₁⟩ := exists_avg_ne hG θ hθ h' hc' hu
  have hs₁ := isSm_avg (hG := hG) h' hc' hφ₁ u
  set y₁ := avg hG φ₁ σ' u
  obtain ⟨φ, hφ, hy₀⟩ := exists_avg_ne hG θ hθ h' hc' hy₁
  have hs₀ := isSm_avg (hG := hG) h' hc' hφ y₁
  obtain ⟨D, hD⟩ := (hB.left hs₁).exists_bd (hG := hG) h hiso hW hφ.smooth hφ.cpt
  have key : ∀ x, IsSm G σ x → B x (avg hG φ σ' y₁) = ∫ g : MG G hG, φ g.mat • B (σ g.mat x) y₁ ∂haar := by
    intro x hx
    have h1 := (hB.swap.left hx).map_avg h' hW' hs₁ hφ.smooth.continuous hφ.cpt hs₀
    have h2 := congrArg star h1
    rw [star_star] at h2
    rw [h2, ← integral_inv_eq_self (fun g : MG G hG => φ g.mat • B (σ g.mat x) y₁), Complex.star_def,
      ← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    have e : B x (σ' g.mat y₁) = B (σ (g⁻¹).mat x) y₁ := by
      rw [← hB.inv _ g.mem _ _ (hx.apply h (g⁻¹).mem) hs₁, ← h.apply_mul g.mem (g⁻¹).mem, ← MG.mat_mul,
        mul_inv_cancel]
      show _ = B (σ 1 x) _
      rw [h.map_one]; rfl
    simp only [e, MG.mat_inv, hφ.symm _ g.mem, Complex.real_smul, map_mul, Complex.conj_ofReal,
      Complex.conj_conj]
  obtain ⟨z₀, hz₀⟩ := exists_riesz (G := G) (σ := σ) (l := fun x => B x (avg hG φ σ' y₁)) (hB.left hs₀).add
    (hB.left hs₀).smul (D := D) fun x hx => by rw [key x hx]; exact hD x hx
  exact ⟨_, z₀, hs₀, hy₀, hz₀⟩

def homMG (hG : IsMatGroup G) (h : RepOn G σ) : MG G hG →* (H →L[ℂ] H) where
  toFun g := σ g.mat
  map_one' := h.map_one
  map_mul' a b := h.map_mul _ a.mem _ b.mem

theorem IsInv.exists_op [(haar : Measure (MG G hG)).IsInvInvariant] (θ : Mat n →L[ℝ] Mat n)
    (hθ : ∀ x ∈ G, θ x = x⁻¹) (hB : IsInv G σ σ' W W' C B) (h : RepOn G σ) (h' : RepOn G σ')
    (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (hiso' : ∀ g ∈ G, ∀ v, ‖σ' g v‖ = ‖v‖)
    (hc : ∀ v, ContinuousOn (fun g => σ g v) G) (hc' : ∀ v, ContinuousOn (fun g => σ' g v) G)
    (hirr : PI.UpqRep.IsIrredOn G σ) (hirr' : PI.UpqRep.IsIrredOn G σ')
    (hW : ∀ i, LieW G (W i)) (hW' : ∀ j, LieW G (W' j)) [Nontrivial H] [Nontrivial H'] :
    ∃ T : H' →L[ℂ] H, (∀ g ∈ G, ∀ y, T (σ' g y) = σ g (T y)) ∧
      ∀ x y, IsSm G σ x → IsSm G σ' y → B x y = ⟪T y, x⟫_ℂ := by
  obtain ⟨y₀, z₀, hy₀s, hy₀, hz₀⟩ := hB.exists_rep (hG := hG) θ hθ h h' hiso hc' hW hW'
  obtain ⟨x₀, w₀, hx₀s, hx₀, hw₀⟩ := hB.swap.exists_rep (hG := hG) θ hθ h' h hiso' hc hW' hW
  obtain ⟨T, hT, hTB⟩ := exists_op_of_form (σ := homMG hG h) (σ' := homMG hG h') (fun g => hiso _ g.mem)
    (fun g => hiso' _ g.mem)
    (FinOfPIAux.schur (homMG hG h') (fun g => hiso' _ g.mem) fun S hS hinv =>
      hirr' S hS fun g hg => hinv (MG.mk hG g hg))
    {x | IsSm G σ x} {y | IsSm G σ' y} (fun g x hx => IsSm.apply h hx g.mem) (fun g y hy => IsSm.apply h' hy g.mem) B
    (fun g x hx y hy => hB.inv _ g.mem x y hx hy) hy₀s hy₀ hz₀
  have hT' : ∀ g ∈ G, ∀ y, T (σ' g y) = σ g (T y) := fun g hg y => hT (MG.mk hG g hg) y
  refine ⟨T, hT', fun x y hx hy => ?_⟩
  have h0 : ∀ y, IsSm G σ' y → B x₀ y = ⟪T y, x₀⟫_ℂ := hTB x₀ hx₀s w₀ fun y hy => by
    have := congrArg star (hw₀ y hy)
    rw [star_star] at this
    rw [this, Complex.star_def, inner_conj_symm]
  have horb : ∀ a ∈ orbSpan G σ x₀, B a y = ⟪T y, a⟫_ℂ := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨g, hg, rfl⟩ := ha
      have hg' := (hG.2.2.2 g hg).1
      have e : σ' g (σ' g⁻¹ y) = y := by
        rw [← h'.apply_mul hg hg', (hG.2.2.2 g hg).2, h'.map_one]; rfl
      have hy' := hy.apply h' hg'
      calc B (σ g x₀) y = B (σ g x₀) (σ' g (σ' g⁻¹ y)) := by rw [e]
        _ = ⟪T (σ' g⁻¹ y), x₀⟫_ℂ := by rw [hB.inv g hg _ _ hx₀s hy', h0 _ hy']
        _ = ⟪σ g (T (σ' g⁻¹ y)), σ g x₀⟫_ℂ :=
          ((⟨(σ g : H →ₗ[ℂ] H), hiso g hg⟩ : H →ₗᵢ[ℂ] H).inner_map_map _ _).symm
        _ = _ := by rw [← hT' g hg, e]
    | zero => simpa using hB.smul_left 0 0 y IsSm.zero hy
    | add a b ha hb iha ihb =>
      rw [hB.add_left a b y (isSm_of_mem_orbSpan h hx₀s ha) (isSm_of_mem_orbSpan h hx₀s hb) hy, iha, ihb,
        inner_add_right]
    | smul c a ha iha => rw [hB.smul_left c a y (isSm_of_mem_orbSpan h hx₀s ha) hy, iha, inner_smul_right]
  have hd : Dense (orbSpan G σ x₀ : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    refine (hirr _ (Submodule.isClosed_topologicalClosure _) fun g hg v hv => ?_).resolve_left fun h0 => hx₀ ?_
    · exact map_mem_closure (σ g).continuous hv fun y hy => apply_mem_orbSpan h hg hy
    · have hm : x₀ ∈ orbSpan G σ x₀ := Submodule.subset_span ⟨1, h.one_mem, by simp [h.map_one]⟩
      have := Submodule.le_topologicalClosure _ hm
      rwa [h0, Submodule.mem_bot] at this
  set C' := |C * ∑ j, ‖dsW σ' (W' j) y‖| * Fintype.card ι + ‖T y‖ with hC'
  have hC0 : 0 ≤ C' := by positivity
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨a, ha, hxa⟩ := exists_approx hG h hiso hx₀s hd hx (ι := Option ι) (W := fun o => o.elim [] W)
    (fun o => by
      cases o with
      | none => exact fun X hX => absurd hX List.not_mem_nil
      | some i => exact hW i) (δ := δ / (C' + 1)) (by positivity)
  have has := isSm_of_mem_orbSpan h hx₀s ha
  have e : B x y - ⟪T y, x⟫_ℂ = B (x - a) y - ⟪T y, x - a⟫_ℂ := by
    rw [(hB.left hy).sub hx has, inner_sub_right, horb a ha]; ring
  have h1 : ‖B (x - a) y‖ ≤ |C * ∑ j, ‖dsW σ' (W' j) y‖| * (Fintype.card ι * (δ / (C' + 1))) := by
    refine ((hB.left hy).bd _ (hx.sub has)).trans (mul_le_mul (le_abs_self _) ?_
      (Finset.sum_nonneg fun _ _ => norm_nonneg _) (abs_nonneg _))
    refine (Finset.sum_le_sum fun i _ => (hxa (some i)).le).trans (le_of_eq ?_)
    simp
  have h2 : ‖⟪T y, x - a⟫_ℂ‖ ≤ ‖T y‖ * (δ / (C' + 1)) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hxa none).le (norm_nonneg _))
  rw [e, zero_add]
  refine (norm_sub_le _ _).trans ((add_le_add h1 h2).trans ?_)
  rw [← mul_assoc, ← add_mul, ← hC', ← mul_div_assoc, div_le_iff₀ (by positivity)]
  nlinarith

end Two

end CompanionTheory.D.gk.Poul

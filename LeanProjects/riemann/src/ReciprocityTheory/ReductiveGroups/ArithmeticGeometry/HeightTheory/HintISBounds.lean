import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HintLogFinprod

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def hintSm (c : ι) (sg : K →+* ℂ) (φ : (Ω c →+* ℂ) → ℝ)
    (z : BlockSphere d.D (d.N + 1)) : ℝ :=
  ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), φ P

def HintIS (c : ι) (sg : K →+* ℂ) (φ : (Ω c →+* ℂ) → ℝ) : Prop :=
  Integrable (d.hintSm c sg φ) (blockSphereProb d.D (d.N + 1))

theorem hint_fs (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) :
    ∀ᵐ z ∂(blockSphereProb d.D (d.N + 1)), ∃ s : Finset (Ω c →+* ℂ), s.card = d.delc c ∧
      (∀ P ∈ s, P ∈ PT (Ω := Ω c) sg) ∧ ∀ φ, d.hintSm c sg φ z = ∑ P ∈ s, φ P := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  filter_upwards [d.norm_at_sg hd h c sg] with z hz
  obtain ⟨hfin, hcard, -, -⟩ := hz
  refine ⟨hfin.toFinset, ?_, fun P hP => (hfin.mem_toFinset.1 hP).1, fun φ => ?_⟩
  · rw [← hcard, Set.ncard_eq_toFinset_card _ hfin]
  · exact finsum_mem_eq_finite_toFinset_sum _ hfin

theorem hintIS_lin (hd : d.AxH 𝒜) (h : d.S1) {c : ι} {sg : K →+* ℂ}
    {φ₁ φ₂ : (Ω c →+* ℂ) → ℝ} (h₁ : d.HintIS c sg φ₁) (h₂ : d.HintIS c sg φ₂) (a₁ a₂ b : ℝ) :
    d.HintIS c sg (fun P => a₁ * φ₁ P + a₂ * φ₂ P + b) := by
  have hfs := d.hint_fs hd h c sg
  haveI : IsFiniteMeasure (blockSphereProb d.D (d.N + 1)) := by
    unfold blockSphereProb; infer_instance
  unfold HintIS at *
  refine (((h₁.const_mul a₁).add (h₂.const_mul a₂)).add
    (integrable_const (b * (d.delc c : ℝ)))).congr ?_
  filter_upwards [hfs] with z hz
  obtain ⟨s, hs, -, hφ⟩ := hz
  simp only [Pi.add_apply, hφ, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, hs,
    nsmul_eq_mul]
  ring

theorem hintIS_congr (hd : d.AxH 𝒜) (h : d.S1) {c : ι} {sg : K →+* ℂ}
    {φ ψ : (Ω c →+* ℂ) → ℝ} (hφ : d.HintIS c sg φ) (heq : ∀ P ∈ PT (Ω := Ω c) sg, φ P = ψ P) :
    d.HintIS c sg ψ := by
  unfold HintIS at *
  refine hφ.congr (Filter.Eventually.of_forall fun z => ?_)
  exact finsum_mem_congr rfl fun P hP => heq P hP.1

theorem hintIS_bounds (hd : d.AxH 𝒜) (h : d.S1) {c : ι} {sg : K →+* ℂ}
    {φ ψ : (Ω c →+* ℂ) → ℝ}
    (hm : AEStronglyMeasurable (d.hintSm c sg φ) (blockSphereProb d.D (d.N + 1)))
    (hψ : d.HintIS c sg ψ) (hle : ∀ P ∈ PT (Ω := Ω c) sg, ψ P ≤ φ P) (B : ℝ)
    (hB : ∀ P ∈ PT (Ω := Ω c) sg, φ P ≤ B) : d.HintIS c sg φ := by
  have hfs := d.hint_fs hd h c sg
  haveI : IsFiniteMeasure (blockSphereProb d.D (d.N + 1)) := by
    unfold blockSphereProb; infer_instance
  unfold HintIS at *
  refine Integrable.mono' (hψ.abs.add (integrable_const |(d.delc c : ℝ) * B|)) hm ?_
  filter_upwards [hfs] with z hz
  obtain ⟨s, hs, hsP, hφ⟩ := hz
  have h1 : d.hintSm c sg ψ z ≤ d.hintSm c sg φ z := by
    rw [hφ, hφ]
    exact Finset.sum_le_sum fun P hP => hle P (hsP P hP)
  have h2 : d.hintSm c sg φ z ≤ (d.delc c : ℝ) * B := by
    rw [hφ, ← hs, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun P hP => hB P (hsP P hP)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith [neg_abs_le (d.hintSm c sg ψ z), abs_nonneg ((d.delc c : ℝ) * B)]
  · linarith [le_abs_self ((d.delc c : ℝ) * B), abs_nonneg (d.hintSm c sg ψ z)]

theorem hint_bsp_smul : blockSphereProb d.D (d.N + 1) =
    (((volume : Measure (EuclideanSpace ℂ (Fin (d.N + 1)))).toSphere Set.univ)⁻¹ ^ d.D) •
      d.sphMeasure := by
  unfold blockSphereProb
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, smul_eq_mul, sphMeasure, Measure.pi_pi]
  simp only [sphereProb, ProbabilityTheory.cond_apply MeasurableSet.univ, Set.univ_inter,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem eq_ratio_smul_of_mem_graded {d' : Data K ι Ω WT A} (hd : d'.AxH 𝒜) {c : ι} {G : WT} {f e : A c}
    (he : e ∈ 𝒜 c G) (he0 : e ≠ 0) (hf : f ∈ 𝒜 c G) : f = ratio (Ω := Ω c) f e • e := by
  have hnz : (⟨e, he⟩ : 𝒜 c G) ≠ 0 := fun h0 => he0 (by simpa using congrArg Subtype.val h0)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨e, he⟩ : 𝒜 c G) hnz).mp (hd.finrank_one c G) ⟨f, hf⟩
  have hex : ∃ a : Ω c, f = a • e := ⟨a, by simpa using (congrArg Subtype.val ha).symm⟩
  rw [ratio, dif_pos hex]
  exact hex.choose_spec

theorem hint_meas (hd : d.AxH 𝒜) (c : ι) (sg : K →+* ℂ) {G : WT} {f : A c} (hf : f ∈ 𝒜 c G)
    (hf0 : f ≠ 0) :
    AEStronglyMeasurable (d.hintSm c sg fun P => Real.log (d.nrm c G f P))
      (blockSphereProb d.D (d.N + 1)) := by
  rw [d.hint_bsp_smul]
  exact ((hd.a13 c sg hf hf0).smul_measure _).aestronglyMeasurable

variable {d} in
theorem hint_ratio_ne (hd : d.AxH 𝒜) {c : ι} {G : WT} {f e : A c} (he : e ∈ 𝒜 c G) (he0 : e ≠ 0)
    (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0) : ratio (Ω := Ω c) f e ≠ 0 := by
  intro h0
  have h1 := eq_ratio_smul_of_mem_graded hd he he0 hf
  rw [h0, zero_smul] at h1
  exact hf0 h1

theorem hint_log_line (hd : d.AxH 𝒜) {c : ι} {G : WT} {f e : A c} (he : e ∈ 𝒜 c G) (he0 : e ≠ 0)
    (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0) (P : Ω c →+* ℂ) :
    Real.log (d.nrm c G f P) = Real.log ‖P (ratio (Ω := Ω c) f e)‖ + Real.log (d.nrm c G e P) := by
  have hfe := eq_ratio_smul_of_mem_graded hd he he0 hf
  have hr := hint_ratio_ne hd he he0 hf hf0
  calc Real.log (d.nrm c G f P)
      = Real.log (d.nrm c G (ratio (Ω := Ω c) f e • e) P) := by rw [← hfe]
    _ = _ := by
      rw [hd.nrm_smul c P _ he he0 hr,
        Real.log_mul (norm_ne_zero_iff.mpr ((map_ne_zero P).mpr hr)) (hd.nrm_pos c P he he0).ne']

theorem hint_log_mul (hd : d.AxH 𝒜) {c : ι} {G G' : WT} {f g : A c} (hf : f ∈ 𝒜 c G)
    (hg : g ∈ 𝒜 c G') (hf0 : f ≠ 0) (hg0 : g ≠ 0) (P : Ω c →+* ℂ) :
    Real.log (d.nrm c (G + G') (f * g) P) =
      Real.log (d.nrm c G f P) + Real.log (d.nrm c G' g P) := by
  rw [hd.nrm_mul c P hf hg hf0 hg0,
    Real.log_mul (hd.nrm_pos c P hf hf0).ne' (hd.nrm_pos c P hg hg0).ne']

theorem hint_pow (hd : d.AxH 𝒜) {c : ι} {G : WT} {f : A c} (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0) :
    ∀ k : ℕ, 0 < k → f ^ k ∈ 𝒜 c (k • G) ∧ f ^ k ≠ 0 ∧
      ∀ P, Real.log (d.nrm c (k • G) (f ^ k) P) = k * Real.log (d.nrm c G f P) := by
  intro k hk
  haveI := hd.graded c
  induction k with
  | zero => exact absurd hk (lt_irrefl 0)
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨by simpa using hf, by simpa using hf0, fun P => by simp⟩
    · obtain ⟨h1, h2, h3⟩ := ih hn
      have hmem : f ^ (n + 1) ∈ 𝒜 c ((n + 1) • G) := by
        rw [pow_succ, succ_nsmul]; exact SetLike.mul_mem_graded h1 hf
      have hne : f ^ (n + 1) ≠ 0 := by
        rw [pow_succ]; exact hd.mul_ne_zero c h1 hf h2 hf0
      refine ⟨hmem, hne, fun P => ?_⟩
      rw [pow_succ, succ_nsmul, hd.nrm_mul c P h1 hf h2 hf0,
        Real.log_mul (hd.nrm_pos c P h1 h2).ne' (hd.nrm_pos c P hf hf0).ne', h3 P]
      push_cast
      ring

theorem hint_log_be (hd : d.AxH 𝒜) (c : ι) (P : Ω c →+* ℂ) :
    Real.log (d.be c P) =
      Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) + Real.log ‖d.hintU c P‖ := by
  have he := hd.w_mem (d.jc c) c
  have he0 := hd.w_base c
  have key : ∀ j, d.nrm c d.wL (d.w j c) P =
      ‖P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ * d.nrm c d.wL (d.w (d.jc c) c) P := by
    intro j
    by_cases hj : d.w j c = 0
    · have hr : ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = 0 := by
        have h1 := eq_ratio_smul_of_mem_graded hd he he0 (hd.w_mem j c)
        have h2 : ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c = 0 := by
          rw [← h1]; exact hj
        exact (smul_eq_zero.mp h2).resolve_right he0
      rw [hr, hj, hd.nrm_zero, map_zero, norm_zero, zero_mul]
    · rw [← hd.nrm_smul c P _ he he0 (hint_ratio_ne hd he he0 (hd.w_mem j c) hj),
        ← eq_ratio_smul_of_mem_graded hd he he0 (hd.w_mem j c)]
  have hsum : ∑ j, d.nrm c d.wL (d.w j c) P ^ 2 = d.nrm c d.wL (d.w (d.jc c) c) P ^ 2 *
      ∑ j, ‖P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [key j]; ring
  have hU : ‖d.hintU c P‖ = Real.sqrt (∑ j, ‖P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ ^ 2) := by
    simp [hintU, EuclideanSpace.norm_eq]
  have hUne : ‖d.hintU c P‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h0
    have h1 := congrArg (fun x => x (d.jc c)) h0
    exact hint_ratio_ne hd he he0 he he0 (by simpa [hintU] using h1)
  have hpos := hd.nrm_pos c P he he0
  rw [be, hsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpos.le, ← hU, Real.log_mul hpos.ne' hUne]

theorem hint_bdd (sg : K →+* ℂ) (c : ι) {G : WT} {f : ∀ c, A c}
    (hb : BddAbove (Set.range fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 G (f p.1) p.2)) :
    ∃ B, ∀ P ∈ PT (Ω := Ω c) sg, d.nrm c G (f c) P ≤ B := by
  obtain ⟨B, hB⟩ := hb
  exact ⟨B, fun P hP => hB ⟨⟨c, ⟨P, hP⟩⟩, rfl⟩⟩

theorem hint_log_le (hd : d.AxH 𝒜) {c : ι} {G : WT} {f : A c} (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0)
    {sg : K →+* ℂ} {B : ℝ} (hB : ∀ P ∈ PT (Ω := Ω c) sg, d.nrm c G f P ≤ B) :
    ∀ P ∈ PT (Ω := Ω c) sg, Real.log (d.nrm c G f P) ≤ Real.log B := fun P hP => Real.log_le_log (hd.nrm_pos c P hf hf0) (hB P hP)

theorem hint_thp_ne (hd : d.AxH 𝒜) (c : ι) : ∃ k, d.thp k c ≠ 0 := by
  by_contra hall
  push_neg at hall
  obtain ⟨e, he, -, h3⟩ := hd.a4
  obtain ⟨q, hq, p, hp⟩ := h3 1
  apply hq c
  have h4 := hp c
  rw [Pi.one_apply, mul_one] at h4
  rw [h4]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hr : ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c) = 0 := by
    rw [hall]
    have h1 := eq_ratio_smul_of_mem_graded hd (he c).1 (he c).2 (Submodule.zero_mem _)
    exact (smul_eq_zero.mp h1.symm).resolve_right (he c).2
  rw [hr, map_zero, mul_zero]

end Data

end ReciprocityTheory.ChartRestriction.G.T0

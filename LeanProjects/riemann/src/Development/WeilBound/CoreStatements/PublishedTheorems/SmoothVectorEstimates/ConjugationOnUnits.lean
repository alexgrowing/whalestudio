import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows.ConjugationOnUnits

section Mat

variable {ι : Type} [Fintype ι] {a : ℕ}

def mulI (M N : LieI ι a) : LieI ι a := Matrix.of.symm (Matrix.of M * Matrix.of N)

theorem of_mulI (M N : LieI ι a) : Matrix.of (mulI M N) = Matrix.of M * Matrix.of N := rfl

theorem mulI_apply (M N : LieI ι a) (i k : Fin a) (l : ι) :
    mulI M N i k l = ∑ j, M i j l * N j k l := by
  simp [mulI, Matrix.mul_apply, Finset.sum_apply]

theorem contDiff_mulI : ContDiff ℝ ∞ (fun p : LieI ι a × LieI ι a => mulI p.1 p.2) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun k => contDiff_pi.2 fun l => ?_
  simp only [mulI_apply]
  refine ContDiff.sum fun j _ => ?_
  fun_prop

theorem isUnit_mul_iff' {A B : Matrix (Fin a) (Fin a) (ι → ℂ)} :
    IsUnit (A * B) ↔ IsUnit A ∧ IsUnit B := by
  simp only [Matrix.isUnit_iff_isUnit_det, IsUnit.mul_iff]

theorem isOpen_units : IsOpen {M : LieI ι a | IsUnit (Matrix.of M)} := by
  have hc : Continuous fun M : LieI ι a => (Matrix.of M).det := Continuous.matrix_det continuous_id
  have : {M : LieI ι a | IsUnit (Matrix.of M)} =
      (fun M : LieI ι a => (Matrix.of M).det) ⁻¹' {x | IsUnit x} := by
    ext M; simp [Matrix.isUnit_iff_isUnit_det]
  rw [this]; exact Units.isOpen.preimage hc

theorem isUnit_oneI : IsUnit (Matrix.of (oneI ι a)) := by
  simp [oneI]

def conjL (A B : LieI ι a) : LieI ι a →L[ℝ] LieI ι a :=
  LinearMap.toContinuousLinearMap
    ((Matrix.ofLinearEquiv ℝ).symm.toLinearMap ∘ₗ LinearMap.mulLeft ℝ (Matrix.of A) ∘ₗ
      LinearMap.mulRight ℝ (Matrix.of B) ∘ₗ (Matrix.ofLinearEquiv ℝ).toLinearMap)

theorem conjL_apply (A B Z : LieI ι a) : conjL A B Z = mulI A (mulI Z B) := rfl

end Mat

section Orb

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
  (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X))

open Classical in

def opI (M : LieI ι a) : X →L[ℂ] X := if h : IsUnit (Matrix.of M) then ρ h.unit else 0

theorem orb_eq (v : X) (M : LieI ι a) : orb ρ v M = opI ρ M v := by
  unfold orb opI; split_ifs <;> simp

theorem orb_add (v w : X) : orb ρ (v + w) = orb ρ v + orb ρ w := by
  funext M; simp [orb_eq]

theorem orb_smul (c : ℂ) (v : X) : orb ρ (c • v) = c • orb ρ v := by
  funext M; simp [orb_eq]

theorem orb_zero : orb ρ (0 : X) = 0 := by
  funext M; simp [orb_eq]

theorem opI_mul (M N : LieI ι a) (v : X) : opI ρ M (opI ρ N v) = opI ρ (mulI M N) v := by
  unfold opI
  by_cases hM : IsUnit (Matrix.of M)
  · by_cases hN : IsUnit (Matrix.of N)
    · have hMN : IsUnit (Matrix.of (mulI M N)) := by rw [of_mulI]; exact hM.mul hN
      rw [dif_pos hM, dif_pos hN, dif_pos hMN, ← ContinuousLinearMap.mul_apply, ← map_mul]
      congr 2
      ext : 1
      simp [of_mulI]
    · have hMN : ¬ IsUnit (Matrix.of (mulI M N)) := by rw [of_mulI, isUnit_mul_iff']; tauto
      rw [dif_neg hN, dif_neg hMN]; simp
  · have hMN : ¬ IsUnit (Matrix.of (mulI M N)) := by rw [of_mulI, isUnit_mul_iff']; tauto
    rw [dif_neg hM, dif_neg hMN]; simp

end Orb

section Rapid

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
  (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) {V : Type} [NormedAddCommGroup V]

def Good (𝒢 : Submodule ℂ (V → X)) (G : V → X) : Prop :=
  Continuous G ∧ (∀ N : ℕ, ∃ C : ℝ, ∀ y, (1 + ‖y‖) ^ N * ‖G y‖ ≤ C) ∧
    ∃ D : LieI ι a → V → X, (∀ Z, D Z ∈ 𝒢) ∧
      ∀ y, ∃ D' : LieI ι a →L[ℝ] X, (∀ Z, D' Z = D Z y) ∧ HasFDerivAt (orb ρ (G y)) D' (oneI ι a)

variable {ρ} {𝒢 : Submodule ℂ (V → X)}

theorem good_zero : Good ρ 𝒢 0 := by
  refine ⟨continuous_const, fun N => ⟨0, fun y => by simp⟩, fun _ => 0, fun _ => zero_mem _,
    fun y => ⟨0, fun Z => by simp, ?_⟩⟩
  simp only [Pi.zero_apply, orb_zero]
  exact hasFDerivAt_const _ _

theorem good_add {G1 G2 : V → X} (h1 : Good ρ 𝒢 G1) (h2 : Good ρ 𝒢 G2) : Good ρ 𝒢 (G1 + G2) := by
  obtain ⟨c1, r1, D1, m1, d1⟩ := h1
  obtain ⟨c2, r2, D2, m2, d2⟩ := h2
  refine ⟨c1.add c2, fun N => ?_, fun Z => D1 Z + D2 Z, fun Z => add_mem (m1 Z) (m2 Z), fun y => ?_⟩
  · obtain ⟨C1, hC1⟩ := r1 N
    obtain ⟨C2, hC2⟩ := r2 N
    refine ⟨C1 + C2, fun y => ?_⟩
    have hp : 0 ≤ (1 + ‖y‖) ^ N := by positivity
    calc (1 + ‖y‖) ^ N * ‖(G1 + G2) y‖ ≤ (1 + ‖y‖) ^ N * (‖G1 y‖ + ‖G2 y‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hp
      _ = (1 + ‖y‖) ^ N * ‖G1 y‖ + (1 + ‖y‖) ^ N * ‖G2 y‖ := by ring
      _ ≤ C1 + C2 := add_le_add (hC1 y) (hC2 y)
  · obtain ⟨E1, e1, f1⟩ := d1 y
    obtain ⟨E2, e2, f2⟩ := d2 y
    refine ⟨E1 + E2, fun Z => by simp [e1, e2], ?_⟩
    rw [Pi.add_apply, orb_add]
    exact f1.add f2

theorem good_smul (c : ℂ) {G : V → X} (h : Good ρ 𝒢 G) : Good ρ 𝒢 (c • G) := by
  obtain ⟨c0, r, D, m, d⟩ := h
  refine ⟨c0.const_smul c, fun N => ?_, fun Z => c • D Z, fun Z => Submodule.smul_mem _ c (m Z),
    fun y => ?_⟩
  · obtain ⟨C, hC⟩ := r N
    refine ⟨‖c‖ * C, fun y => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg c)
  · obtain ⟨E, e, f⟩ := d y
    refine ⟨c • E, fun Z => by simp [e], ?_⟩
    rw [Pi.smul_apply, orb_smul]
    exact f.const_smul c

theorem rapidFam_span {s : Set (V → X)} (h : ∀ G ∈ s, Good ρ (Submodule.span ℂ s) G) :
    RapidFam ρ (Submodule.span ℂ s) := by
  intro G hG
  induction hG using Submodule.span_induction with
  | mem G hG => exact h G hG
  | zero => exact good_zero
  | add G1 G2 _ _ h1 h2 => exact good_add h1 h2
  | smul c G _ h => exact good_smul c h

end Rapid

section Smooth

theorem contDiff_smul_of_on {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E]
    [NormedSpace ℂ E] {O : Set V} (hO : IsOpen O) {η : V → ℂ} (hη : ContDiff ℝ ∞ η)
    (hηO : tsupport η ⊆ O) {f : V → E} (hf : ContDiffOn ℝ ∞ f O) : ContDiff ℝ ∞ (fun x => η x • f x) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ O
  · exact hη.contDiffAt.smul (hf.contDiffAt (hO.mem_nhds hx))
  · have h : η =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hηO h)
    refine (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq ?_
    filter_upwards [h] with y hy
    simp [hy]

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
  (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem contDiffOn_cut {O : Set V} (hO : IsOpen O) {η : V → ℂ} (hη : ContDiff ℝ ∞ η)
    (hηO : tsupport η ⊆ O) {σ : V → LieI ι a} (hσ : ContDiffOn ℝ ∞ σ O)
    (hσu : ∀ x ∈ O, IsUnit (Matrix.of (σ x))) {w : X} (hw : SmV ρ w) :
    ContDiffOn ℝ ∞ (fun q : LieI ι a × V => η q.2 • orb ρ w (mulI q.1 (σ q.2)))
      ({M | IsUnit (Matrix.of M)} ×ˢ Set.univ) := by
  intro q hq
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases hx : q.2 ∈ O
  · have hq1 : IsUnit (Matrix.of q.1) := (Set.mem_prod.1 hq).1
    have hu : IsUnit (Matrix.of (mulI q.1 (σ q.2))) := by rw [of_mulI]; exact hq1.mul (hσu _ hx)
    have hσx : ContDiffAt ℝ ∞ σ q.2 := hσ.contDiffAt (hO.mem_nhds hx)
    have h0 : ContDiffAt ℝ ∞ (fun q : LieI ι a × V => (q.1, σ q.2)) q :=
      contDiffAt_fst.prodMk (ContDiffAt.comp (g := σ) (f := fun q : LieI ι a × V => q.2) q hσx contDiffAt_snd)
    have h1 : ContDiffAt ℝ ∞ (fun q : LieI ι a × V => mulI q.1 (σ q.2)) q :=
      ContDiffAt.comp (g := fun p : LieI ι a × LieI ι a => mulI p.1 p.2) (f := fun q : LieI ι a × V => (q.1, σ q.2))
        q (contDiff_mulI.contDiffAt) h0
    have hw' : ContDiffOn ℝ ∞ (orb ρ w) {M | IsUnit (Matrix.of M)} := hw
    have hwu : ContDiffAt ℝ ∞ (orb ρ w) (mulI q.1 (σ q.2)) := hw'.contDiffAt (isOpen_units.mem_nhds hu)
    have h2 : ContDiffAt ℝ ∞ (fun q : LieI ι a × V => orb ρ w (mulI q.1 (σ q.2))) q :=
      ContDiffAt.comp (g := orb ρ w) (f := fun q : LieI ι a × V => mulI q.1 (σ q.2)) q hwu h1
    have h3 : ContDiffAt ℝ ∞ (fun q : LieI ι a × V => η q.2) q :=
      ContDiffAt.comp (g := η) (f := fun q : LieI ι a × V => q.2) q hη.contDiffAt contDiffAt_snd
    exact h3.smul h2
  · have h : η =ᶠ[𝓝 q.2] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hηO h)
    refine (contDiffAt_const (c := (0 : X))).congr_of_eventuallyEq ?_
    filter_upwards [(continuous_snd.tendsto q).eventually h] with y hy
    simp [hy]

variable {ρ} in
theorem hasFDerivAt_orb_mul {w : X} {Dw : LieI ι a →L[ℝ] X} (hw : HasFDerivAt (orb ρ w) Dw (oneI ι a))
    {S T : LieI ι a} (hST : Matrix.of S * Matrix.of T = 1) :
    HasFDerivAt (fun M => orb ρ w (mulI M S))
      (((opI ρ S).restrictScalars ℝ).comp (Dw.comp (conjL T S))) (oneI ι a) := by
  have hTS : Matrix.of T * Matrix.of S = 1 := mul_eq_one_comm.1 hST
  have hm : ∀ M, mulI S (mulI T (mulI M S)) = mulI M S := by
    intro M
    apply Matrix.of.injective
    simp only [of_mulI]
    rw [← mul_assoc, hST, one_mul]
  have he : (fun M => orb ρ w (mulI M S)) =
      fun M => ((opI ρ S).restrictScalars ℝ) (orb ρ w (conjL T S M)) := by
    funext M
    simp only [ContinuousLinearMap.coe_restrictScalars', orb_eq, opI_mul, conjL_apply, hm]
  have h1 : conjL T S (oneI ι a) = oneI ι a := by
    apply Matrix.of.injective
    simp [conjL_apply, of_mulI, oneI, hTS]
  have h2 : HasFDerivAt (fun M => orb ρ w (conjL T S M)) (Dw.comp (conjL T S)) (oneI ι a) := by
    have hw2 := hw
    rw [← h1] at hw2
    exact hw2.comp (oneI ι a) (conjL T S).hasFDerivAt
  rw [he]
  exact ((opI ρ S).restrictScalars ℝ).hasFDerivAt.comp (oneI ι a) h2

end Smooth

section FT

variable {V P X : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  (μ : Measure V) [μ.IsAddHaarMeasure] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X] (β : V →L[ℝ] V →L[ℝ] ℝ)

theorem continuous_ch (y : V) : Continuous fun x : V => Complex.exp (-(β x y : ℝ) * Complex.I) := by
  have : Continuous fun x : V => β x y := β.continuous₂.comp (continuous_id.prodMk continuous_const)
  fun_prop

theorem integrable_ch {F : V → X} (hF : Continuous F) (hc : HasCompactSupport F) (y : V) :
    Integrable (fun x => Complex.exp (-(β x y : ℝ) * Complex.I) • F x) μ :=
  ((continuous_ch β y).smul hF).integrable_of_hasCompactSupport
    (hc.smul_left (f := fun x => Complex.exp (-(β x y : ℝ) * Complex.I)))

theorem hasFDerivAt_FT_param (y : V) {Ψ : P × V → X} {s : Set P} {k : Set V} (hs : IsOpen s)
    (hk : IsCompact k) (hΨ : ContDiffOn ℝ 1 Ψ (s ×ˢ Set.univ)) (h0 : ∀ p ∈ s, ∀ x ∉ k, Ψ (p, x) = 0)
    {p0 : P} (hp0 : p0 ∈ s) (L : V → P →L[ℝ] X) (hL : ∀ x, HasFDerivAt (fun p => Ψ (p, x)) (L x) p0) :
    ∃ D' : P →L[ℝ] X, (∀ Z, D' Z = ∫ x, Complex.exp (-(β x y : ℝ) * Complex.I) • L x Z ∂μ) ∧
      HasFDerivAt (fun p => FT μ β (fun x => Ψ (p, x)) y) D' p0 := by
  set f : V → ℂ := fun t => Complex.exp (-(β t y : ℝ) * Complex.I) with hf_def
  have hf : LocallyIntegrable f μ := (continuous_ch β y).locallyIntegrable
  set g : P → V → X := fun p t => Ψ (p, -t) with hg_def
  have hmaps : Set.MapsTo (fun q : P × V => (q.1, -q.2)) (s ×ˢ Set.univ) (s ×ˢ Set.univ) :=
    fun q hq => ⟨hq.1, trivial⟩
  have hg : ContDiffOn ℝ 1 (↿g) (s ×ˢ Set.univ) :=
    hΨ.comp (contDiff_fst.prodMk contDiff_snd.neg).contDiffOn hmaps
  have hgs : ∀ p x, p ∈ s → x ∉ -k → g p x = 0 := fun p x hp hx => h0 p hp (-x) (by simpa using hx)
  have H := hasFDerivAt_convolution_right_with_param (μ := μ) (ContinuousLinearMap.lsmul ℝ ℂ) hs hk.neg
    hgs hf hg (p0, 0) hp0
  dsimp only at H
  have hin : HasFDerivAt (fun p : P => (p, (0 : V))) ((ContinuousLinearMap.id ℝ P).prod 0) p0 :=
    (hasFDerivAt_id p0).prodMk (hasFDerivAt_const (0 : V) p0)
  have H2 := H.comp p0 hin
  have hdiff : ∀ x Z, fderiv ℝ (↿g) (p0, x) (Z, 0) = L (-x) Z := by
    intro x Z
    have hd : DifferentiableAt ℝ (↿g) (p0, x) :=
      (hg.contDiffAt ((hs.prod isOpen_univ).mem_nhds ⟨hp0, trivial⟩)).differentiableAt one_ne_zero
    have h1 : HasFDerivAt (fun p => (↿g) (p, x))
        ((fderiv ℝ (↿g) (p0, x)).comp ((ContinuousLinearMap.id ℝ P).prod 0)) p0 :=
      hd.hasFDerivAt.comp p0 (((hasFDerivAt_id p0).prodMk (hasFDerivAt_const x p0)) :
        HasFDerivAt (fun p : P => (p, x)) ((ContinuousLinearMap.id ℝ P).prod 0) p0)
    have h2 : HasFDerivAt (fun p => (↿g) (p, x)) (L (-x)) p0 := hL (-x)
    rw [← h1.unique h2]
    simp
  have hcont : Continuous fun x : V => fderiv ℝ (↿g) (p0, x) :=
    (hg.continuousOn_fderiv_of_isOpen (hs.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) fun x => ⟨hp0, trivial⟩
  have hcs : HasCompactSupport fun x : V => fderiv ℝ (↿g) (p0, x) := by
    refine HasCompactSupport.intro hk.neg fun x hx => ?_
    refine (hasFDerivAt_zero_of_eventually_const 0 ?_).fderiv
    have M2 : (-k)ᶜ ∈ 𝓝 x := hk.neg.isClosed.isOpen_compl.mem_nhds hx
    rw [nhds_prod_eq]
    filter_upwards [Filter.prod_mem_prod (hs.mem_nhds hp0) M2]
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    exact hgs p t hp ht
  refine ⟨_, fun Z => ?_, H2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_)⟩
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply]
    rw [convolution_precompR_apply _ hf hcs hcont, convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [zero_sub, ContinuousLinearMap.lsmul_apply, hdiff, neg_neg, hf_def]
  · simp [Function.comp, convolution_def, FT, hg_def, hf_def]

end FT

section Gen

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [CompleteSpace X] (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) {V : Type} [NormedAddCommGroup V]
  [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
  [μ.IsAddHaarMeasure] (β : V →L[ℝ] V →L[ℝ] ℝ)

theorem good_gen (hS4 : S4) (hβ : ∀ y, (∀ x, β x y = 0) → y = 0)
    (hD : ∀ v, SmV ρ v → ∃ D : LieI ι a →L[ℝ] X, HasFDerivAt (orb ρ v) D (oneI ι a) ∧ ∀ Z, SmV ρ (D Z))
    {O : Set V} (hO : IsOpen O) {σ τ : V → LieI ι a} (hσ : ContDiffOn ℝ ∞ σ O)
    (hτ : ContDiffOn ℝ ∞ τ O) (hστ : ∀ x ∈ O, Matrix.of (σ x) * Matrix.of (τ x) = 1)
    {𝒢 : Submodule ℂ (V → X)}
    (h𝒢 : ∀ (η : V → ℂ) (w : X), ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ O → SmV ρ w →
      FT μ β (fun x => η x • orb ρ w (σ x)) ∈ 𝒢)
    {η : V → ℂ} {w : X} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) (hηO : tsupport η ⊆ O)
    (hw : SmV ρ w) : Good ρ 𝒢 (FT μ β (fun x => η x • orb ρ w (σ x))) := by
  have hσu : ∀ x ∈ O, IsUnit (Matrix.of (σ x)) := fun x hx =>
    ⟨⟨_, _, hστ x hx, mul_eq_one_comm.1 (hστ x hx)⟩, rfl⟩
  have hη0 : ∀ x ∉ O, η x = 0 := fun x hx =>
    (notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hηO h)).eq_of_nhds
  have hF : ∀ (θ : V → ℂ) (v : X), ContDiff ℝ ∞ θ → tsupport θ ⊆ O → SmV ρ v →
      ContDiff ℝ ∞ (fun x => θ x • orb ρ v (σ x)) := fun θ v hθ hθO hv =>
    contDiff_smul_of_on hO hθ hθO
      ((show ContDiffOn ℝ ∞ (orb ρ v) {M | IsUnit (Matrix.of M)} from hv).comp hσ fun x hx => hσu x hx)
  have hFc : ∀ (θ : V → ℂ) (v : X), HasCompactSupport θ →
      HasCompactSupport (fun x => θ x • orb ρ v (σ x)) :=
    fun θ v h => h.smul_right
  obtain ⟨hGc, hGr⟩ := hS4 V μ β hβ X _ (hF η w hη hηO hw) (hFc η w hηc)
  obtain ⟨Dw, hDw, hDwS⟩ := hD w hw
  set b := Module.finBasis ℝ (LieI ι a)
  set coef : V → LieI ι a → Fin (Module.finrank ℝ (LieI ι a)) → ℂ :=
    fun x Z i => (Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (b.coord i))) (conjL (τ x) (σ x) Z)
    with hcoef
  have hcoefC : ∀ Z i, ContDiffOn ℝ ∞ (fun x => coef x Z i) O := by
    intro Z i
    have h0 : ContDiffOn ℝ ∞ (fun x => mulI Z (σ x)) O :=
      ContDiff.comp_contDiffOn (g := fun p : LieI ι a × LieI ι a => mulI p.1 p.2)
        (f := fun x => (Z, σ x)) contDiff_mulI (contDiffOn_const.prodMk hσ)
    have h1 : ContDiffOn ℝ ∞ (fun x => conjL (τ x) (σ x) Z) O :=
      ContDiff.comp_contDiffOn (g := fun p : LieI ι a × LieI ι a => mulI p.1 p.2)
        (f := fun x => (τ x, mulI Z (σ x))) contDiff_mulI (hτ.prodMk h0)
    exact ContDiff.comp_contDiffOn
      (g := ⇑(Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (b.coord i))))
      (f := fun x => conjL (τ x) (σ x) Z) (ContinuousLinearMap.contDiff _) h1
  have hηi : ∀ Z i, ContDiff ℝ ∞ (fun x => η x * coef x Z i) := fun Z i =>
    contDiff_smul_of_on hO hη hηO (hcoefC Z i)
  have hηic : ∀ Z i, HasCompactSupport (fun x => η x * coef x Z i) := fun Z i => hηc.mul_right
  have hηiO : ∀ Z i, tsupport (fun x => η x * coef x Z i) ⊆ O := fun Z i =>
    (tsupport_mul_subset_left).trans hηO
  refine ⟨hGc, hGr, fun Z => ∑ i, FT μ β (fun x => (η x * coef x Z i) • orb ρ (Dw (b i)) (σ x)),
    fun Z => Submodule.sum_mem _ fun i _ => h𝒢 _ _ (hηi Z i) (hηic Z i) (hηiO Z i) (hDwS _),
    fun y => ?_⟩
  set Ψ : LieI ι a × V → X := fun q => η q.2 • orb ρ w (mulI q.1 (σ q.2)) with hΨ
  set Lx : V → LieI ι a →L[ℝ] X :=
    fun x => η x • ((opI ρ (σ x)).restrictScalars ℝ).comp (Dw.comp (conjL (τ x) (σ x))) with hLx
  have hL : ∀ x, HasFDerivAt (fun p => Ψ (p, x)) (Lx x) (oneI ι a) := by
    intro x
    by_cases hx : x ∈ O
    · exact (hasFDerivAt_orb_mul hDw (hστ x hx)).const_smul (η x)
    · have e : (fun p => Ψ (p, x)) = fun _ => 0 := by funext p; simp [hΨ, hη0 x hx]
      rw [e]
      simp only [hLx, hη0 x hx, zero_smul]
      exact hasFDerivAt_const _ _
  have hΨ0 : ∀ p ∈ {M : LieI ι a | IsUnit (Matrix.of M)}, ∀ x ∉ tsupport η, Ψ (p, x) = 0 := by
    intro p _ x hx
    simp [hΨ, image_eq_zero_of_notMem_tsupport hx]
  obtain ⟨D', hD', hder⟩ := hasFDerivAt_FT_param μ β y isOpen_units hηc
    ((contDiffOn_cut ρ hO hη hηO hσ hσu hw).of_le (by simp)) hΨ0 isUnit_oneI Lx hL
  refine ⟨D', fun Z => ?_, ?_⟩
  · have key : ∀ x, Lx x Z = ∑ i, (η x * coef x Z i) • orb ρ (Dw (b i)) (σ x) := by
      intro x
      simp only [hLx, hcoef, ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply,
        LinearMap.coe_toContinuousLinearMap', ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_restrictScalars', orb_eq]
      conv_lhs => rw [← b.sum_repr (conjL (τ x) (σ x) Z)]
      simp only [map_sum, map_smul, ContinuousLinearMap.map_smul_of_tower, Finset.smul_sum, mul_smul,
        Complex.coe_smul, Module.Basis.coord_apply]
    rw [hD']
    beta_reduce
    rw [Finset.sum_apply]
    unfold FT
    rw [← integral_finsetSum _ fun i _ => integrable_ch μ β
      ((hF _ _ (hηi Z i) (hηiO Z i) (hDwS _)).continuous) (hFc _ _ (hηic Z i)) y]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [key, Finset.smul_sum]
  · have e : orb ρ (FT μ β (fun x => η x • orb ρ w (σ x)) y) =
        fun p => FT μ β (fun x => Ψ (p, x)) y := by
      funext M
      rw [orb_eq]
      unfold FT
      rw [← ContinuousLinearMap.integral_comp_comm _
        (integrable_ch μ β (hF η w hη hηO hw).continuous (hFc η w hηc) y)]
      congr 1
      funext x
      simp only [map_smul, hΨ, orb_eq, opI_mul]
    rw [e]
    exact hder

end Gen

end ConjugationOnUnits

open ConjugationOnUnits in
theorem conjugation_units_open : S2 → S4 → S6 := by
  intro hS2 hS4 ι _ a X _ _ _ ρ hρ V _ _ _ _ _ μ _ β hβ O σ τ hO hσ hτ hστ
  obtain ⟨-, -, -, -, -, hD⟩ := hS2 ι a X ρ hρ
  let gen : Set (V → X) := {G | ∃ (η : V → ℂ) (w : X), ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
    tsupport η ⊆ O ∧ SmV ρ w ∧ G = FT μ β (fun x => η x • orb ρ w (σ x))}
  have hmem : ∀ (η : V → ℂ) (w : X), ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ O →
      SmV ρ w → FT μ β (fun x => η x • orb ρ w (σ x)) ∈ Submodule.span ℂ gen :=
    fun η w h1 h2 h3 h4 => Submodule.subset_span ⟨η, w, h1, h2, h3, h4, rfl⟩
  refine ⟨Submodule.span ℂ gen, rapidFam_span fun G hG => ?_, hmem⟩
  obtain ⟨η, w, h1, h2, h3, h4, rfl⟩ := hG
  exact good_gen ρ μ β hS4 hβ hD hO hσ hτ hστ hmem h1 h2 h3 h4

end PositivityTheory.jumpWindows

end

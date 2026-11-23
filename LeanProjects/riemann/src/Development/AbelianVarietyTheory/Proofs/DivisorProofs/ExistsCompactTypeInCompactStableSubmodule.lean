import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDerivedActionFiniteDimUnitaryRep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightCompactDominanceOfMemHighestWeightSpan
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsHighestWeightIrreducibleUnitaryRepU

open Matrix MeasureTheory Finset
open scoped InnerProductSpace ContDiff Topology

noncomputable section

namespace GlobalTheory.KTypeExists

open Formalism.REAL GlobalTheory.UnitaryDerived GlobalTheory.UnitaryHighestWeight

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inUJ_mul {n : ℕ} {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h) :
    inUJ ε (g * h) := by
  unfold inUJ at *
  calc (g * h)ᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [hg, hh]

theorem exists_smooth_equivariant {n : ℕ} {ε : Fin n → Bool} {B : Type} [NormedRing B] [NormedAlgebra ℂ B]
    [CompleteSpace B] {σ : Matrix (Fin n) (Fin n) ℂ → B} (h1 : σ 1 = 1)
    (hcont : ContinuousOn σ {g | inUJ ε g}) :
    ∃ F : Matrix (Fin n) (Fin n) ℂ → B, SmoothOnGV ε F ∧ F 1 = 1 ∧
      ∀ k, inUJ ε k → (∀ g, inUJ ε g → σ (k * g) = σ k * σ g) → ∀ x, inUJ ε x → F (k * x) = σ k * F x := by
  obtain ⟨hemb, hrange⟩ := isClosedEmbeddingMatrix n ε
  set μ := muG ε
  have hmem : ∀ g : UJ ε, inUJ ε (toM g) := fun g => g.2
  have hu : Continuous fun g : UJ ε => toM g := hemb.continuous
  have hb : Continuous fun g : UJ ε => σ (toM g) := hcont.comp_continuous hu hmem
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := hmem 1
  have hnb : {g | ‖σ g - 1‖ < 1 / 2} ∈ 𝓝[{g | inUJ ε g}] (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h := (hcont 1 hone) (Metric.ball_mem_nhds _ (half_pos one_pos))
    simpa [h1, Set.preimage, dist_eq_norm] using h
  obtain ⟨U, hU, hUs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hnb
  obtain ⟨φ, hφU, hφc, hφ, hφr, hφ1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hU
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => (hφr ⟨y, rfl⟩).1
  have hψ : Continuous fun g : UJ ε => φ (toM g) := hφ.continuous.comp hu
  have hψc : HasCompactSupport fun g : UJ ε => φ (toM g) := hφc.comp_isClosedEmbedding hemb
  have hint' : ∀ x, inUJ ε x → Integrable (fun g : UJ ε => φ (toM g) • σ (x * toM g)) μ := fun x hx =>
    (hψ.smul (hcont.comp_continuous (continuous_const.matrix_mul hu)
      fun g => inUJ_mul hx (hmem g))).integrable_of_hasCompactSupport hψc.smul_right
  have hint : Integrable (fun g : UJ ε => φ (toM g) • σ (toM g)) μ := by simpa using hint' 1 hone
  have hψi : Integrable (fun g : UJ ε => φ (toM g)) μ := hψ.integrable_of_hasCompactSupport hψc
  have hpos : 0 < ∫ g : UJ ε, φ (toM g) ∂μ :=
    hψ.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hψc (fun g => hφ0 _)
      (by show φ 1 ≠ 0; rw [hφ1]; exact one_ne_zero)
  set c := ∫ g : UJ ε, φ (toM g) ∂μ with hc
  set A := ∫ g : UJ ε, φ (toM g) • σ (toM g) ∂μ with hA
  have hAu : ∃ A' : B, A * A' = 1 := by
    have e1 : ∫ g : UJ ε, (φ (toM g) • σ (toM g) - φ (toM g) • (1 : B)) ∂μ = A - c • (1 : B) := by
      rw [integral_sub hint (hψi.smul_const _), integral_smul_const]
    have e2 : ‖∫ g : UJ ε, (φ (toM g) • σ (toM g) - φ (toM g) • (1 : B)) ∂μ‖
        ≤ ∫ g : UJ ε, φ (toM g) * (1 / 2) ∂μ := by
      refine norm_integral_le_of_norm_le (hψi.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hφ0 _)]
      by_cases hg : φ (toM g) = 0
      · simp [hg]
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hUs ⟨hφU (subset_tsupport _ hg), hmem g⟩)) (hφ0 _)
    rw [e1, integral_mul_const, ← hc] at e2
    have e3 : ‖(1 : B) - c⁻¹ • A‖ < 1 := by
      have : (1 : B) - c⁻¹ • A = -(c⁻¹ • (A - c • (1 : B))) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul, neg_sub]
      rw [this, norm_neg, norm_smul, Real.norm_of_nonneg (inv_pos.2 hpos).le, inv_mul_lt_iff₀ hpos]
      linarith
    obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one e3
    rw [sub_sub_cancel] at hu
    refine ⟨c⁻¹ • (↑u⁻¹ : B), ?_⟩
    rw [mul_smul_comm, ← smul_mul_assoc, ← hu, Units.mul_inv]
  obtain ⟨A', hA'⟩ := hAu
  let y : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun x => Jm ε * xᴴ * Jm ε
  have hy : ContDiff ℝ ∞ y := contDiff_matMul (contDiff_matMul contDiff_const contDiff_adj) contDiff_const
  have hyx : ∀ x, inUJ ε x → y x * x = 1 := fun x hx => by
    have h : xᴴ * Jm ε * x = Jm ε := hx
    calc y x * x = Jm ε * (xᴴ * Jm ε * x) := by simp only [y, Matrix.mul_assoc]
      _ = 1 := by rw [h, Jm_mul_self]
  have hform : ∀ x, inUJ ε x →
      ∫ g : UJ ε, φ (toM g) • σ (x * toM g) ∂μ = ∫ g : UJ ε, φ (y x * toM g) • σ (toM g) ∂μ := by
    intro x hx
    obtain ⟨z, hz⟩ : x ∈ Set.range (fun g : UJ ε => toM g) := by
      rw [show Set.range (fun g : UJ ε => toM g) = _ from hrange]; exact hx
    have hz' : toM z = x := hz
    rw [← integral_mul_left_eq_self (fun g : UJ ε => φ (y x * toM g) • σ (toM g)) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : toM (z * g) = x * toM g := by rw [← hz']; rfl
    simp only [e]
    rw [← Matrix.mul_assoc, hyx x hx, Matrix.one_mul]
  refine ⟨fun x => (∫ g : UJ ε, φ (toM g) • σ (x * toM g) ∂μ) * A', ?_, ?_, ?_⟩
  · intro x₀ _
    have hC : IsCompact (Set.image2 (· * ·) (Metric.closedBall x₀ 1) (tsupport φ)) := by
      rw [← Set.image_prod]
      exact ((isCompact_closedBall x₀ 1).prod hφc).image (contDiff_matMul contDiff_fst contDiff_snd).continuous
    have hK := hemb.isCompact_preimage hC
    have hs : ContDiff ℝ ∞ fun x => ∫ g in (fun g : UJ ε => toM g) ⁻¹'
        (Set.image2 (· * ·) (Metric.closedBall x₀ 1) (tsupport φ)), φ (y x * toM g) • σ (toM g) ∂μ :=
      contDiff_infty.2 fun m => GlobalTheory.GardingVec.contDiff_setIntegral_nat μ hK (hu.prodMk hb) m
        (fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × B) => φ (y z.1 * z.2.1) • z.2.2)
        ((hφ.comp (contDiff_matMul (hy.comp contDiff_fst) (contDiff_fst.comp contDiff_snd))).smul
          (contDiff_snd.comp contDiff_snd))
    refine ⟨Metric.ball x₀ 1, _, Metric.isOpen_ball, Metric.mem_ball_self one_pos,
      (hs.mul (contDiff_const (c := A'))).contDiffOn, fun x hx hxG => ?_⟩
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, ← hform x hxG]
    intro g hg
    by_contra hne
    refine hg ⟨x, Metric.ball_subset_closedBall hx, y x * toM g,
      subset_tsupport _ fun h => hne (by rw [h, zero_smul]), ?_⟩
    show x * (y x * toM g) = toM g
    rw [← Matrix.mul_assoc, mul_eq_one_comm.1 (hyx x hxG), Matrix.one_mul]
  · simpa only [Matrix.one_mul] using hA'
  · intro k hk hmul x hx
    have := (ContinuousLinearMap.mul ℂ B (σ k)).integral_comp_comm (hint' x hx)
    rw [ContinuousLinearMap.mul_apply'] at this
    beta_reduce
    rw [← mul_assoc (σ k), ← this]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    beta_reduce
    rw [Matrix.mul_assoc, hmul _ (inUJ_mul hx (hmem g)), ContinuousLinearMap.mul_apply', mul_smul_comm]

end Smooth

section Lie

variable {n : ℕ} {ε : Fin n → Bool}

theorem inK_smul {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) : inK ε ((t : ℂ) • X) := by
  refine ⟨?_, by rw [Matrix.smul_mul, Matrix.mul_smul, hX.2]⟩
  have h : Xᴴ * Jm ε + Jm ε * X = 0 := hX.1
  show ((t : ℂ) • X)ᴴ * Jm ε + Jm ε * ((t : ℂ) • X) = 0
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [← smul_add, h, smul_zero]

theorem exp_memK {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε :=
  (kFacts n ε).2.2.2.1 _ (inK_smul hX t)

theorem entry_eq_zero {X : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X) {a b : Fin n} (hab : ε a ≠ ε b) :
    X a b = 0 := by
  have h := congrFun (congrFun hX a) b
  simp only [Jm, mul_diagonal, diagonal_mul] at h
  cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at h hab
  · linear_combination (1 / 2 : ℂ) * h
  · linear_combination (-1 / 2 : ℂ) * h

theorem single_comm {a b : Fin n} (hab : ε a = ε b) :
    Matrix.single a b (1 : ℂ) * Jm ε = Jm ε * Matrix.single a b 1 := by
  ext i j
  simp only [Jm, mul_diagonal, diagonal_mul, Matrix.single_apply]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    simp [hab]
  · simp [h]

theorem conj_single {a b : Fin n} (hab : ε a = ε b) :
    Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Jm ε = Matrix.single b a 1 := by
  rw [conjTranspose_single, star_one, ← single_comm hab.symm, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]

theorem cpart_inK {a b : Fin n} (hab : ε a = ε b) :
    inK ε (cpart1 ε (Matrix.single a b 1)) ∧ inK ε (cpart2 ε (Matrix.single a b 1)) := by
  obtain ⟨h1, h2, -⟩ := cpartMem n ε (Matrix.single a b 1)
  refine ⟨⟨h1, ?_⟩, h2, ?_⟩
  · rw [cpart1, conj_single hab, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      single_comm hab, single_comm hab.symm]
  · rw [cpart2, conj_single hab, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      single_comm hab, single_comm hab.symm]

theorem diag_inK (θ : Fin n → ℝ) : inK ε (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by
  have h : (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) * Jm ε =
      Jm ε * Matrix.diagonal fun a => (θ a : ℂ) * Complex.I := by
    simp only [Jm, diagonal_mul_diagonal, mul_comm]
  refine ⟨?_, h⟩
  show _ * _ + _ = 0
  rw [diag_skew, Matrix.neg_mul, h, neg_add_cancel]

end Lie

section Deriv

variable {n : ℕ} {ε : Fin n → Bool} {B : Type} [NormedRing B] [NormedAlgebra ℂ B]
  {F : Matrix (Fin n) (Fin n) ℂ → B}

theorem rdV_left (hs : SmoothOnGV ε F) (hK : ∀ k ∈ Kset ε, ∀ x, inUJ ε x → F (k * x) = F k * F x)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    RdV X F g = F g * RdV X F 1 := by
  rw [← ((hasDerivAt_rdV hs hX).const_mul (F g)).deriv, RdV]
  congr 1
  funext t
  exact hK _ hg _ (exp_indefinite_unitary_holds n ε X hX t)

theorem rdV_one_of_eqK (hs : SmoothOnGV ε F) {f : Matrix (Fin n) (Fin n) ℂ → B} {b : B}
    (hf : ∀ g ∈ Kset ε, f g = F g * b) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    RdV X f 1 = RdV X F 1 * b := by
  rw [← ((hasDerivAt_rdV hs hX.1).mul_const b).deriv, RdV]
  congr 1
  funext t
  rw [Matrix.one_mul]
  exact hf _ (exp_memK hX t)

theorem eabV_left (hs : SmoothOnGV ε F) (hK : ∀ k ∈ Kset ε, ∀ x, inUJ ε x → F (k * x) = F k * F x)
    (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    EabV ε a b F g = F g * EabV ε a b F 1 := by
  obtain ⟨h1, h2, -⟩ := cpartMem n ε (Matrix.single a b 1)
  simp only [EabV, EcV]
  rw [rdV_left hs hK h1 hg, rdV_left hs hK h2 hg, mul_add, mul_smul_comm]

theorem eabV_eabVK (hs : SmoothOnGV ε F) (hK : ∀ k ∈ Kset ε, ∀ x, inUJ ε x → F (k * x) = F k * F x)
    {a b : Fin n} (hab : ε a = ε b) (c d : Fin n) :
    EabV ε a b (EabV ε c d F) 1 = EabV ε a b F 1 * EabV ε c d F 1 := by
  obtain ⟨h1, h2⟩ := cpart_inK hab
  have h := fun g hg => eabV_left hs hK c d (g := g) hg
  show RdV _ _ 1 + Complex.I • RdV _ _ 1 = (RdV _ F 1 + Complex.I • RdV _ F 1) * _
  rw [rdV_one_of_eqK hs h h1, rdV_one_of_eqK hs h h2, add_mul, smul_mul_assoc]

theorem kRel_eabV (hs : SmoothOnGV ε F) (hK : ∀ k ∈ Kset ε, ∀ x, inUJ ε x → F (k * x) = F k * F x) :
    KRel ε fun a b => EabV ε a b F 1 := by
  intro a b c d hab hcd
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  have := eabGlV n ε B F a b c d 1 hs hone
  rwa [eabV_eabVK hs hK hab, eabV_eabVK hs hK hcd] at this

end Deriv

section Unit

variable {n : ℕ} {ε : Fin n → Bool} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {π : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)}

theorem rdV_skewK (hs : SmoothOnGV ε π) (h1 : π 1 = 1) (hiso : ∀ g ∈ Kset ε, ∀ v, ‖π g v‖ = ‖v‖)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (x y : W) :
    ⟪RdV X π 1 x, y⟫_ℂ = -⟪x, RdV X π 1 y⟫_ℂ := by
  have h := (hasDerivAt_apply hs hX.1 x).inner ℂ (hasDerivAt_apply hs hX.1 y)
  have hc : (fun t : ℝ => ⟪π (NormedSpace.exp ((t : ℂ) • X)) x, π (NormedSpace.exp ((t : ℂ) • X)) y⟫_ℂ)
      = fun _ => ⟪x, y⟫_ℂ := by
    funext t
    exact LinearIsometry.inner_map_map
      ⟨(π (NormedSpace.exp ((t : ℂ) • X))).toLinearMap, hiso _ (exp_memK hX t)⟩ x y
  rw [hc] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, h1, ContinuousLinearMap.one_apply] at h0
  linear_combination h0

theorem exists_derived (hs : SmoothOnGV ε π) (h1 : π 1 = 1)
    (hK : ∀ k ∈ Kset ε, ∀ x, inUJ ε x → π (k * x) = π k * π x) (hiso : ∀ g ∈ Kset ε, ∀ v, ‖π g v‖ = ‖v‖) :
    ∃ E : Fin n → Fin n → Module.End ℂ W, KRel ε E ∧ KUnit ε E ∧
      ∀ Z : Matrix (Fin n) (Fin n) ℂ, inK ε Z → ∀ v,
        HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0 := by
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  refine ⟨fun a b => (EabV ε a b π 1).toLinearMap, ?_, ?_, ?_⟩
  · intro a b c d hab hcd
    have := congrArg ContinuousLinearMap.toLinearMap (kRel_eabV hs hK a b c d hab hcd)
    split_ifs at this ⊢ <;> exact this
  · intro a b hab x y
    obtain ⟨h1', h2'⟩ := cpart_inK hab
    have e1 : cpart1 ε (Matrix.single b a 1) = ((-1 : ℝ) : ℂ) • cpart1 ε (Matrix.single a b (1 : ℂ)) := by
      rw [cpart1, cpart1, conj_single hab, conj_single hab.symm, ← neg_sub, smul_neg]
      push_cast
      rw [neg_one_smul]
    have e2 : cpart2 ε (Matrix.single b a 1) = cpart2 ε (Matrix.single a b (1 : ℂ)) := by
      rw [cpart2, cpart2, conj_single hab, conj_single hab.symm, add_comm]
    have e3 := (rdLinV n _ _ π π _ _ (-1) 0 1 hs hs h1'.1 h1'.1 hone).2.1
    simp only [EabV, EcV, e1, e2, e3, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right]
    have s1 := rdV_skewK hs h1 hiso h1' x y
    have s2 := rdV_skewK hs h1 hiso h2' x y
    rw [s1, s2]
    simp
  · intro Z hZ v
    have := hasDerivAt_apply hs hZ.1 v
    rw [rdV_eq_sum hs hZ.1] at this
    simpa using this

end Unit

section Weights

open Formalism.MainNotions.S

variable {n : ℕ} {ε : Fin n → Bool} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {π : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)}

theorem group_zeroK (h1 : π 1 = 1) (Z : Matrix (Fin n) (Fin n) ℂ) (v : W) :
    π (NormedSpace.exp (((0 : ℝ) : ℂ) • Z)) v = v := by
  simp [h1]

theorem group_addK (hK : ∀ k ∈ Kset ε, ∀ x, inUJ ε x → π (k * x) = π k * π x)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) (s t : ℝ) (v : W) :
    π (NormedSpace.exp (((s + t : ℝ) : ℂ) • Z)) v =
      π (NormedSpace.exp ((s : ℂ) • Z)) (π (NormedSpace.exp ((t : ℂ) • Z)) v) := by
  rw [Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute _ _
    (((Commute.refl Z).smul_left _).smul_right _), hK _ (exp_memK hZ s) _ (exp_indefinite_unitary_holds n ε Z hZ.1 t)]
  rfl

theorem isWtOn_of_isWeightK (h1 : π 1 = 1) (hK : ∀ k ∈ Kset ε, ∀ x, inUJ ε x → π (k * x) = π k * π x)
    (E : Fin n → Fin n → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin n) (Fin n) ℂ, inK ε Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (μ : Fin n → ℝ) (v : W) (hv : IsWeight E μ v) : IsWtOn (Kset ε) π μ v := by
  intro θ _
  have h := eigen (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)))
    (∑ a, ((θ a : ℂ) * Complex.I) • E a a) (group_zeroK h1 _) (group_addK hK (diag_inK θ))
    (fun w => by
      have := hE _ (diag_inK θ) w
      rw [UnitaryHighestWeight.sum_diag] at this
      simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using this)
    v (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) (by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, hv _, smul_smul, ← Finset.sum_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring)
  simp only [exp_diag, one_mul] at h
  exact h

theorem isWeight_of_isWtOnK (E : Fin n → Fin n → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin n) (Fin n) ℂ, inK ε Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (μ : Fin n → ℝ) (v : W) (hv : IsWtOn (Kset ε) π μ v) : IsWeight E μ v := by
  intro a
  set θ : Fin n → ℝ := Pi.single a 1 with hθ
  have h1 := hE _ (diag_inK θ) v
  rw [UnitaryHighestWeight.sum_diag] at h1
  have h2 : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)) v) =
      fun t : ℝ => Complex.exp ((μ a * Complex.I) * t) • v := by
    funext t
    have hm := exp_memK (diag_inK (ε := ε) θ) t
    rw [exp_diag] at hm ⊢
    rw [hv (fun b => t * θ b) hm]
    congr 2
    simp [hθ, Pi.single_apply]
    ring
  have h3 : HasDerivAt (fun t : ℝ => Complex.exp ((μ a * Complex.I) * t) • v) ((μ a * Complex.I) • v) 0 := by
    have h4 : HasDerivAt (fun t : ℝ => (μ a * Complex.I) * (t : ℂ)) (μ a * Complex.I) 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (μ a * Complex.I)
    simpa using h4.cexp.smul_const v
  rw [h2] at h1
  have h5 := h1.unique h3
  have h6 : ∑ b, ((θ b : ℂ) * Complex.I) • E b b v = Complex.I • E a a v := by
    rw [Finset.sum_eq_single a]
    · simp [hθ]
    · intro b _ hb
      simp [hθ, Pi.single_eq_of_ne hb]
    · simp
  rw [h6, mul_comm, ← smul_smul] at h5
  exact smul_right_injective W Complex.I_ne_zero h5

theorem stable_of_derivedK [FiniteDimensional ℂ W] (h1 : π 1 = 1)
    (hK : ∀ k ∈ Kset ε, ∀ x, inUJ ε x → π (k * x) = π k * π x) (E : Fin n → Fin n → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin n) (Fin n) ℂ, inK ε Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (S : Submodule ℂ W) (hS : KStable ε E S) : IsKStableOn ε π S := by
  intro g hg v hv
  obtain ⟨Y, hY, hg', -⟩ := compact_exponential_surjective n ε g hg
  have h := stable (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Y))) (∑ a, ∑ b, Y a b • E a b)
    (group_zeroK h1 _) (group_addK hK hY)
    (fun w => by simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using hE _ hY w) S
    (fun w hw => by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      refine S.sum_mem fun a _ => S.sum_mem fun b _ => ?_
      by_cases hab : ε a = ε b
      · exact S.smul_mem _ (hS a b hab w hw)
      · rw [entry_eq_zero hY.2 hab, zero_smul]
        exact S.zero_mem) v hv 1
  simpa [hg'] using h

theorem cdom_of_mem_kSpan (E : Fin n → Fin n → Module.End ℂ W) (Λ μ : Fin n → ℝ) (x v : W) (hr : KRel ε E)
    (hk : KUnit ε E) (hΛ : KHighest ε E Λ x) (hv : v ∈ kSpan ε E x) (hv0 : v ≠ 0) (hμ : IsWeight E μ v) :
    CDom ε μ Λ := by
  by_contra hne
  rw [compact_span_eq_lowering hr hΛ] at hv
  have key : ∀ z ∈ lowSpan ε E x, ⟪z, v⟫_ℂ = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      refine compact_weight_orthogonal W n _ E _ μ _ v hk (word_action_weight hr hΛ.1 w (fun q hq => (hw q hq).1)) hμ ?_
      intro heq
      exact hne (heq ▸ cdom_add_lowering_word _ Λ w hw)
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
    | smul c y _ hy => rw [inner_smul_left, hy, mul_zero]
  exact hv0 (inner_self_eq_zero.mp (key v hv))

theorem exists_highest [FiniteDimensional ℂ W] [Nontrivial W] (hs : SmoothOnGV ε π) (h1 : π 1 = 1)
    (hK : ∀ k ∈ Kset ε, ∀ x, inUJ ε x → π (k * x) = π k * π x) (hiso : ∀ g ∈ Kset ε, ∀ v, ‖π g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ W, IsKStableOn ε π S → S = ⊥ ∨ S = ⊤) :
    ∃ Λ : Fin n → ℝ, (∃ v, v ≠ 0 ∧ IsWtOn (Kset ε) π Λ v) ∧
      ∀ (μ : Fin n → ℝ) (v : W), v ≠ 0 → IsWtOn (Kset ε) π μ v → CDom ε μ Λ := by
  obtain ⟨E, hr, hk, hE⟩ := exists_derived hs h1 hK hiso
  obtain ⟨x, -, hx, Λ, hΛ⟩ := highestWeightExists_holds W n ε E ⊤ inferInstance hr hk (fun _ _ _ _ _ => trivial) top_ne_bot
  have hxm : x ∈ kSpan ε E x := Submodule.mem_sInf.2 fun S hS => hS.1
  have hst : KStable ε E (kSpan ε E x) := fun a b hab y hy =>
    Submodule.mem_sInf.2 fun S hS => hS.2 a b hab y (Submodule.mem_sInf.1 hy S hS)
  have htop : kSpan ε E x = ⊤ := by
    rcases hirr _ (stable_of_derivedK h1 hK E hE _ hst) with h | h
    · rw [h] at hxm
      exact absurd hxm hx
    · exact h
  exact ⟨Λ, ⟨x, hx, isWtOn_of_isWeightK h1 hK E hE Λ x hΛ.1⟩, fun μ v hv hw =>
    cdom_of_mem_kSpan E Λ μ x v hr hk hΛ (htop ▸ trivial) hv (isWeight_of_isWtOnK E hE μ v hw)⟩

end Weights

section Main

open Formalism.MainNotions.S

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem exists_minimal (S : Submodule ℂ H) [FiniteDimensional ℂ S] (hS : IsKStableOn ε σ S) (h0 : S ≠ ⊥) :
    ∃ S' : Submodule ℂ H, S' ≤ S ∧ S' ≠ ⊥ ∧ IsKStableOn ε σ S' ∧
      ∀ T : Submodule ℂ H, T ≤ S' → IsKStableOn ε σ T → T = ⊥ ∨ T = S' := by
  obtain ⟨S', ⟨hle, hne, hst⟩, hmin⟩ := (measure fun T : Submodule ℂ H => Module.finrank ℂ T).wf.has_min
    {T | T ≤ S ∧ T ≠ ⊥ ∧ IsKStableOn ε σ T} ⟨S, le_rfl, h0, hS⟩
  refine ⟨S', hle, hne, hst, fun T hT hTs => ?_⟩
  by_contra hcon
  push Not at hcon
  haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hle
  exact hmin T ⟨hT.trans hle, hcon.1, hTs⟩ (Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hT hcon.2))

theorem proj_comm (hσ : IsURepOn (UJset ε) σ) (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (hS : IsKStableOn ε σ S) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v : H) :
    S.starProjection (σ k v) = σ k (S.starProjection v) := by
  have hk' : kᴴ ∈ Kset ε := by
    refine ⟨Unitary.star_mem hk.1, ?_⟩
    have := congrArg conjTranspose hk.2
    rw [conjTranspose_mul, conjTranspose_mul, Jm_conjTranspose] at this
    exact this.symm
  have hkU : k ∈ UJset ε := (kFacts n ε).1 k hk
  have hkU' : kᴴ ∈ UJset ε := (kFacts n ε).1 _ hk'
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hS k hk _ (Submodule.starProjection_apply_mem S v)) fun w hw => ?_
  have hkk : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk.1
  have hw' : w = σ k (σ kᴴ w) := by
    have := hσ.1.2 k hkU _ hkU'
    rw [hkk, hσ.1.1] at this
    exact DFunLike.congr_fun this w
  rw [← map_sub, hw']
  have := LinearIsometry.inner_map_map (𝕜 := ℂ) ⟨(σ k).toLinearMap, hσ.2.1 k hkU⟩ (v - S.starProjection v) (σ kᴴ w)
  exact this.trans (Submodule.starProjection_inner_eq_zero v _ (hS _ hk' w hw))

theorem exists_smooth_restrict (hσ : IsURepOn (UJset ε) σ) (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (hS : IsKStableOn ε σ S) :
    ∃ π : Matrix (Fin n) (Fin n) ℂ → (S →L[ℂ] S), SmoothOnGV ε π ∧ π 1 = 1 ∧
      (∀ k ∈ Kset ε, ∀ x, inUJ ε x → π (k * x) = π k * π x) ∧ ∀ k ∈ Kset ε, ∀ v : S, (π k v : H) = σ k v := by
  haveI : CompleteSpace S := FiniteDimensional.complete ℂ S
  let b : Matrix (Fin n) (Fin n) ℂ → (S →L[ℂ] S) := fun g => S.orthogonalProjection ∘L σ g ∘L S.subtypeL
  have hb : ∀ g (v : S), (b g v : H) = S.starProjection (σ g v) := fun g v => rfl
  have hbK : ∀ k ∈ Kset ε, ∀ v : S, (b k v : H) = σ k v := fun k hk v => by
    rw [hb, (Submodule.starProjection_eq_self_iff (K := S)).2 (hS k hk v v.2)]
  have hb1 : b 1 = 1 := by
    ext v
    rw [hb, hσ.1.1]
    exact (Submodule.starProjection_eq_self_iff (K := S)).2 v.2
  have hcont : ContinuousOn b {g | inUJ ε g} :=
    continuousOn_clm_apply.2 fun v => S.orthogonalProjection.continuous.comp_continuousOn (hσ.2.2 v)
  have hmul : ∀ k ∈ Kset ε, ∀ g, inUJ ε g → b (k * g) = b k * b g := fun k hk g hg => by
    ext v
    rw [ContinuousLinearMap.mul_apply, hbK k hk, hb, hb, hσ.1.2 k ((kFacts n ε).1 k hk) g hg,
      ContinuousLinearMap.comp_apply, proj_comm hσ S hS hk]
  obtain ⟨F, hF, hF1, hFK⟩ := exists_smooth_equivariant hb1 hcont
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  have hFb : ∀ k ∈ Kset ε, F k = b k := fun k hk => by
    simpa [hF1] using hFK k ((kFacts n ε).1 k hk) (hmul k hk) 1 hone
  refine ⟨F, hF, hF1, fun k hk x hx => ?_, fun k hk v => ?_⟩
  · rw [hFb k hk]
    exact hFK k ((kFacts n ε).1 k hk) (hmul k hk) x hx
  · rw [hFb k hk, hbK k hk]

theorem exists_kType : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : GlobalTheory.HolDict.Mt n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S →
    IsKStableOn ε σ S → S ≠ ⊥ → ∃ (μ : Fin n → ℝ) (S' : Submodule ℂ H), S' ≤ S ∧ IsKTypeOf ε σ μ S' := by
  intro n ε H _ _ σ hσ S _ hS h0
  obtain ⟨S', hle, hne, hst, hmin⟩ := exists_minimal S hS h0
  haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hle
  haveI : Nontrivial S' := Submodule.nontrivial_iff_ne_bot.2 hne
  obtain ⟨π, hs, h1, hK, hπ⟩ := exists_smooth_restrict hσ S' hst
  have hiso : ∀ g ∈ Kset ε, ∀ v, ‖π g v‖ = ‖v‖ := fun g hg v => by
    rw [Submodule.coe_norm, hπ g hg, hσ.2.1 g ((kFacts n ε).1 g hg), Submodule.coe_norm]
  have hwt : ∀ (μ : Fin n → ℝ) (v : S'), IsWtOn (Kset ε) π μ v ↔ IsWtOn (Kset ε) σ μ (v : H) := fun μ v =>
    forall₂_congr fun θ hθ => by rw [← hπ _ hθ, ← Submodule.coe_smul, Subtype.coe_inj]
  obtain ⟨Λ, ⟨x, hx, hxw⟩, hΛ⟩ := exists_highest hs h1 hK hiso fun T hT => by
    rcases hmin (T.map S'.subtype) (Submodule.map_subtype_le _ _) (by
      rintro g hg _ ⟨v, hv, rfl⟩
      exact ⟨π g v, hT g hg v hv, hπ g hg v⟩) with h | h
    · exact Or.inl (Submodule.map_injective_of_injective S'.injective_subtype (by rw [h, Submodule.map_bot]))
    · exact Or.inr (Submodule.map_injective_of_injective S'.injective_subtype
        (by rw [h, Submodule.map_top, Submodule.range_subtype]))
  refine ⟨Λ, S', hle, inferInstance, hst, hmin, ⟨x, x.2, fun h => hx (Subtype.ext h), (hwt Λ x).1 hxw⟩,
    fun μ v hv hv0 hw => hΛ μ ⟨v, hv⟩ (fun h => hv0 (congrArg Subtype.val h)) ((hwt μ ⟨v, hv⟩).2 hw)⟩

end Main

end GlobalTheory.KTypeExists

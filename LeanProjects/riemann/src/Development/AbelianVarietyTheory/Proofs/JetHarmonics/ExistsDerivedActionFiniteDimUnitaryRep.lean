import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.PeriodIntegrals.UpqRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat

open Matrix MeasureTheory Finset
open scoped InnerProductSpace ContDiff Topology

noncomputable section

namespace GlobalTheory.UnitaryDerived

open Formalism.REAL

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem differentiableAt_exp_line {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    DifferentiableAt ℝ (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) 0 := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)).differentiableAt
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun x => x i j
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  exact (LinearMap.toContinuousLinearMap L).differentiableAt.comp 0 h

end

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_matMul {n : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f g : P → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ fun p => f p * g p := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun l _ => (contDiff_pi.1 (contDiff_pi.1 hf i) l).mul (contDiff_pi.1 (contDiff_pi.1 hg l) j)

theorem contDiff_adj {n : ℕ} : ContDiff ℝ ∞ fun x : Matrix (Fin n) (Fin n) ℂ => xᴴ := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun x => xᴴ
      map_add' := fun x y => conjTranspose_add x y
      map_smul' := fun c x => by simp [conjTranspose_smul] }
  exact (LinearMap.toContinuousLinearMap L).contDiff

theorem smooth_of_continuous {n : ℕ} {ε : Fin n → Bool} {B : Type} [NormedRing B] [NormedAlgebra ℂ B]
    [CompleteSpace B] {σ : Matrix (Fin n) (Fin n) ℂ → B} (h1 : σ 1 = 1)
    (hmul : ∀ a, inUJ ε a → ∀ b, inUJ ε b → σ (a * b) = σ a * σ b)
    (hcont : ContinuousOn σ {g | inUJ ε g}) : SmoothOnGV ε σ := by
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
  have hint : Integrable (fun g : UJ ε => φ (toM g) • σ (toM g)) μ :=
    (hψ.smul hb).integrable_of_hasCompactSupport hψc.smul_right
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
  have hform : ∀ x, inUJ ε x → σ x * A = ∫ g : UJ ε, φ (y x * toM g) • σ (toM g) ∂μ := by
    intro x hx
    obtain ⟨z, hz⟩ : x ∈ Set.range (fun g : UJ ε => toM g) := by
      rw [show Set.range (fun g : UJ ε => toM g) = _ from hrange]; exact hx
    have hz' : toM z = x := hz
    have := (ContinuousLinearMap.mul ℂ B (σ x)).integral_comp_comm hint
    rw [ContinuousLinearMap.mul_apply'] at this
    rw [hA, ← this, ← integral_mul_left_eq_self (fun g : UJ ε => φ (y x * toM g) • σ (toM g)) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : toM (z * g) = x * toM g := by rw [← hz']; rfl
    simp only [e]
    rw [← Matrix.mul_assoc, hyx x hx, Matrix.one_mul, hmul _ hx _ (hmem g), ContinuousLinearMap.mul_apply',
      mul_smul_comm]
  intro x₀ _
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
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, ← hform x hxG, mul_assoc, hA', mul_one]
  intro g hg
  by_contra hne
  refine hg ⟨x, Metric.ball_subset_closedBall hx, y x * toM g,
    subset_tsupport _ fun h => hne (by rw [h, zero_smul]), ?_⟩
  show x * (y x * toM g) = toM g
  rw [← Matrix.mul_assoc, mul_eq_one_comm.1 (hyx x hxG), Matrix.one_mul]

section Deriv

variable {n : ℕ} {ε : Fin n → Bool} {B : Type} [NormedRing B] [NormedAlgebra ℂ B]
  {σ : Matrix (Fin n) (Fin n) ℂ → B}

theorem hasDerivAt_rdV {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : SmoothOnGV ε f) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) (RdV X f 1) 0 := by
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simpa using exp_indefinite_unitary_holds n ε X hX 0
  obtain ⟨U, F, hU, h1, hF, hfF⟩ := hf 1 hone
  have hd : DifferentiableAt ℝ (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) 0 :=
    differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => differentiableAt_exp_line X i j
  have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by simp
  have hFd : DifferentiableAt ℝ F (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [h0]
    exact (hF.contDiffAt (hU.mem_nhds h1)).differentiableAt (by simp)
  have hev : (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      F ∘ fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) := by
    filter_upwards [hd.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU.mem_nhds h1)] with t ht
    exact hfF _ ht (exp_indefinite_unitary_holds n ε X hX t)
  have := ((hFd.comp 0 hd).congr_of_eventuallyEq hev).hasDerivAt
  simpa only [RdV, Matrix.one_mul] using this

theorem rdV_mul (hs : SmoothOnGV ε σ) (hmul : ∀ a, inUJ ε a → ∀ b, inUJ ε b → σ (a * b) = σ a * σ b)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    RdV X σ g = σ g * RdV X σ 1 := by
  rw [← ((hasDerivAt_rdV hs hX).const_mul (σ g)).deriv, RdV]
  congr 1
  funext t
  exact hmul _ hg _ (exp_indefinite_unitary_holds n ε X hX t)

theorem rdV_one_of_eq (hs : SmoothOnGV ε σ) {f : Matrix (Fin n) (Fin n) ℂ → B} {b : B}
    (hf : ∀ g, inUJ ε g → f g = σ g * b) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    RdV X f 1 = RdV X σ 1 * b := by
  rw [← ((hasDerivAt_rdV hs hX).mul_const b).deriv, RdV]
  congr 1
  funext t
  rw [Matrix.one_mul]
  exact hf _ (exp_indefinite_unitary_holds n ε X hX t)

theorem eabV_mul (hs : SmoothOnGV ε σ) (hmul : ∀ a, inUJ ε a → ∀ b, inUJ ε b → σ (a * b) = σ a * σ b)
    (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    EabV ε a b σ g = σ g * EabV ε a b σ 1 := by
  obtain ⟨h1, h2, -⟩ := cpartMem n ε (Matrix.single a b 1)
  simp only [EabV, EcV]
  rw [rdV_mul hs hmul h1 hg, rdV_mul hs hmul h2 hg, mul_add, mul_smul_comm]

theorem eabV_eabV (hs : SmoothOnGV ε σ) (hmul : ∀ a, inUJ ε a → ∀ b, inUJ ε b → σ (a * b) = σ a * σ b)
    (a b c d : Fin n) :
    EabV ε a b (EabV ε c d σ) 1 = EabV ε a b σ 1 * EabV ε c d σ 1 := by
  obtain ⟨h1, h2, -⟩ := cpartMem n ε (Matrix.single a b 1)
  have h := fun g hg => eabV_mul hs hmul c d (g := g) hg
  show RdV _ _ 1 + Complex.I • RdV _ _ 1 = (RdV _ σ 1 + Complex.I • RdV _ σ 1) * _
  rw [rdV_one_of_eq hs h h1, rdV_one_of_eq hs h h2, add_mul, smul_mul_assoc]

theorem glRel_eabV (hs : SmoothOnGV ε σ) (hmul : ∀ a, inUJ ε a → ∀ b, inUJ ε b → σ (a * b) = σ a * σ b) :
    GlRel fun a b => EabV ε a b σ 1 := by
  intro a b c d
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  have := eabGlV n ε B σ a b c d 1 hs hone
  rwa [eabV_eabV hs hmul, eabV_eabV hs hmul] at this

theorem rdV_eq_sum (hs : SmoothOnGV ε σ) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z) :
    RdV Z σ 1 = ∑ a, ∑ b, Z a b • EabV ε a b σ 1 := by
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  obtain ⟨h1, h2⟩ := (cpartMem n ε Z).2.2.2 hZ
  rw [← ecSumV n ε B σ Z 1 hs hone, EcV, h1, h2]
  simp [RdV]

end Deriv

section Unit

variable {n : ℕ} {ε : Fin n → Bool} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {π : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)}

theorem hasDerivAt_apply (hs : SmoothOnGV ε π) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : W) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v) (RdV X π 1 v) 0 :=
  ((ContinuousLinearMap.apply ℂ W v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_rdV hs hX)

theorem rdV_skew (hs : SmoothOnGV ε π) (h1 : π 1 = 1) (hiso : ∀ g, inUJ ε g → ∀ v, ‖π g v‖ = ‖v‖)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (x y : W) :
    ⟪RdV X π 1 x, y⟫_ℂ = -⟪x, RdV X π 1 y⟫_ℂ := by
  have h := (hasDerivAt_apply hs hX x).inner ℂ (hasDerivAt_apply hs hX y)
  have hc : (fun t : ℝ => ⟪π (NormedSpace.exp ((t : ℂ) • X)) x, π (NormedSpace.exp ((t : ℂ) • X)) y⟫_ℂ)
      = fun _ => ⟪x, y⟫_ℂ := by
    funext t
    exact LinearIsometry.inner_map_map
      ⟨(π (NormedSpace.exp ((t : ℂ) • X))).toLinearMap, hiso _ (exp_indefinite_unitary_holds n ε X hX t)⟩ x y
  rw [hc] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, h1, ContinuousLinearMap.one_apply] at h0
  linear_combination h0

end Unit

theorem Jm_allPos (k : ℕ) : Jm (PI.UpqRep.allPos k) = 1 := by
  simp [Jm, PI.UpqRep.allPos]

theorem exists_derived_action : ∀ (k : ℕ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)),
    PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) π →
    ∃ E : Fin k → Fin k → Module.End ℂ W, Formalism.REAL.GlRel E ∧ Formalism.REAL.IsUnitary (PI.UpqRep.allPos k) E ∧
      ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
        HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0 := by
  intro k W _ _ _ π ⟨⟨h1, hmul⟩, hiso, hcont⟩
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hmul' : ∀ a, inUJ (PI.UpqRep.allPos k) a → ∀ b, inUJ (PI.UpqRep.allPos k) b → π (a * b) = π a * π b := hmul
  have hs : SmoothOnGV (PI.UpqRep.allPos k) π :=
    smooth_of_continuous h1 hmul' (continuousOn_clm_apply.2 hcont)
  have hone : inUJ (PI.UpqRep.allPos k) (1 : Matrix (Fin k) (Fin k) ℂ) := by simp [inUJ]
  refine ⟨fun a b => (EabV (PI.UpqRep.allPos k) a b π 1).toLinearMap, ?_, ?_, ?_⟩
  · intro a b c d
    have := congrArg ContinuousLinearMap.toLinearMap (glRel_eabV hs hmul' a b c d)
    split_ifs at this ⊢ <;> exact this
  · intro a b x y
    obtain ⟨h1', h2', -⟩ := cpartMem k (PI.UpqRep.allPos k) (Matrix.single a b 1)
    have e1 : cpart1 (PI.UpqRep.allPos k) (Matrix.single b a 1) =
        ((-1 : ℝ) : ℂ) • cpart1 (PI.UpqRep.allPos k) (Matrix.single a b (1 : ℂ)) := by
      simp only [cpart1, Jm_allPos, Matrix.one_mul, Matrix.mul_one, conjTranspose_single, star_one]
      rw [← neg_sub, smul_neg]
      push_cast
      rw [neg_one_smul]
    have e2 : cpart2 (PI.UpqRep.allPos k) (Matrix.single b a 1) =
        cpart2 (PI.UpqRep.allPos k) (Matrix.single a b (1 : ℂ)) := by
      simp only [cpart2, Jm_allPos, Matrix.one_mul, Matrix.mul_one, conjTranspose_single, star_one, add_comm]
    have e3 := (rdLinV k _ _ π π _ _ (-1) 0 1 hs hs h1' h1' hone).2.1
    simp only [EabV, EcV, e1, e2, e3, sgn, PI.UpqRep.allPos, if_true, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right]
    have s1 := rdV_skew hs h1 hiso h1' x y
    have s2 := rdV_skew hs h1 hiso h2' x y
    rw [s1, s2]
    simp
  · intro Z hZ v
    have hG : inG (PI.UpqRep.allPos k) Z := by simp [inG, Jm_allPos, hZ]
    have := hasDerivAt_apply hs hG v
    rw [rdV_eq_sum hs hG] at this
    simpa using this

end GlobalTheory.UnitaryDerived

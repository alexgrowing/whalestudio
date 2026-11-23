import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PosSemidefSubMulConjTranspose
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaEisensteinConvergeBoundedStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EisAutomorphyLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DerivDerivConstMulCexpBilinearAtZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfA
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.EisHeat

section Lines

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]

omit [FiniteDimensional ℂ X] in

theorem deriv_line {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : X → V} {p : X}
    (hf : DifferentiableAt ℂ f p) (v : X) :
    HasDerivAt (fun s : ℂ => f (p + s • v)) (fderiv ℂ f p v) 0 := by
  have h : HasDerivAt (fun s : ℂ => p + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add p
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 h (by simp)

theorem deriv_two {f : X → ℂ} {U : Set X} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {p : X}
    (hp : p ∈ U) (v w : X) :
    deriv (fun s : ℂ => deriv (fun t : ℂ => f (p + s • v + t • w)) 0) 0 =
      fderiv ℂ (fderiv ℂ f) p v w := by
  have h1 : DifferentiableAt ℂ (fderiv ℂ f) p :=
    (SCV.analyticAt_of_differentiableOn hf (hU.mem_nhds hp)).fderiv.differentiableAt
  have h2 := (deriv_line h1 v).clm_apply (hasDerivAt_const (0 : ℂ) w)
  have h3 : ∀ᶠ s : ℂ in 𝓝 0, p + s • v ∈ U := by
    have : Continuous fun s : ℂ => p + s • v := by fun_prop
    exact this.continuousAt.eventually_mem (by simpa using hU.mem_nhds hp)
  have h4 : (fun s : ℂ => deriv (fun t : ℂ => f (p + s • v + t • w)) 0) =ᶠ[𝓝 0]
      fun s => fderiv ℂ f (p + s • v) w :=
    h3.mono fun s hs => (deriv_line (hf.differentiableAt (hU.mem_nhds hs)) w).deriv
  rw [h4.deriv_eq, h2.deriv]
  simp

end Lines

variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

theorem imH_isHermitian (Z : Matrix (Fin N) (Fin N) ℂ) : (imH Z).IsHermitian := by
  unfold imH IsHermitian
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose, ← neg_sub Z, smul_neg,
    ← neg_smul]
  congr 1
  simp

theorem eventually_posDef (δ : ℝ) {p : CF Ψ N N × CF Ψ n N × CF Ψ n N}
    (hp : ∀ τ, (imH (p.1 τ) - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef) :
    ∀ᶠ q : CF Ψ N N × CF Ψ n N × CF Ψ n N in 𝓝 p,
      ∀ τ, (imH (q.1 τ) - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef := by
  refine Filter.eventually_all.2 fun τ => ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.posDef_eventually
    (fun q : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
      imH (q.1 τ) - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) (fun i j => ?_) (fun q => ?_) p (hp τ)
  · change Continuous fun q : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
      (2 * I)⁻¹ * (q.1 τ i j - star (q.1 τ j i)) - ((δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) i j
    fun_prop
  · refine (imH_isHermitian _).sub ?_
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one]
    simp

theorem isOpen_dom : IsOpen {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N} := by
  refine isOpen_iff_mem_nhds.2 fun p hp => ?_
  have := eventually_posDef Ψ 0 (p := p) (fun τ => by simpa using hp τ)
  filter_upwards [this] with q hq τ
  simpa using hq τ

open Classical in

noncomputable def dir {m : ℕ} (τ : Ψ) (k : Fin m) (a : Fin N) : CF Ψ m N :=
  fun σ i j => if σ = τ ∧ k = i ∧ a = j then 1 else 0

open Classical in

theorem heat_iff {D : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ}
    (hD : DifferentiableOn ℂ (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => D p.1 p.2.1 p.2.2)
      {p | (p.1 : CM Ψ N N) ∈ Hn Ψ N}) :
    IsHeat Ψ D ↔ ∀ Z z z', (Z : CM Ψ N N) ∈ Hn Ψ N → ∀ (τ : Ψ) (a b : Fin N),
      2 * Real.pi * I * fderiv ℂ (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => D p.1 p.2.1 p.2.2)
        (Z, z, z') (dir Ψ τ a b, 0, 0) =
      ∑ k, fderiv ℂ (fderiv ℂ (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => D p.1 p.2.1 p.2.2))
        (Z, z, z') (0, dir Ψ τ k a, 0) (0, 0, dir Ψ τ k b) := by
  have key : ∀ {m : ℕ} (x : CF Ψ m N) (τ : Ψ) (k : Fin m) (a : Fin N) (s : ℂ),
      x + s • dir Ψ τ k a =
        (fun σ => Matrix.of (x σ) + if σ = τ then Matrix.single k a s else 0 : CM Ψ m N) := by
    intro m x τ k a s
    funext σ i j
    change x σ i j + s * (if σ = τ ∧ k = i ∧ a = j then 1 else 0) =
      x σ i j + (if σ = τ then Matrix.single k a s else 0 : Matrix (Fin m) (Fin N) ℂ) i j
    by_cases h : σ = τ
    · simp [h, Matrix.single]
    · simp [h]
  have main : ∀ (Z : CF Ψ N N) (z z' : CF Ψ n N), (Z : CM Ψ N N) ∈ Hn Ψ N →
      ∀ (τ : Ψ) (a b : Fin N),
      (2 * Real.pi * I * fderiv ℂ (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => D p.1 p.2.1 p.2.2)
        (Z, z, z') (dir Ψ τ a b, 0, 0) =
      ∑ k, fderiv ℂ (fderiv ℂ (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => D p.1 p.2.1 p.2.2))
        (Z, z, z') (0, dir Ψ τ k a, 0) (0, 0, dir Ψ τ k b)) ↔
      2 * Real.pi * I * deriv (fun s : ℂ =>
        D (fun σ => Matrix.of (Z σ) + if σ = τ then Matrix.single a b s else 0) z z') 0 =
      ∑ k, deriv (fun s : ℂ => deriv (fun t : ℂ =>
        D Z (fun σ => Matrix.of (z σ) + if σ = τ then Matrix.single k a s else 0)
          (fun σ => Matrix.of (z' σ) + if σ = τ then Matrix.single k b t else 0)) 0) 0 := by
    intro Z z z' hZ τ a b
    have hp : ((Z, z, z') : CF Ψ N N × CF Ψ n N × CF Ψ n N) ∈
      {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N} := hZ
    rw [← (deriv_line (hD.differentiableAt ((isOpen_dom Ψ).mem_nhds hp)) _).deriv]
    simp only [← deriv_two (isOpen_dom Ψ) hD hp]
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero]
    simp only [key]
  exact ⟨fun h Z z z' hZ τ a b => (main Z z z' hZ τ a b).2 (h.2 Z hZ z z' τ a b),
    fun h => ⟨hD, fun Z hZ z z' τ a b => (main Z z z' hZ τ a b).1 (h Z z z' hZ τ a b)⟩⟩

theorem isHeat_tsum {ι : Type} {D : ι → CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ}
    (hD : ∀ i, IsHeat Ψ (D i))
    (hle : ∀ p : CF Ψ N N × CF Ψ n N × CF Ψ n N, (p.1 : CM Ψ N N) ∈ Hn Ψ N → ∃ t ∈ 𝓝 p,
      ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ q ∈ t, ‖D i q.1 q.2.1 q.2.2‖ ≤ u i) :
    IsHeat Ψ fun Z z z' => ∑' i, D i Z z z' := by
  have h0 := SCV.hasSumLocallyUniformlyOn_of_locally_normal
    (F := fun i (q : CF Ψ N N × CF Ψ n N × CF Ψ n N) => D i q.1 q.2.1 q.2.2)
    (U := {p | (p.1 : CM Ψ N N) ∈ Hn Ψ N}) hle
  have hd := SCV.differentiableOn_of_hasSumLocallyUniformlyOn (isOpen_dom Ψ) h0 fun i => (hD i).1
  have h1 := SCV.hasSumLocallyUniformlyOn_fderiv (isOpen_dom Ψ) h0 fun i => (hD i).1
  have h2 := SCV.hasSumLocallyUniformlyOn_fderiv (isOpen_dom Ψ) h1 fun i p hp =>
    (SCV.analyticAt_of_differentiableOn (hD i).1
      ((isOpen_dom Ψ).mem_nhds hp)).fderiv.differentiableAt.differentiableWithinAt
  refine (heat_iff Ψ hd).2 fun Z z z' hZ τ a b => ?_
  have hp : ((Z, z, z') : CF Ψ N N × CF Ψ n N × CF Ψ n N) ∈
    {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N} := hZ
  have s1 := fun v => (h1.hasSum hp).mapL (ContinuousLinearMap.apply ℂ ℂ v)
  have s2 := fun v w => ((h2.hasSum hp).mapL (ContinuousLinearMap.apply ℂ _ v)).mapL
    (ContinuousLinearMap.apply ℂ ℂ w)
  simp only [ContinuousLinearMap.apply_apply] at s1 s2
  refine ((s1 _).mul_left _).unique ?_
  simp only [fun i => (heat_iff Ψ (hD i).1).1 (hD i) Z z z' hZ τ a b]
  exact hasSum_sum fun k _ => s2 _ _

theorem isHeat_const_mul {D : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ} (hD : IsHeat Ψ D) (c : ℂ) :
    IsHeat Ψ fun Z z z' => c * D Z z z' := by
  refine ⟨hD.1.const_mul c, fun Z hZ z z' τ a b => ?_⟩
  simp only [deriv_const_mul_field', deriv_const_mul_field]
  rw [← Finset.mul_sum, ← hD.2 Z hZ z z' τ a b]
  ring

variable [NumberField E] [IsCMField E]

theorem hFac_inv_bound (n N : ℕ) {δ : ℝ} (hδ : 0 < δ) (B : ℝ) :
    ∃ K : ℝ, ∀ γ ∈ UU E N, ∀ Z ∈ Hn Ψ N, Z ∈ HnGe Ψ N δ → ∀ z z' : CM Ψ n N,
      (∀ τ a b, ‖Z τ a b‖ ≤ B) → (∀ τ a b, ‖z τ a b‖ ≤ B) → (∀ τ a b, ‖z' τ a b‖ ≤ B) →
      ‖(hFac Ψ γ Z z z')⁻¹‖ ≤
        K * ‖(hFac Ψ γ (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ)) (0 : CM Ψ n N) 0)⁻¹‖ := by
  obtain ⟨c, hc, hcmp⟩ := norm_det_denom_compare N δ (B + B) hδ
  refine ⟨∏ _τ : Ψ, (c ^ n)⁻¹ *
    Real.exp (‖2 * (π : ℂ) * I‖ * ∑ _k : Fin n, ∑ _a : Fin N, B * ∑ _b : Fin N, δ⁻¹ * B),
    fun γ hγ Z hZ hZ' z z' hB hz hz' => ?_⟩
  rw [EisTrans.hFac_zero, hFac, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib, norm_prod,
    norm_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => ?_
  have hr := (HermComp.row_rel _ (HAct.map_mem τ.1 hγ)).2
  have hd := (((unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ).1 τ).1
  have hd0 := (((unitary_act_halfSpace E Ψ N γ hγ).2 _ (Base.I_mem_Hn Ψ)).1 τ).1
  rw [mul_inv, norm_mul, mul_right_comm (c ^ n)⁻¹]
  refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
  · unfold hDen at hd hd0 ⊢
    change γ.toBlocks₂₂.map τ.1 * (γ.toBlocks₂₁.map τ.1)ᴴ =
      γ.toBlocks₂₁.map τ.1 * (γ.toBlocks₂₂.map τ.1)ᴴ at hr
    generalize γ.toBlocks₂₁.map τ.1 = C at *
    generalize γ.toBlocks₂₂.map τ.1 = D at *
    have h1 : (C * Dᴴ).IsHermitian := by
      unfold IsHermitian
      rw [conjTranspose_mul, conjTranspose_conjTranspose, hr]
    have h2 : (C * Cᴴ + D * Dᴴ).PosDef := by
      have e : C * Cᴴ + D * Dᴴ = (C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D) *
          (C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D)ᴴ := by
        simp only [Matrix.mul_smul, Matrix.mul_one, conjTranspose_add, conjTranspose_smul,
          Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, hr, Complex.star_def, Complex.conj_I,
          smul_add, smul_smul, neg_smul, Matrix.mul_neg, smul_neg, I_mul_I, neg_neg, one_smul]
        abel
      rw [e]
      exact PosDef.mul_conjTranspose_self _
        (Matrix.vecMul_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 (Ne.isUnit hd0)))
    have h3 := (hcmp C D (Z τ) h1 h2 (hZ' τ) fun a b => (norm_add_le _ _).trans
      (add_le_add (hB τ a b) (by simpa using hB τ b a))).1
    rw [norm_inv, norm_inv, norm_pow, norm_pow, ← mul_inv, ← mul_pow]
    have h4 := norm_pos_iff.2 hd0
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h3 n)
  · rw [← Complex.exp_neg]
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
    rw [norm_neg, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hb := EisTrans.entry_bound hδ hr hd (hZ' τ)
    refine norm_sum_le_of_le _ fun k _ => norm_sum_le_of_le _ fun a _ => ?_
    rw [norm_mul]
    refine mul_le_mul (hz' τ k a) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hz' τ k a))
    rw [Matrix.mulVec, dotProduct]
    refine norm_sum_le_of_le _ fun b _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hb a b) (hz τ k b) (norm_nonneg _) (by positivity)

end GlobalTheory.SW.EisHeat

open GlobalTheory.SW.EisHeat in

theorem GlobalTheory.SW.isHeat_eis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → IsHeat Ψ (eis Ψ φ) := by
  rintro E _ _ _ Ψ hΨ n N hn hN φ ⟨R, hR, hφ⟩
  refine isHeat_tsum Ψ (D := fun U : Lag E N => eisTerm Ψ U.2.choose φ)
    (fun U => isHeat_const_mul Ψ (isHeat_hFac_inv E Ψ n N _ U.2.choose_spec.1) _) fun p hp => ?_
  obtain ⟨B, hB⟩ := (GlobalTheory.T.schwartzBruhatInnerProduct_self_nonneg_bounds E _ _ R φ hR hφ).2.2.2.2.1
  obtain ⟨δ₀, hδ₀, hI⟩ := EisTrans.exists_mem_HnGe Ψ (Base.I_mem_Hn (N := N) Ψ)
  obtain ⟨C, hC⟩ := GlobalTheory.T.hermitianTheta_eisenstein_converge_bounded E Ψ hΨ n N hn hN R δ₀ hR hδ₀
  have hs := (hC φ hφ B hB _ hI).1
  obtain ⟨δ, hδ, hp'⟩ := EisTrans.exists_mem_HnGe Ψ hp
  have h1 := eventually_posDef Ψ (δ / 2) (p := p) fun τ => by
    have h : (((δ / 2 : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef :=
      PosDef.one.smul (by exact_mod_cast half_pos hδ)
    convert PosDef.posSemidef_add (hp' τ) h using 1
    rw [sub_add, ← sub_smul]
    congr 2
    push_cast
    ring
  obtain ⟨K, hK⟩ := hFac_inv_bound Ψ n N (half_pos hδ) (‖p‖ + 1)
  have h2 : ∀ᶠ q : CF Ψ N N × CF Ψ n N × CF Ψ n N in 𝓝 p, ‖q‖ < ‖p‖ + 1 :=
    continuous_norm.continuousAt.eventually_lt_const (lt_add_one _)
  refine ⟨_, (h1.and h2).and ((isOpen_dom Ψ).mem_nhds hp), _, hs.mul_left K, fun U q hq => ?_⟩
  obtain ⟨⟨q1, q2⟩, q3⟩ := hq
  have e : ∀ {m : ℕ} (x : CF Ψ m N), ‖x‖ ≤ ‖q‖ → ∀ τ a b, ‖x τ a b‖ ≤ ‖p‖ + 1 :=
    fun x hx τ a b => (norm_le_pi_norm _ b).trans <| (norm_le_pi_norm _ a).trans <|
      (norm_le_pi_norm x τ).trans <| hx.trans q2.le
  simp only [eisTerm]
  rw [norm_mul, norm_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hK _ U.2.choose_spec.1 _ q3 (fun τ => (q1 τ).posSemidef) _ _
    (e _ (norm_fst_le q)) (e _ ((norm_fst_le q.2).trans (norm_snd_le q)))
    (e _ ((norm_snd_le q.2).trans (norm_snd_le q)))) (norm_nonneg _)

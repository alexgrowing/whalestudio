import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier

open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory

open Complex Matrix NumberField Filter Topology in

theorem _root_.GlobalTheory.entire_eq_zero_of_mul_continuous_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f t : E → ℂ} (hf : Differentiable ℂ f) (ht : Continuous t) (ht0 : t ≠ 0)
    (h : ∀ z, f z * t z = 0) (z : E) : f z = 0 := by
  obtain ⟨w, hw⟩ : ∃ w, t w ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact ht0 (funext hne)
  have hU : ∀ᶠ y in 𝓝 w, f y = 0 := by
    filter_upwards [ht.continuousAt.eventually_ne hw] with y hy
    exact (mul_eq_zero.mp (h y)).resolve_right hy
  have hc : Continuous fun s : ℂ => w + s • (z - w) := by fun_prop
  have hlim : Tendsto (fun s : ℂ => w + s • (z - w)) (𝓝 0) (𝓝 w) := by
    simpa using hc.tendsto 0
  have hd : Differentiable ℂ fun s : ℂ => f (w + s • (z - w)) :=
    hf.comp ((differentiable_const _).add (differentiable_id.smul_const _))
  have h0 : (fun s : ℂ => f (w + s • (z - w))) =ᶠ[𝓝 0] 0 := by
    filter_upwards [hlim.eventually hU] with s hs
    simpa using hs
  have han : AnalyticOnNhd ℂ (fun s : ℂ => f (w + s • (z - w))) Set.univ :=
    fun s _ => hd.analyticAt s
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ 0) h0 (Set.mem_univ 1)
  simpa using this

open Complex Matrix NumberField Filter Topology in
private theorem span_real_period_lattice_full {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g)) :
    Submodule.span ℝ (Set.range fun p : (Fin g → ℤ) × (Fin g → ℤ) =>
      τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec p.1 + _root_.ReciprocityTheory.PTheta.ofIntVec p.2) = ⊤ := by
  unfold _root_.ReciprocityTheory.PTheta.SiegelH at hτ
  obtain ⟨-, hY⟩ := hτ
  set Y : Matrix (Fin g) (Fin g) ℝ := τ.map Complex.im with hYdef
  have hYu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hY.det_pos.ne'
  rw [eq_top_iff]
  intro v _
  set a : Fin g → ℝ := Y⁻¹ *ᵥ fun i => (v i).im
  set u : Fin g → ℝ := (fun i => (v i).re) - (τ.map Complex.re) *ᵥ a
  have hYa : Y *ᵥ a = fun i => (v i).im := by
    simp only [a, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hYu, Matrix.one_mulVec]
  have hv : v = ∑ j, a j • (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec (Pi.single j 1) + _root_.ReciprocityTheory.PTheta.ofIntVec 0)
      + ∑ j, u j • (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec 0 + _root_.ReciprocityTheory.PTheta.ofIntVec (Pi.single j 1)) := by
    funext i
    have hi := congrFun hYa i
    simp only [Matrix.mulVec, dotProduct, Y, Matrix.map_apply] at hi
    apply Complex.ext
    · simp [Finset.sum_apply, Matrix.mulVec, dotProduct, _root_.ReciprocityTheory.PTheta.ofIntVec, Pi.single_apply, u]
      rw [Finset.sum_congr rfl fun x _ => mul_comm (a x) _]
      ring
    · simp [Finset.sum_apply, Matrix.mulVec, dotProduct, _root_.ReciprocityTheory.PTheta.ofIntVec, Pi.single_apply, u]
      rw [← hi]
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [hv]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
  · exact Submodule.subset_span ⟨(Pi.single j 1, 0), rfl⟩
  · exact Submodule.subset_span ⟨(0, Pi.single j 1), rfl⟩

open Complex Matrix NumberField Filter Topology in

theorem _root_.GlobalTheory.two_dvd_of_entire_sign_periodic {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g)) {σ : (Fin g → ℂ) → ℂ} (hσ : Differentiable ℂ σ) (h0 : σ 0 ≠ 0)
    {N : (Fin g → ℤ) → (Fin g → ℤ) → ℤ}
    (h : ∀ m m' z, σ (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m + _root_.ReciprocityTheory.PTheta.ofIntVec m') = _root_.ReciprocityTheory.PTheta.eC ((N m m' : ℂ) / 2) * σ z)
    (m m' : Fin g → ℤ) : 2 ∣ N m m' := by
  have hsq : ∀ z w, σ z ^ 2 = σ w ^ 2 :=
    _root_.GlobalTheory.entire_apply_eq_of_periodic_of_span_real (F := fun z => σ z ^ 2) (hσ.pow 2)
      (span_real_period_lattice_full hτ) (by
        rintro x _ ⟨⟨n, n'⟩, rfl⟩
        simp only
        rw [← add_assoc, h, mul_pow, _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.eC_pow,
          show ((2 : ℕ) : ℂ) * ((N n n' : ℂ) / 2) = ((N n n' : ℤ) : ℂ) by push_cast; ring,
          _root_.ReciprocityTheory.PTheta.eC_int, one_mul])
  have hconst : ∀ z, σ z - σ 0 = 0 := by
    refine _root_.GlobalTheory.entire_eq_zero_of_mul_continuous_eq_zero (t := fun z => σ z + σ 0)
      (hσ.sub_const _) (hσ.continuous.add continuous_const) ?_ ?_
    · intro ht
      have := congrFun ht 0
      simp only [Pi.zero_apply] at this
      exact h0 (by linear_combination this / 2)
    · intro z
      have := hsq z 0
      linear_combination this
  have he : _root_.ReciprocityTheory.PTheta.eC ((N m m' : ℂ) / 2) = 1 := by
    have h1 := h m m' 0
    rw [zero_add, sub_eq_zero.mp (hconst _)] at h1
    have h2 : (_root_.ReciprocityTheory.PTheta.eC ((N m m' : ℂ) / 2) - 1) * σ 0 = 0 := by linear_combination -h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right h0)
  have hz := _root_.GlobalTheory.intCast_zmod_eq_of_eC_eq (N := 2) two_pos (p := N m m') (q := 0)
    (by rw [show ((N m m' : ℤ) : ℂ) / ((2 : ℕ) : ℂ) = (N m m' : ℂ) / 2 by norm_num, he]
        simp [_root_.ReciprocityTheory.PTheta.eC_zero])
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (by simpa using hz)

section Transform

variable {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} {τ : Matrix (Fin g) (Fin g) ℂ}

end Transform

open Complex Matrix NumberField Filter Topology in
private theorem symplectic_block_combination_eq {g : ℕ} (A B C D τ : Matrix (Fin g) (Fin g) ℂ)
    (r2 : Cᵀ * B - Aᵀ * D = -1) (r4 : Dᵀ * B - Bᵀ * D = 0) :
    (τ * Aᵀ + Bᵀ) * D - (τ * Cᵀ + Dᵀ) * B = τ := by
  have e : (τ * Aᵀ + Bᵀ) * D - (τ * Cᵀ + Dᵀ) * B =
      τ * (-(Cᵀ * B - Aᵀ * D)) - (Dᵀ * B - Bᵀ * D) := by
    simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_neg]; abel
  rw [e, r2, r4, neg_neg, Matrix.mul_one, sub_zero]

open Complex Matrix NumberField Filter Topology in
private theorem mulVec_lattice_translate_eq {g : ℕ} (A B C D τ τ' Mi : Matrix (Fin g) (Fin g) ℂ)
    (F1 : A - τ' * C = Mi) (F2 : Mi * τ = τ' * D - B) (z u v : Fin g → ℂ) :
    Mi *ᵥ (z + τ *ᵥ u + v) = Mi *ᵥ z + τ' *ᵥ (D *ᵥ u - C *ᵥ v) + (A *ᵥ v - B *ᵥ u) := by
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec, F2, ← F1]
  simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  abel

open Complex Matrix NumberField Filter Topology in
private theorem quadratic_lattice_translate_eq {g : ℕ} (C τ τ' M : Matrix (Fin g) (Fin g) ℂ) (hM : IsUnit M.det)
    (hτ : τᵀ = τ) (hS : (M⁻¹ * C)ᵀ = M⁻¹ * C) (z u v q q' : Fin g → ℂ)
    (hC : C *ᵥ (τ *ᵥ u + v) = M *ᵥ u - q)
    (hL : M⁻¹ᵀ *ᵥ (τ *ᵥ u + v) = τ' *ᵥ q + q') :
    (z + τ *ᵥ u + v) ⬝ᵥ (M⁻¹ * C) *ᵥ (z + τ *ᵥ u + v) = z ⬝ᵥ (M⁻¹ * C) *ᵥ z
      + 2 * (u ⬝ᵥ z + u ⬝ᵥ τ *ᵥ u / 2) - 2 * (q ⬝ᵥ M⁻¹ᵀ *ᵥ z + q ⬝ᵥ τ' *ᵥ q / 2)
      + (u ⬝ᵥ v - q ⬝ᵥ q') := by
  set l := τ *ᵥ u + v with hl
  have hSl : (M⁻¹ * C) *ᵥ l = u - M⁻¹ *ᵥ q := by
    rw [← Matrix.mulVec_mulVec, hC, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]
  have hsymm : ∀ a b : Fin g → ℂ, a ⬝ᵥ (M⁻¹ * C) *ᵥ b = b ⬝ᵥ (M⁻¹ * C) *ᵥ a := by
    intro a b
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS, dotProduct_comm]
  have htr : ∀ a b : Fin g → ℂ, a ⬝ᵥ M⁻¹ *ᵥ b = (M⁻¹ᵀ *ᵥ a) ⬝ᵥ b := by
    intro a b
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have hτu : l ⬝ᵥ u = u ⬝ᵥ τ *ᵥ u + u ⬝ᵥ v := by
    rw [hl, add_dotProduct, dotProduct_comm v u, Matrix.dotProduct_mulVec, dotProduct_comm,
      ← Matrix.mulVec_transpose, hτ]
    rw [dotProduct_comm]
  have e1 : ∀ a b : Fin g → ℂ, (a + b) ⬝ᵥ (M⁻¹ * C) *ᵥ (a + b) =
      a ⬝ᵥ (M⁻¹ * C) *ᵥ a + 2 * (b ⬝ᵥ (M⁻¹ * C) *ᵥ a) + b ⬝ᵥ (M⁻¹ * C) *ᵥ b := by
    intro a b
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hsymm a b]; ring
  rw [add_assoc z, ← hl]
  clear_value l
  rw [e1 z l, hsymm l z, hSl, dotProduct_sub, dotProduct_sub, htr, htr, hL, hτu, add_dotProduct,
    dotProduct_comm z u, dotProduct_comm (M⁻¹ᵀ *ᵥ z) q, dotProduct_comm (τ' *ᵥ q) q, dotProduct_comm q' q]
  ring

open Complex Matrix NumberField Filter Topology in

theorem _root_.GlobalTheory.halfChar_fixed_of_theta_transform_unit :
    ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), γ ∈ Matrix.symplecticGroup (Fin g) ℤ → (∀ i j, (8 : ℤ) ∣ γ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ γ (Sum.inr i) (Sum.inl j)) → ∀ (c : ℂ) (n n' : Fin g → ℤ), c ≠ 0 → (∀ τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g), ∀ z : Fin g → ℂ, _root_.ReciprocityTheory.PTheta.theta (_root_.ReciprocityTheory.ChartRestriction.G.Key.halfVec 0) (_root_.ReciprocityTheory.ChartRestriction.G.Key.halfVec 0) (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.zAct γ τ z) (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct γ τ) ^ 2 = c * (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut γ τ).det * _root_.ReciprocityTheory.PTheta.eC (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.expArg γ τ z) * _root_.ReciprocityTheory.PTheta.theta (_root_.ReciprocityTheory.ChartRestriction.G.Key.halfVec 0) (_root_.ReciprocityTheory.ChartRestriction.G.Key.halfVec 0) z τ ^ 2) → ∀ τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g), ∀ ρ : (Fin g → ℂ) → ℂ, Differentiable ℂ ρ → (∀ z, ρ z ≠ 0) → (∀ z, _root_.ReciprocityTheory.PTheta.theta (_root_.ReciprocityTheory.ChartRestriction.G.Key.halfVec n) (_root_.ReciprocityTheory.ChartRestriction.G.Key.halfVec n') (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.zAct γ τ z) (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct γ τ) = ρ z * _root_.ReciprocityTheory.PTheta.theta (_root_.ReciprocityTheory.ChartRestriction.G.Key.halfVec n) (_root_.ReciprocityTheory.ChartRestriction.G.Key.halfVec n') z τ) → (∀ i, (2 : ℤ) ∣ (γ.toBlocks₁₁ᵀ *ᵥ n) i - n i) ∧ (∀ i, (2 : ℤ) ∣ (γ.toBlocks₂₂ᵀ *ᵥ n') i - n' i) := by

  intro g γ hγ h8 c n n' hc _hθ τ hτ ρ hρ hρ0 hrel
  obtain ⟨r1, r2, r3, r4⟩ := _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.sp_rel hγ
  set A := (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat γ).toBlocks₁₁ with hA
  set B := (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat γ).toBlocks₁₂ with hB
  set C := (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat γ).toBlocks₂₁ with hC
  set D := (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat γ).toBlocks₂₂ with hD
  have hτs : τ.IsSymm := hτ.1
  have hM : IsUnit (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut γ τ).det := _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut_isUnit hγ hτ
  have hτ'mem : _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct γ τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) := _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct_mem hγ hτ
  have hτ's : (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct γ τ).IsSymm := _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct_isSymm hγ hτs hM
  have F1 : A - _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct γ τ * C = (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut γ τ)⁻¹ᵀ := _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.sp_A hγ hτs hM
  have hMeq : _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut γ τ = C * τ + D := _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut_eq γ τ
  have hτ'eq : _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct γ τ = (A * τ + B) * (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut γ τ)⁻¹ := by rw [_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct_eq, _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.nAut_eq]
  set M := _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut γ τ with hMdef
  set τ' := _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct γ τ with hτ'def
  have hMt : IsUnit Mᵀ.det := by rwa [Matrix.det_transpose]
  have F2 : M⁻¹ᵀ * τ = τ' * D - B := by
    have h1 : τ' * M = A * τ + B := by
      rw [hτ'eq, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hM, Matrix.mul_one]
    have h2 : Mᵀ * τ' = (A * τ + B)ᵀ := by
      rw [← h1, Matrix.transpose_mul, hτ's.eq]
    have key : Mᵀ * (τ' * D - B) = τ := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, h2, hMeq]
      simp only [Matrix.transpose_add, Matrix.transpose_mul, hτs.eq]
      exact symplectic_block_combination_eq A B C D τ r2 r4
    rw [← key, ← Matrix.mul_assoc, Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_mul _ hMt,
      Matrix.one_mul]
  have hMi : M⁻¹ = Aᵀ - Cᵀ * τ' := by
    rw [← Matrix.transpose_transpose M⁻¹, ← F1, Matrix.transpose_sub, Matrix.transpose_mul,
      hτ's.eq]
  have hS : (M⁻¹ * C)ᵀ = M⁻¹ * C := by
    rw [Matrix.transpose_mul, ← F1, hMi]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [sub_eq_zero.mp r1]
  have hAi : A = γ.toBlocks₁₁.map (↑) := by ext i j; rfl
  have hBi : B = γ.toBlocks₁₂.map (↑) := by ext i j; rfl
  have hCi : C = γ.toBlocks₂₁.map (↑) := by ext i j; rfl
  have hDi : D = γ.toBlocks₂₂.map (↑) := by ext i j; rfl
  have hsub : ∀ u v : Fin g → ℤ, _root_.ReciprocityTheory.PTheta.ofIntVec (u - v) = _root_.ReciprocityTheory.PTheta.ofIntVec u - _root_.ReciprocityTheory.PTheta.ofIntVec v := by
    intro u v; funext i; simp [_root_.ReciprocityTheory.PTheta.ofIntVec]

  have transl : ∀ (a b : Fin g → ℝ) (σ₀ : Matrix (Fin g) (Fin g) ℂ), σ₀ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) →
      ∀ (u u' : Fin g → ℤ) (x : Fin g → ℂ),
      _root_.ReciprocityTheory.PTheta.theta a b (x + σ₀ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec u + _root_.ReciprocityTheory.PTheta.ofIntVec u') σ₀ =
        _root_.ReciprocityTheory.PTheta.eC (_root_.ReciprocityTheory.PTheta.ofRealVec a ⬝ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec u' - _root_.ReciprocityTheory.PTheta.ofRealVec b ⬝ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec u) *
          _root_.ReciprocityTheory.PTheta.eC (-(_root_.ReciprocityTheory.PTheta.ofIntVec u ⬝ᵥ σ₀ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec u / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec u ⬝ᵥ x)) * _root_.ReciprocityTheory.PTheta.theta a b x σ₀ := by
    intro a b σ₀ hσ₀ u u' x
    have hmem : (fun z => _root_.ReciprocityTheory.PTheta.theta a b z σ₀) ∈ _root_.GlobalTheory.thetaLevelChar a b 1 σ₀ := by
      rw [_root_.GlobalTheory.thetaLevelChar_one hσ₀]; exact Submodule.mem_span_singleton_self _
    have := (_root_.GlobalTheory.mem_thetaLevelChar.mp hmem).2 u u' x
    simpa only [Nat.cast_one, one_mul, neg_one_mul] using this

  have hzact : ∀ z, _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.zAct γ τ z = M⁻¹ᵀ *ᵥ z := fun z => rfl
  have hJ : ∀ z, _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.expArg γ τ z = z ⬝ᵥ (M⁻¹ * C) *ᵥ z := fun z => rfl
  have hdlin : ∀ (K : Matrix (Fin g) (Fin g) ℂ) (u : Fin g → ℂ),
      Differentiable ℂ fun z : Fin g → ℂ => u ⬝ᵥ K *ᵥ z := by
    intro K u; simp only [dotProduct, Matrix.mulVec]; fun_prop
  have hdJ : Differentiable ℂ fun z => _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.expArg γ τ z := by
    simp only [hJ, dotProduct, Matrix.mulVec]; fun_prop
  have hdE : ∀ f : (Fin g → ℂ) → ℂ, Differentiable ℂ f → Differentiable ℂ fun z => _root_.ReciprocityTheory.PTheta.eC (f z) := by
    intro f hf; unfold _root_.ReciprocityTheory.PTheta.eC; fun_prop
  set a := _root_.ReciprocityTheory.ChartRestriction.G.Key.halfVec n
  set b := _root_.ReciprocityTheory.ChartRestriction.G.Key.halfVec n'
  have hθne : (fun z => _root_.ReciprocityTheory.PTheta.theta a b z τ) ≠ 0 := _root_.GlobalTheory.theta_ne_zero hτ a b
  have hθc : Continuous fun z => _root_.ReciprocityTheory.PTheta.theta a b z τ := (_root_.GlobalTheory.differentiable_theta hτ a b).continuous
  let P : (Fin g → ℤ) → (Fin g → ℤ) → Fin g → ℤ := fun m m' => γ.toBlocks₂₂ *ᵥ m - γ.toBlocks₂₁ *ᵥ m'
  let P' : (Fin g → ℤ) → (Fin g → ℤ) → Fin g → ℤ := fun m m' => γ.toBlocks₁₁ *ᵥ m' - γ.toBlocks₁₂ *ᵥ m
  let N : (Fin g → ℤ) → (Fin g → ℤ) → ℤ := fun m m' => n ⬝ᵥ P' m m' - n' ⬝ᵥ P m m' - n ⬝ᵥ m' + n' ⬝ᵥ m
    - m ⬝ᵥ m' + P m m' ⬝ᵥ P' m m'
  let σ : (Fin g → ℂ) → ℂ := fun z => ρ z * _root_.ReciprocityTheory.PTheta.eC (-(_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.expArg γ τ z) / 2)
  have hdJ2 : Differentiable ℂ fun z => -(_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.expArg γ τ z) / 2 := by
    simp only [div_eq_mul_inv]; exact hdJ.neg.mul_const _
  have hσd : Differentiable ℂ σ := hρ.mul (hdE _ hdJ2)
  have hσ0 : σ 0 ≠ 0 := mul_ne_zero (hρ0 0) (_root_.GlobalTheory.eC_ne_zero _)
  have hper : ∀ m m' z, σ (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m + _root_.ReciprocityTheory.PTheta.ofIntVec m') = _root_.ReciprocityTheory.PTheta.eC ((N m m' : ℂ) / 2) * σ z := by
    intro m m' z
    have hp : _root_.ReciprocityTheory.PTheta.ofIntVec (P m m') = D *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m - C *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m' := by
      simp only [P, hsub, _root_.ReciprocityTheory.PTheta.ofIntVec_mulVec, hDi, hCi]
    have hp' : _root_.ReciprocityTheory.PTheta.ofIntVec (P' m m') = A *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m' - B *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m := by
      simp only [P', hsub, _root_.ReciprocityTheory.PTheta.ofIntVec_mulVec, hAi, hBi]
    have hL : ∀ x, M⁻¹ᵀ *ᵥ (x + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m + _root_.ReciprocityTheory.PTheta.ofIntVec m') =
        M⁻¹ᵀ *ᵥ x + τ' *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec (P m m') + _root_.ReciprocityTheory.PTheta.ofIntVec (P' m m') := by
      intro x; rw [hp, hp']; exact mulVec_lattice_translate_eq A B C D τ τ' M⁻¹ᵀ F1 F2 x _ _
    have hL0 : M⁻¹ᵀ *ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m + _root_.ReciprocityTheory.PTheta.ofIntVec m') = τ' *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec (P m m') + _root_.ReciprocityTheory.PTheta.ofIntVec (P' m m') := by
      simpa [add_assoc] using hL 0
    have hCl : C *ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m + _root_.ReciprocityTheory.PTheta.ofIntVec m') = M *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m - _root_.ReciprocityTheory.PTheta.ofIntVec (P m m') := by
      rw [hp, hMeq]; simp only [Matrix.mulVec_add, Matrix.add_mulVec, Matrix.mulVec_mulVec]; abel
    have hquad := quadratic_lattice_translate_eq C τ τ' M hM hτs.eq hS z _ _ _ _ hCl hL0
    rw [← hJ, ← hJ] at hquad

    have key : ∀ x, (ρ (x + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m + _root_.ReciprocityTheory.PTheta.ofIntVec m') *
          (_root_.ReciprocityTheory.PTheta.eC (_root_.ReciprocityTheory.PTheta.ofRealVec a ⬝ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m' - _root_.ReciprocityTheory.PTheta.ofRealVec b ⬝ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m) *
            _root_.ReciprocityTheory.PTheta.eC (-(_root_.ReciprocityTheory.PTheta.ofIntVec m ⬝ᵥ τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec m ⬝ᵥ x))) -
        (_root_.ReciprocityTheory.PTheta.eC (_root_.ReciprocityTheory.PTheta.ofRealVec a ⬝ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec (P' m m') - _root_.ReciprocityTheory.PTheta.ofRealVec b ⬝ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec (P m m')) *
            _root_.ReciprocityTheory.PTheta.eC (-(_root_.ReciprocityTheory.PTheta.ofIntVec (P m m') ⬝ᵥ τ' *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec (P m m') / 2 +
              _root_.ReciprocityTheory.PTheta.ofIntVec (P m m') ⬝ᵥ M⁻¹ᵀ *ᵥ x))) * ρ x) * _root_.ReciprocityTheory.PTheta.theta a b x τ = 0 := by
      intro x
      have h1 := hrel (x + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m + _root_.ReciprocityTheory.PTheta.ofIntVec m')
      rw [hzact, hL, transl a b τ' hτ'mem, ← hzact, hrel x, transl a b τ hτ] at h1
      rw [hzact] at h1
      linear_combination -h1
    have hdot : ∀ u : Fin g → ℂ, Differentiable ℂ fun x : Fin g → ℂ => u ⬝ᵥ x := by
      intro u; simp only [dotProduct]; fun_prop
    have hfd : Differentiable ℂ fun x => ρ (x + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m + _root_.ReciprocityTheory.PTheta.ofIntVec m') *
          (_root_.ReciprocityTheory.PTheta.eC (_root_.ReciprocityTheory.PTheta.ofRealVec a ⬝ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m' - _root_.ReciprocityTheory.PTheta.ofRealVec b ⬝ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m) *
            _root_.ReciprocityTheory.PTheta.eC (-(_root_.ReciprocityTheory.PTheta.ofIntVec m ⬝ᵥ τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec m ⬝ᵥ x))) -
        (_root_.ReciprocityTheory.PTheta.eC (_root_.ReciprocityTheory.PTheta.ofRealVec a ⬝ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec (P' m m') - _root_.ReciprocityTheory.PTheta.ofRealVec b ⬝ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec (P m m')) *
            _root_.ReciprocityTheory.PTheta.eC (-(_root_.ReciprocityTheory.PTheta.ofIntVec (P m m') ⬝ᵥ τ' *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec (P m m') / 2 +
              _root_.ReciprocityTheory.PTheta.ofIntVec (P m m') ⬝ᵥ M⁻¹ᵀ *ᵥ x))) * ρ x :=
      ((hρ.comp ((differentiable_id.add_const _).add_const _)).mul ((differentiable_const _).mul
        (hdE _ ((differentiable_const _).add (hdot _)).neg))).sub
        (((differentiable_const _).mul (hdE _ ((differentiable_const _).add (hdlin _ _)).neg)).mul hρ)
    have hρrel := sub_eq_zero.mp (_root_.GlobalTheory.entire_eq_zero_of_mul_continuous_eq_zero hfd hθc hθne key z)
    have hEne : _root_.ReciprocityTheory.PTheta.eC (_root_.ReciprocityTheory.PTheta.ofRealVec a ⬝ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m' - _root_.ReciprocityTheory.PTheta.ofRealVec b ⬝ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m) *
        _root_.ReciprocityTheory.PTheta.eC (-(_root_.ReciprocityTheory.PTheta.ofIntVec m ⬝ᵥ τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec m ⬝ᵥ z)) ≠ 0 :=
      mul_ne_zero (_root_.GlobalTheory.eC_ne_zero _) (_root_.GlobalTheory.eC_ne_zero _)
    apply mul_left_cancel₀ hEne
    have hexp : _root_.ReciprocityTheory.PTheta.eC (_root_.ReciprocityTheory.PTheta.ofRealVec a ⬝ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec (P' m m') - _root_.ReciprocityTheory.PTheta.ofRealVec b ⬝ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec (P m m')) *
          _root_.ReciprocityTheory.PTheta.eC (-(_root_.ReciprocityTheory.PTheta.ofIntVec (P m m') ⬝ᵥ τ' *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec (P m m') / 2 +
            _root_.ReciprocityTheory.PTheta.ofIntVec (P m m') ⬝ᵥ M⁻¹ᵀ *ᵥ z)) *
          _root_.ReciprocityTheory.PTheta.eC (-(_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.expArg γ τ (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m + _root_.ReciprocityTheory.PTheta.ofIntVec m')) / 2) =
        _root_.ReciprocityTheory.PTheta.eC (_root_.ReciprocityTheory.PTheta.ofRealVec a ⬝ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m' - _root_.ReciprocityTheory.PTheta.ofRealVec b ⬝ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m) *
          _root_.ReciprocityTheory.PTheta.eC (-(_root_.ReciprocityTheory.PTheta.ofIntVec m ⬝ᵥ τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec m ⬝ᵥ z)) *
          _root_.ReciprocityTheory.PTheta.eC ((N m m' : ℂ) / 2) * _root_.ReciprocityTheory.PTheta.eC (-(_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.expArg γ τ z) / 2) := by
      simp only [← _root_.ReciprocityTheory.PTheta.eC_add]
      congr 1
      rw [hquad]
      simp only [a, b, _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.ofRealVec_halfVec, smul_dotProduct, _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.ofIntVec_dot, smul_eq_mul, N]
      push_cast
      ring
    simp only [σ]
    linear_combination ρ z * hexp + _root_.ReciprocityTheory.PTheta.eC (-(_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.expArg γ τ (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m + _root_.ReciprocityTheory.PTheta.ofIntVec m')) / 2) * hρrel

  have hN : ∀ m m', 2 ∣ N m m' := _root_.GlobalTheory.two_dvd_of_entire_sign_periodic hτ hσd hσ0 hper
  have hev : ∀ (X : Matrix (Fin g) (Fin g) ℤ), (∀ i j, (2:ℤ) ∣ X i j) →
      ∀ u v : Fin g → ℤ, (2:ℤ) ∣ u ⬝ᵥ X *ᵥ v := by
    intro X hX u v
    refine Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right ?_ _
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_left (hX j k) _
  have hCev : ∀ i j, (2:ℤ) ∣ γ.toBlocks₂₁ i j := fun i j => dvd_trans (by norm_num) (h8 i j).2
  have hBev : ∀ i j, (2:ℤ) ∣ γ.toBlocks₁₂ i j := fun i j => dvd_trans (by norm_num) (h8 i j).1
  have hsingle : ∀ (X : Matrix (Fin g) (Fin g) ℤ) (u : Fin g → ℤ) (i : Fin g),
      (Xᵀ *ᵥ u) i = u ⬝ᵥ X *ᵥ Pi.single i 1 := by
    intro X u i
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    simp
  constructor
  · intro i
    have h := hN 0 (Pi.single i 1)
    have e : (γ.toBlocks₁₁ᵀ *ᵥ n) i - n i = N 0 (Pi.single i 1)
        - n' ⬝ᵥ γ.toBlocks₂₁ *ᵥ Pi.single i 1
        + (γ.toBlocks₁₁ *ᵥ Pi.single i 1) ⬝ᵥ γ.toBlocks₂₁ *ᵥ Pi.single i 1 := by
      simp only [N, P, P', hsingle]
      simp
      rw [dotProduct_comm (γ.toBlocks₂₁.col i)]
      ring
    rw [e]
    exact dvd_add (dvd_sub h (hev _ hCev _ _)) (hev _ hCev _ _)
  · intro i
    have h := hN (Pi.single i 1) 0
    have e : (γ.toBlocks₂₂ᵀ *ᵥ n') i - n' i = -N (Pi.single i 1) 0
        - n ⬝ᵥ γ.toBlocks₁₂ *ᵥ Pi.single i 1
        - (γ.toBlocks₂₂ *ᵥ Pi.single i 1) ⬝ᵥ γ.toBlocks₁₂ *ᵥ Pi.single i 1 := by
      simp only [N, P, P', hsingle]
      simp
      ring
    rw [e]
    exact dvd_sub (dvd_sub (dvd_neg.mpr h) (hev _ hBev _ _)) (hev _ hBev _ _)

end GlobalTheory

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBoxDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenStabilizerSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix

open GlobalTheory.WeilM GlobalTheory.SplitFlip GlobalTheory.RankCoinv MeasureTheory ValuativeRel
open scoped Matrix

namespace GlobalTheory.BlockDiagonalOmegaIdentities

theorem X0_mul_blockDiag {k : Type} [Field k] {a b : ℕ} (g : Matrix (Fin a) (Fin a) k) :
    GlobalTheory.SplitFlip.X0 k (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)) *
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 (1 : Matrix (Fin b) (Fin b) k)) =
      g * GlobalTheory.SplitFlip.X0 k (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)) := by
  ext i j
  obtain ⟨j', rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).surjective j
  rw [frameMatrixFirstColumnBlock_mul_apply]
  rcases j' with j' | j'
  · simp [Matrix.mul_apply, X0, Matrix.fromBlocks]
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply, Matrix.mul_apply, X0, Matrix.of_apply]
    symm
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [if_neg, mul_zero]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega

theorem X0_mul_transpose_X0 {k : Type} [Field k] {a b : ℕ} :
    GlobalTheory.SplitFlip.X0 k (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)) *
      (GlobalTheory.SplitFlip.X0 k (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)))ᵀ = 1 := by
  ext i j
  rw [GlobalTheory.SplitFlip.frameMatrixFirstColumnBlock_mul_apply]
  simp [GlobalTheory.SplitFlip.X0, Matrix.one_apply, eq_comm]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem omA_unit {a d : ℕ} (ν β : kˣ →* ℂˣ) (Φ : Matrix (Fin a) (Fin d) k → ℂ) : omA ν β 1 1 Φ = Φ := by
  funext X; simp [omA]

theorem omA_one_invT_apply {a d : ℕ} (ν β : kˣ →* ℂˣ) (D : GL (Fin d) k) (Φ : Matrix (Fin a) (Fin d) k → ℂ)
    (Y : Matrix (Fin a) (Fin d) k) :
    omA ν β 1 (invT D) Φ Y = ((β (gdet D) : ℂ))⁻¹ * apow (gdet D) ((a : ℂ) / 2) * Φ (Y * D.val) := by
  simp only [omA, map_one, inv_one, Units.val_one, apow_one, mul_one, one_mul, invT_invT, gdet_invT, map_inv,
    apow_inv, Fintype.card_fin, Matrix.one_mul, Units.val_inv_eq_inv_val]
  congr 2
  ring_nf

theorem omA_inv_inv_apply {a d : ℕ} (ν β : kˣ →* ℂˣ) (g : GL (Fin a) k) (D : GL (Fin d) k)
    (Φ : Matrix (Fin a) (Fin d) k → ℂ) (X : Matrix (Fin a) (Fin d) k) :
    omA ν β g⁻¹ (invT D)⁻¹ Φ X = (ν (gdet g) : ℂ) * β (gdet D) * apow (gdet g) ((d : ℂ) / 2) *
      apow (gdet D) (-(a : ℂ) / 2) * Φ (g.val * X * (D⁻¹).val) := by
  simp only [omA, map_inv, invT_invT, gdet_invT, inv_inv, apow_inv, Fintype.card_fin, Units.val_inv_eq_inv_val]
  ring_nf

theorem apow_ofReal (x : kˣ) (t : ℝ) : apow x (t : ℂ) = ((GlobalTheory.SplitWeil.nabs k x ^ t : ℝ) : ℂ) :=
  (Complex.ofReal_cpow (GlobalTheory.SplitWeil.nabs_pos' x).le t).symm

theorem orbit_nhds (a b : ℕ) (S : Set (GL (Fin (a + b)) k)) (hS : IsOpen S) (h1 : 1 ∈ S) :
    ∃ U ∈ nhds (GlobalTheory.SplitFlip.X0 k (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))), ∀ c ∈ U, ∃ M ∈ S,
      GlobalTheory.SplitFlip.X0 k (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)) * M.val = c := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  set X₀ := GlobalTheory.SplitFlip.X0 k (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)) with hX₀
  obtain ⟨T, hT, rfl⟩ := isEmbedding_val_GL.isInducing.isOpen_iff.1 hS
  let φ : Matrix (Fin a) (Fin (a + b)) k → Matrix (Fin (a + b)) (Fin (a + b)) k := fun c => 1 + X₀ᵀ * (c - X₀)
  have hφ : Continuous φ := continuous_const.add (continuous_const.matrix_mul (continuous_id.sub continuous_const))
  have hO : IsOpen (T ∩ {M | M.det ≠ 0}) :=
    hT.inter (isOpen_ne_fun (continuous_id.matrix_det) continuous_const)
  refine ⟨φ ⁻¹' (T ∩ {M | M.det ≠ 0}), (hO.preimage hφ).mem_nhds ?_, fun c hc => ?_⟩
  · have : φ X₀ = 1 := by simp [φ]
    rw [Set.mem_preimage, this]
    exact ⟨h1, by simp⟩
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (φ c) hc.2, hc.1, ?_⟩
    show X₀ * (1 + X₀ᵀ * (c - X₀)) = c
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hX₀, X0_mul_transpose_X0]
    simp

theorem mul_mem_box {a d : ℕ} (ϖ : kˣ) (m : ℕ) {C Y : Matrix (Fin a) (Fin d) k} {N : Matrix (Fin d) (Fin d) k}
    (hN : ∀ i j, N i j ∈ 𝒪[k]) (hY : Y ∈ box ϖ C (fun _ => m)) : Y * N ∈ box ϖ (C * N) (fun _ => m) := by
  intro i j
  rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [← sub_mul, map_mul]
  exact (mul_le_of_le_one_right' (hN l j)).trans (hY i l)

theorem boxFn_mul_inv {a d : ℕ} (ϖ : kˣ) (m : ℕ) (C Y : Matrix (Fin a) (Fin d) k) {M : GL (Fin d) k}
    (hM : M ∈ GlobalTheory.SplitWeil.KO k (Fin d)) :
    boxFn ϖ C (fun _ => m) (Y * (M⁻¹).val) = boxFn ϖ (C * M.val) (fun _ => m) Y := by
  obtain ⟨h1, h2⟩ := (mem_KO_iff M).1 hM
  by_cases hY : Y ∈ box ϖ (C * M.val) (fun _ => m)
  · have := mul_mem_box ϖ m h2 hY
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this
    rw [boxFn, boxFn, Set.indicator_of_mem hY, Set.indicator_of_mem this]; rfl
  · have : Y * (M⁻¹).val ∉ box ϖ C (fun _ => m) := fun h => hY (by
      have := mul_mem_box ϖ m h1 h
      rwa [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one] at this)
    rw [boxFn, boxFn, Set.indicator_of_notMem hY, Set.indicator_of_notMem this]

section Haar
variable {a d : ℕ} [MeasurableSpace (Matrix (Fin a) (Fin d) k)] [BorelSpace (Matrix (Fin a) (Fin d) k)]
  (μ : Measure (Matrix (Fin a) (Fin d) k)) [μ.IsAddHaarMeasure]

theorem integral_boxFn (ϖ : kˣ) (C : Matrix (Fin a) (Fin d) k) (m : ℕ) :
    ∫ X, boxFn ϖ C (fun _ => m) X ∂μ = (μ.real (box ϖ 0 (fun _ => m)) : ℂ) := by
  have hm : MeasurableSet (box ϖ C (fun _ => m)) := (isClopen_box ϖ C _).isOpen.measurableSet
  have e : box ϖ C (fun _ => m) = (fun Y => -C + Y) ⁻¹' box ϖ 0 (fun _ => m) := by
    ext Y
    simp only [box, Set.mem_setOf_eq, Set.mem_preimage, Matrix.add_apply, Matrix.neg_apply, Matrix.zero_apply,
      sub_zero, neg_add_eq_sub, Matrix.sub_apply]
  show ∫ X, (box ϖ C (fun _ => m)).indicator 1 X ∂μ = _
  rw [integral_indicator hm]
  simp only [Pi.one_apply, setIntegral_const, Complex.real_smul, mul_one]
  rw [e, Measure.real, measure_preimage_add]; rfl

theorem real_box_ne_zero (ϖ : kˣ) (m : ℕ) :
    (μ.real (box ϖ (0 : Matrix (Fin a) (Fin d) k) (fun _ => m)) : ℂ) ≠ 0 := by
  have hpos : 0 < μ (box ϖ 0 (fun _ => m)) :=
    (isClopen_box ϖ 0 _).isOpen.measure_pos μ ⟨0, Decomp.mem_box_self ϖ 0 _⟩
  have hfin : μ (box ϖ 0 (fun _ => m)) < ⊤ := (isCompact_box ϖ 0 _).measure_lt_top
  exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'

theorem functional_eq_integral {ϖ : kˣ} (hϖ : IsUnif ϖ) (C : Matrix (Fin a) (Fin d) k) (n : ℕ)
    (T : SB (Matrix (Fin a) (Fin d) k) →ₗ[ℂ] ℂ)
    (hT : ∀ m : ℕ, ∀ c ∈ box ϖ C (fun _ => n), T ⟨boxFn ϖ c (fun _ => m), boxFn_mem_SB ϖ c _⟩ =
      T ⟨boxFn ϖ C (fun _ => m), boxFn_mem_SB ϖ C _⟩) :
    ∃ t : ℂ, ∀ Ψ : SB (Matrix (Fin a) (Fin d) k), (∀ Y ∉ box ϖ C (fun _ => n), Ψ.1 Y = 0) →
      T Ψ = (∫ X, Ψ.1 X ∂μ) * t := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let B : ℕ → Matrix (Fin a) (Fin d) k → SB (Matrix (Fin a) (Fin d) k) :=
    fun m c => ⟨boxFn ϖ c (fun _ => m), boxFn_mem_SB ϖ c _⟩
  let V : ℕ → ℂ := fun m => (μ.real (box ϖ (0 : Matrix (Fin a) (Fin d) k) (fun _ => m)) : ℂ)
  have hV : ∀ m, V m ≠ 0 := real_box_ne_zero μ ϖ
  have key : ∀ Ψ : SB (Matrix (Fin a) (Fin d) k), (∀ Y ∉ box ϖ C (fun _ => n), Ψ.1 Y = 0) →
      ∃ m₁ : ℕ, ∀ m ≥ m₁, T Ψ = (∫ X, Ψ.1 X ∂μ) * (T (B m C) / V m) := by
    intro Ψ hΨ
    obtain ⟨m₁, hm₁⟩ := Decomp.exists_sum_boxFn k (Fin a) (Fin d) ϖ hϖ Ψ.1 Ψ.2
    refine ⟨m₁, fun m hm => ?_⟩
    obtain ⟨s, hs, -⟩ := hm₁ m hm
    have e1 : Ψ = ∑ c ∈ s, Ψ.1 c • B m c := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact hs
    have e2 : T Ψ = (∑ c ∈ s, Ψ.1 c) * T (B m C) := by
      conv_lhs => rw [e1]
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_smul, smul_eq_mul]
      by_cases hc : c ∈ box ϖ C (fun _ => n)
      · rw [hT m c hc]
      · rw [hΨ c hc, zero_mul, zero_mul]
    have e3 : ∫ X, Ψ.1 X ∂μ = (∑ c ∈ s, Ψ.1 c) * V m := by
      have : ∀ X, Ψ.1 X = ∑ c ∈ s, Ψ.1 c * boxFn ϖ c (fun _ => m) X := fun X => by
        conv_lhs => rw [hs]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_congr_ae (Filter.Eventually.of_forall this), integral_finset_sum, Finset.sum_mul]
      · exact Finset.sum_congr rfl fun c _ => by rw [integral_const_mul, integral_boxFn]
      · intro c _
        obtain ⟨h1, h2⟩ := boxFn_mem_SB ϖ c (fun _ => m)
        exact (h1.continuous.integrable_of_hasCompactSupport h2).const_mul _
    rw [e2, e3, mul_assoc, mul_div_cancel₀ _ (hV m)]
  refine ⟨T (B n C) / V n, fun Ψ hΨ => ?_⟩
  obtain ⟨m₁, h1⟩ := key Ψ hΨ
  obtain ⟨m₂, h2⟩ := key (B n C) (fun Y hY => Set.indicator_of_notMem hY _)
  have h3 := h2 (max m₁ m₂) (le_max_right _ _)
  rw [show ∫ X, (B n C).1 X ∂μ = V n from integral_boxFn μ ϖ C n] at h3
  rw [h1 (max m₁ m₂) (le_max_left _ _), h3, mul_div_cancel_left₀ _ (hV n)]

end Haar

theorem local_form (a b : ℕ) (ν β : kˣ →* ℂˣ) (hβ : GlobalTheory.SmGL.IsSmoothChar β)
    (Bf : SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ[ℂ] SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ⋆[ℂ] ℂ)
    (hh : ∀ (h : GL (Fin (a + b)) k) (Ψ₁ Ψ₁' Ψ₂ Ψ₂' : SB (Matrix (Fin a) (Fin (a + b)) k)),
        Ψ₁'.1 = omA ν β 1 h Ψ₁.1 → Ψ₂'.1 = omA ν β 1 h Ψ₂.1 → Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂)
    [MeasurableSpace (Matrix (Fin a) (Fin (a + b)) k)] [BorelSpace (Matrix (Fin a) (Fin (a + b)) k)]
    (μ : Measure (Matrix (Fin a) (Fin (a + b)) k)) [μ.IsAddHaarMeasure]
    (Ψ₂ : SB (Matrix (Fin a) (Fin (a + b)) k)) :
    ∃ U ∈ nhds (GlobalTheory.SplitFlip.X0 k (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))), ∃ c : ℂ,
      ∀ Ψ₁ : SB (Matrix (Fin a) (Fin (a + b)) k), (∀ Y ∉ U, Ψ₁.1 Y = 0) →
        Bf Ψ₁ Ψ₂ = (∫ X, Ψ₁.1 X ∂μ) * c := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
  set X₀ := GlobalTheory.SplitFlip.X0 k (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)) with hX₀
  have hc : Continuous (invT : GL (Fin (a + b)) k → GL (Fin (a + b)) k) :=
    Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩
  have o1 : IsOpen {M : GL (Fin (a + b)) k | omA ν β 1 (invT M⁻¹) Ψ₂.1 = Ψ₂.1} :=
    (GlobalTheory.OmAStab.isOpen_omA_stab k a (a + b) ν β hβ Ψ₂.1 Ψ₂.2).preimage (hc.comp continuous_inv)
  have o2 : IsOpen {M : GL (Fin (a + b)) k | β (gdet M) = 1} :=
    IsOpen.preimage (f := fun M : GL (Fin (a + b)) k => gdet M) Matrix.GeneralLinearGroup.continuous_det hβ
  obtain ⟨U, hU, hUS⟩ := orbit_nhds a b _ ((o1.inter o2).inter isOpen_KO)
    ⟨⟨by simpa using omA_unit ν β Ψ₂.1, by simp⟩, one_mem _⟩
  obtain ⟨n, hn⟩ := Decomp.exists_box_subset hϖ hU
  refine ⟨box ϖ X₀ (fun _ => n), (isClopen_box ϖ X₀ _).isOpen.mem_nhds (Decomp.mem_box_self ϖ X₀ _), ?_⟩
  refine functional_eq_integral μ hϖ X₀ n (Bf.flip Ψ₂) fun m c hc => ?_
  obtain ⟨M, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := hUS c (hn hc)
  refine hh (invT M⁻¹) _ _ Ψ₂ Ψ₂ ?_ h1.symm
  funext Y
  have h4 : β (gdet M⁻¹) = 1 := by
    have h2' : β (gdet M) = 1 := h2
    show β (Matrix.GeneralLinearGroup.det M⁻¹) = 1
    rw [map_inv, map_inv, h2', inv_one]
  rw [omA_one_invT_apply, h4, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (inv_mem h3))]
  show boxFn ϖ (X₀ * M.val) (fun _ => m) Y = _ * boxFn ϖ X₀ (fun _ => m) (Y * (M⁻¹).val)
  rw [boxFn_mul_inv ϖ m _ _ h3]
  simp

theorem integral_mul_mul {a d : ℕ} [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (g : GL (Fin a) k) (M : GL (Fin d) k) (f : Matrix (Fin a) (Fin d) k → ℂ) :
    ∫ X, f (g.val * X * M.val) ∂(GlobalTheory.SplitWeil.volM ν (Fin a) (Fin d)) =
      apow (gdet g) (-(d : ℂ)) * apow (gdet M) (-(a : ℂ)) * ∫ X, f X ∂(GlobalTheory.SplitWeil.volM ν (Fin a) (Fin d)) := by
  rw [GlobalTheory.SplitWeil.integral_comp_mul_mul_volM ν M g f, Complex.real_smul, Complex.ofReal_mul]
  simp only [Fintype.card_fin]
  rw [← apow_ofReal, ← apow_ofReal]
  push_cast
  rfl

theorem frobenius_X0 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β →
    ∀ Bf : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ[ℂ] GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ⋆[ℂ] ℂ,
      (∀ (g : GL (Fin a) k) (Ψ₁ Ψ₁' Ψ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)),
        Ψ₁'.1 = GlobalTheory.SplitFlip.omA ν β g 1 Ψ₁.1 → Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) →
      (∀ (h : GL (Fin (a + b)) k) (Ψ₁ Ψ₁' Ψ₂ Ψ₂' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)),
        Ψ₁'.1 = GlobalTheory.SplitFlip.omA ν β 1 h Ψ₁.1 → Ψ₂'.1 = GlobalTheory.SplitFlip.omA ν β 1 h Ψ₂.1 → Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) →
      ∃ (L : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ⋆[ℂ] ℂ) (χ : kˣ →* ℂˣ) (s : ℝ), (χ = ν ∨ χ = ν⁻¹) ∧
        (∀ Ψ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k), (∀ Ψ₁, Bf Ψ₁ Ψ₂ = 0) → L Ψ₂ = 0) ∧
        (∀ (g : GL (Fin a) k) (Ψ Ψ' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)),
          Ψ'.1 = (fun Y => Ψ.1 (Y * (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1 0 0 (1 : Matrix (Fin b) (Fin b) k))))) →
          L Ψ' = ((χ (Matrix.GeneralLinearGroup.det g) : ℂ) * GlobalTheory.SplitFlip.apow (Matrix.GeneralLinearGroup.det g) (s : ℂ)) * L Ψ) ∧
        (∀ Ψ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k), L Ψ₂ = 0 → ∃ U ∈ nhds (GlobalTheory.SplitFlip.X0 k (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))),
          ∀ Ψ₁ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k), (∀ Y ∉ U, Ψ₁.1 Y = 0) → Bf Ψ₁ Ψ₂ = 0) := by
  intro k _ _ _ _ a b ν β hνs hνu hβs hβu Bf hg hh
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  letI : MeasurableSpace (Matrix (Fin a) (Fin (a + b)) k) := GlobalTheory.SplitWeil.matrixMeasurableSpace
  haveI : BorelSpace (Matrix (Fin a) (Fin (a + b)) k) := inferInstanceAs (BorelSpace (Fin a → Fin (a + b) → k))
  set μ := GlobalTheory.SplitWeil.volM (Measure.addHaar : Measure k) (Fin a) (Fin (a + b)) with hμdef
  haveI : μ.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
  set X₀ := GlobalTheory.SplitFlip.X0 k (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)) with hX₀
  have htest : ∀ U ∈ nhds X₀, ∃ Ψ₁ : SB (Matrix (Fin a) (Fin (a + b)) k), (∀ Y ∉ U, Ψ₁.1 Y = 0) ∧
      ∫ X, Ψ₁.1 X ∂μ ≠ 0 := by
    intro U hU
    obtain ⟨n, hn⟩ := Decomp.exists_box_subset hϖ hU
    refine ⟨⟨boxFn ϖ X₀ (fun _ => n), boxFn_mem_SB ϖ X₀ _⟩,
      fun Y hY => Set.indicator_of_notMem (fun h => hY (hn h)) _, ?_⟩
    show ∫ X, boxFn ϖ X₀ (fun _ => n) X ∂μ ≠ 0
    rw [integral_boxFn]
    exact real_box_ne_zero μ ϖ n
  let P : SB (Matrix (Fin a) (Fin (a + b)) k) → Set (Matrix (Fin a) (Fin (a + b)) k) → ℂ → Prop :=
    fun Ψ₂ U c => U ∈ nhds X₀ ∧ ∀ Ψ₁ : SB (Matrix (Fin a) (Fin (a + b)) k), (∀ Y ∉ U, Ψ₁.1 Y = 0) →
      Bf Ψ₁ Ψ₂ = (∫ X, Ψ₁.1 X ∂μ) * c
  have huniq : ∀ Ψ₂ U U' c c', P Ψ₂ U c → P Ψ₂ U' c' → c = c' := by
    rintro Ψ₂ U U' c c' ⟨hU, h⟩ ⟨hU', h'⟩
    obtain ⟨Ψ₁, hs, hi⟩ := htest (U ∩ U') (Filter.inter_mem hU hU')
    have e1 := h Ψ₁ (fun Y hY => hs Y (fun h => hY h.1))
    have e2 := h' Ψ₁ (fun Y hY => hs Y (fun h => hY h.2))
    exact mul_left_cancel₀ hi (e1.symm.trans e2)
  have hex : ∀ Ψ₂, ∃ U c, P Ψ₂ U c := fun Ψ₂ => by
    obtain ⟨U, hU, c, hc⟩ := local_form a b ν β hβs Bf hh μ Ψ₂
    exact ⟨U, c, hU, hc⟩
  choose U0 c0 hc0 using hex
  have hL : ∀ Ψ₂ U c, P Ψ₂ U c → c0 Ψ₂ = c := fun Ψ₂ U c h => huniq _ _ _ _ _ (hc0 Ψ₂) h
  let L : SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ⋆[ℂ] ℂ :=
    { toFun := c0
      map_add' := fun x y => hL (x + y) (U0 x ∩ U0 y) (c0 x + c0 y) ⟨Filter.inter_mem (hc0 x).1 (hc0 y).1,
        fun Ψ₁ hs => by
          rw [map_add, (hc0 x).2 Ψ₁ (fun Y hY => hs Y (fun h => hY h.1)),
            (hc0 y).2 Ψ₁ (fun Y hY => hs Y (fun h => hY h.2)), mul_add]⟩
      map_smul' := fun r x => hL (r • x) (U0 x) (starRingEnd ℂ r * c0 x) ⟨(hc0 x).1,
        fun Ψ₁ hs => by rw [map_smulₛₗ, (hc0 x).2 Ψ₁ hs, smul_eq_mul]; ring⟩ }
  have hLapp : ∀ Ψ, L Ψ = c0 Ψ := fun _ => rfl
  refine ⟨L, ν, -((a : ℝ) + b) / 2, Or.inl rfl, ?_, ?_, ?_⟩
  · intro Ψ₂ h0
    rw [hLapp]
    exact hL _ Set.univ 0 ⟨Filter.univ_mem, fun Ψ₁ _ => by rw [h0, mul_zero]⟩
  · intro g Ψ Ψ' hΨ'
    clear htest huniq
    rw [hLapp, hLapp]
    set D : GL (Fin (a + b)) k := Matrix.GeneralLinearGroup.mkOfDetNeZero
      (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1 0 0 (1 : Matrix (Fin b) (Fin b) k)))
      (by rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]; exact g.det_ne_zero)
      with hD
    have hDval : D.val = Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks g.1 0 0 (1 : Matrix (Fin b) (Fin b) k)) := rfl
    have hgD : gdet D = gdet g := Units.ext (by
      simp only [gdet, Matrix.GeneralLinearGroup.val_det_apply, hDval]
      rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one])
    have hgDi : gdet D⁻¹ = (gdet g)⁻¹ := by
      show Matrix.GeneralLinearGroup.det D⁻¹ = _
      rw [map_inv]; exact congrArg (·⁻¹) hgD
    have hfixM : X₀ * D.val = g.val * X₀ := X0_mul_blockDiag g.val
    have hfix : (g⁻¹).val * X₀ * D.val = X₀ := by
      rw [Matrix.mul_assoc, hfixM, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    set x := gdet g with hx
    set h : GL (Fin (a + b)) k := invT D with hh_def
    let r : ℂ := (β x : ℂ) * apow x ((-(a : ℝ) / 2 : ℝ) : ℂ)
    let Ψh : SB (Matrix (Fin a) (Fin (a + b)) k) := ⟨omA ν β 1 h Ψ.1, omA_mem_SB ν β 1 h Ψ.2⟩
    have hβx : (β x : ℂ) ≠ 0 := Units.ne_zero _
    have e1 : Ψ' = r • Ψh := by
      apply Subtype.ext
      funext Y
      show Ψ'.1 Y = r * omA ν β 1 (invT D) Ψ.1 Y
      rw [hΨ', omA_one_invT_apply, hgD]
      show Ψ.1 (Y * D.val) = _
      have : apow x ((-(a : ℝ) / 2 : ℝ) : ℂ) * apow x ((a : ℂ) / 2) = 1 := by
        rw [← apow_add]; push_cast; ring_nf; exact apow_zero x
      simp only [r]
      rw [show ∀ u v w z : ℂ, u * v * (u⁻¹ * w * z) = (u * u⁻¹) * (v * w) * z from fun _ _ _ _ => by ring,
        mul_inv_cancel₀ hβx, this]
      ring

    let U' : Set (Matrix (Fin a) (Fin (a + b)) k) := (fun Y => (g⁻¹).val * Y * D.val) ⁻¹' U0 Ψ
    have hU' : U' ∈ nhds X₀ := by
      have hcont : Continuous fun Y : Matrix (Fin a) (Fin (a + b)) k => (g⁻¹).val * Y * D.val :=
        (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      have := hcont.continuousAt (x := X₀) |>.preimage_mem_nhds (by rw [hfix]; exact (hc0 Ψ).1)
      exact this
    refine hL Ψ' U' _ ⟨hU', fun Ψ₁ hs => ?_⟩
    let Ψ₁' : SB (Matrix (Fin a) (Fin (a + b)) k) := ⟨omA ν β g⁻¹ h⁻¹ Ψ₁.1, omA_mem_SB ν β g⁻¹ h⁻¹ Ψ₁.2⟩
    let Ψ₁'' : SB (Matrix (Fin a) (Fin (a + b)) k) := ⟨omA ν β 1 h⁻¹ Ψ₁.1, omA_mem_SB ν β 1 h⁻¹ Ψ₁.2⟩
    have s1 : Bf Ψ₁ Ψh = Bf Ψ₁'' Ψ := by
      refine hh h Ψ₁'' Ψ₁ Ψ Ψh ?_ rfl
      show Ψ₁.1 = omA ν β 1 h (omA ν β 1 h⁻¹ Ψ₁.1)
      rw [← omA_mul, mul_one, mul_inv_cancel, omA_unit]
    have s2 : Bf Ψ₁' Ψ = Bf Ψ₁'' Ψ := by
      refine hg g⁻¹ Ψ₁'' Ψ₁' Ψ ?_
      show omA ν β g⁻¹ h⁻¹ Ψ₁.1 = omA ν β g⁻¹ 1 (omA ν β 1 h⁻¹ Ψ₁.1)
      rw [← omA_mul, mul_one, one_mul]
    have hs' : ∀ Y ∉ U0 Ψ, Ψ₁'.1 Y = 0 := by
      intro Y hY
      show omA ν β g⁻¹ (invT D)⁻¹ Ψ₁.1 Y = 0
      rw [omA_inv_inv_apply]
      have : g.val * Y * (D⁻¹).val ∉ U' := by
        show ¬ ((g⁻¹).val * (g.val * Y * (D⁻¹).val) * D.val ∈ U0 Ψ)
        rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
          Units.inv_mul, Matrix.mul_one]
      rw [hs _ this, mul_zero]
    have s3 := (hc0 Ψ).2 Ψ₁' hs'
    have hint : ∫ X, Ψ₁'.1 X ∂μ = (ν x : ℂ) * β x * apow x (((a + b : ℕ) : ℂ) / 2) * apow x (-(a : ℂ) / 2) *
        (apow x (-((a + b : ℕ) : ℂ)) * apow x (a : ℂ) * ∫ X, Ψ₁.1 X ∂μ) := by
      have : ∀ X, Ψ₁'.1 X = (ν x : ℂ) * β x * apow x (((a + b : ℕ) : ℂ) / 2) * apow x (-(a : ℂ) / 2) *
          Ψ₁.1 (g.val * X * (D⁻¹).val) := fun X => by
        show omA ν β g⁻¹ (invT D)⁻¹ Ψ₁.1 X = _
        rw [omA_inv_inv_apply, hgD]
      simp_rw [this]
      rw [integral_const_mul, hμdef, integral_mul_mul, hgDi, apow_inv, neg_neg]
    have hconj : starRingEnd ℂ r = starRingEnd ℂ (β x : ℂ) * apow x ((-(a : ℝ) / 2 : ℝ) : ℂ) := by
      simp only [r, map_mul]
      rw [apow_ofReal, Complex.conj_ofReal]
    have hββ : starRingEnd ℂ (β x : ℂ) * β x = 1 := by
      rw [Complex.conj_mul', hβu x]; simp
    have hA : apow x ((-(a : ℝ) / 2 : ℝ) : ℂ) * apow x (((a + b : ℕ) : ℂ) / 2) * apow x (-(a : ℂ) / 2) *
        apow x (-((a + b : ℕ) : ℂ)) * apow x (a : ℂ) = apow x ((-((a : ℝ) + b) / 2 : ℝ) : ℂ) := by
      rw [← apow_add, ← apow_add, ← apow_add, ← apow_add]
      congr 1
      push_cast
      ring
    rw [e1, map_smulₛₗ, smul_eq_mul, s1, ← s2, s3, hint, hconj]
    linear_combination ((ν x : ℂ) * c0 Ψ * (∫ X, Ψ₁.1 X ∂μ) * (apow x ((-(a : ℝ) / 2 : ℝ) : ℂ) *
      apow x (((a + b : ℕ) : ℂ) / 2) * apow x (-(a : ℂ) / 2) * apow x (-((a + b : ℕ) : ℂ)) * apow x (a : ℂ))) * hββ +
      ((ν x : ℂ) * c0 Ψ * (∫ X, Ψ₁.1 X ∂μ)) * hA
  · intro Ψ₂ h0
    rw [hLapp] at h0
    exact ⟨U0 Ψ₂, (hc0 Ψ₂).1, fun Ψ₁ hs => by rw [(hc0 Ψ₂).2 Ψ₁ hs, h0, mul_zero]⟩

end GlobalTheory.BlockDiagonalOmegaIdentities

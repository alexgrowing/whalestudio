import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldTopologyNormBallsStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemIntegralGLIffIntegralUnitDetStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlockMatrixMulBlocks
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.Tame

section Alg

variable {F : Type} [Field F]

theorem det_eq_coe {ι : Type} [Fintype ι] [DecidableEq ι] (O : Subring F) (X : Matrix ι ι F)
    (hX : ∀ i j, X i j ∈ O) :
    X.det = ((Matrix.det (fun i j => (⟨X i j, hX i j⟩ : O)) : O) : F) := by
  have h := RingHom.map_det O.subtype (fun i j => (⟨X i j, hX i j⟩ : O))
  have h2 : O.subtype.mapMatrix (fun i j => (⟨X i j, hX i j⟩ : O) : Matrix ι ι O) = X := by
    ext i j; rfl
  rw [h2] at h
  exact h.symm

theorem det_mem {ι : Type} [Fintype ι] [DecidableEq ι] (O : Subring F) (X : Matrix ι ι F)
    (hX : ∀ i j, X i j ∈ O) : X.det ∈ O := by
  rw [det_eq_coe O X hX]; exact Subtype.property _

theorem det_congr_mod {ι : Type} [Fintype ι] [DecidableEq ι] (O : Subring F) {ϖ : F} (hϖ : ϖ ∈ O)
    (X Y : Matrix ι ι F) (hX : ∀ i j, X i j ∈ O) (hY : ∀ i j, Y i j ∈ O)
    (h : ∀ i j, ∃ o ∈ O, X i j - Y i j = ϖ * o) : ∃ o ∈ O, X.det - Y.det = ϖ * o := by
  let Xo : Matrix ι ι O := fun i j => ⟨X i j, hX i j⟩
  let Yo : Matrix ι ι O := fun i j => ⟨Y i j, hY i j⟩
  let I : Ideal O := Ideal.span {⟨ϖ, hϖ⟩}
  have hmap : (Ideal.Quotient.mk I).mapMatrix Xo = (Ideal.Quotient.mk I).mapMatrix Yo := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    obtain ⟨o, ho, e⟩ := h i j
    refine ⟨⟨o, ho⟩, Subtype.ext ?_⟩
    change o * ϖ = X i j - Y i j
    rw [e, mul_comm]
  have hdet : Ideal.Quotient.mk I Xo.det = Ideal.Quotient.mk I Yo.det := by
    rw [RingHom.map_det, RingHom.map_det, hmap]
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hdet
  obtain ⟨a, ha⟩ := hdet
  refine ⟨a, a.2, ?_⟩
  rw [det_eq_coe O X hX, det_eq_coe O Y hY]
  have := congrArg Subtype.val ha
  change (a : F) * ϖ = ((Xo.det : O) : F) - ((Yo.det : O) : F) at this
  change ((Xo.det : O) : F) - ((Yo.det : O) : F) = ϖ * a
  rw [← this, mul_comm]

theorem det_eq_blocks {r c : ℕ} (M : Matrix (Fin (r + c)) (Fin (r + c)) F) :
    M.det = (Matrix.fromBlocks (bAA M) (bAD M) (bDA M) (bDD M)).det := by
  have h : M = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (bAA M) (bAD M) (bDA M) (bDD M)) := by
    ext i j
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp [bAA, bAD, bDA, bDD]
  conv_lhs => rw [h]
  exact Matrix.det_reindex_self _ _

theorem bDD_one {r c : ℕ} : bDD (1 : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 :=
  Matrix.submatrix_one _ (Fin.natAdd_injective _ _)

theorem extendedCharacter_units (δ : Fˣ →* ℂˣ) (u : Fˣ) : chi0 δ (u : F) = ((δ u : ℂˣ) : ℂ) := by
  unfold chi0
  rw [dif_neg u.ne_zero]
  simp

theorem unitCharExtendedByZero_mul (δ : Fˣ →* ℂˣ) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    chi0 δ (x * y) = chi0 δ x * chi0 δ y := by
  have e : x * y = ((Units.mk0 x hx * Units.mk0 y hy : Fˣ) : F) := by simp
  rw [e, extendedCharacter_units, map_mul, Units.val_mul, ← extendedCharacter_units, ← extendedCharacter_units]
  simp

theorem extendedCharacter_congr_of_tame {nrm : AbsoluteValue F ℝ} {δ : Fˣ →* ℂˣ} (hδ : Del nrm δ) {x y : F}
    (hy : nrm y = 1) (hxy : nrm (x - y) < 1) : chi0 δ x = chi0 δ y := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [hy] at hxy
  have h1 : δ (Units.mk0 x hx0 / Units.mk0 y hy0) = 1 := by
    apply hδ.tame
    have e : (((Units.mk0 x hx0 / Units.mk0 y hy0 : Fˣ) : F) - 1) = (x - y) / y := by
      simp only [Units.val_div_eq_div_val, Units.val_mk0]
      field_simp
    rw [e, map_div₀, hy, div_one]
    exact hxy
  rw [map_div, div_eq_one] at h1
  have ex : x = ((Units.mk0 x hx0 : Fˣ) : F) := rfl
  have ey : y = ((Units.mk0 y hy0 : Fˣ) : F) := rfl
  rw [ex, ey, extendedCharacter_units, extendedCharacter_units, h1]

end Alg

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem par_data (h : LF O ϖ nrm q) {r c : ℕ} {k : GL (Fin (r + c)) F} (hk : k ∈ parJ O ϖ r c) :
    nrm (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧
    nrm (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧
    ∃ o ∈ O, (k : Matrix (Fin (r + c)) (Fin (r + c)) F).det -
      (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det *
      (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = ϖ * o := by
  obtain ⟨-, hϖ, hO, hlt, -, hult, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties h
  set M : Matrix (Fin (r + c)) (Fin (r + c)) F := (k : Matrix (Fin (r + c)) (Fin (r + c)) F) with hMdef
  have hM : IsInt O M := hk.1.1
  have hdet : nrm M.det = 1 := ((GlobalTheory.T.mem_integralGL_iff_integral_unit_det h (r + c) k).1 hk.1).2
  have hC := hk.2
  have hcong : ∃ o ∈ O, M.det - (bAA M).det * (bDD M).det = ϖ * o := by
    have := det_congr_mod O hϖ (Matrix.fromBlocks (bAA M) (bAD M) (bDA M) (bDD M))
      (Matrix.fromBlocks (bAA M) (bAD M) 0 (bDD M))
      (by rintro (i | i) (j | j) <;> exact hM _ _)
      (by
        rintro (i | i) (j | j)
        · exact hM _ _
        · exact hM _ _
        · exact O.zero_mem
        · exact hM _ _)
      (by
        rintro (i | i) (j | j)
        · exact ⟨0, O.zero_mem, by simp⟩
        · exact ⟨0, O.zero_mem, by simp⟩
        · obtain ⟨o, ho, e⟩ := hC i j
          exact ⟨o, ho, by simpa using e⟩
        · exact ⟨0, O.zero_mem, by simp⟩)
    rwa [← det_eq_blocks, Matrix.det_fromBlocks_zero₂₁] at this
  obtain ⟨o, ho, e⟩ := hcong
  have hA : nrm (bAA M).det ≤ 1 := (hO _).2 (det_mem O _ fun i j => hM _ _)
  have hD : nrm (bDD M).det ≤ 1 := (hO _).2 (det_mem O _ fun i j => hM _ _)
  have hsmall : nrm (ϖ * o) < 1 := (hlt _).2 ⟨o, ho, rfl⟩
  have hprod : 1 ≤ nrm (bAA M).det * nrm (bDD M).det := by
    have e2 : M.det = (bAA M).det * (bDD M).det + ϖ * o := by rw [← e]; ring
    have h3 := hult ((bAA M).det * (bDD M).det) (ϖ * o)
    rw [← e2, hdet, map_mul] at h3
    rcases le_max_iff.1 h3 with h4 | h4
    · exact h4
    · exact absurd h4 (not_le.2 hsmall)
  have hA0 : 0 ≤ nrm (bAA M).det := nrm.nonneg _
  have hD0 : 0 ≤ nrm (bDD M).det := nrm.nonneg _
  refine ⟨?_, ?_, o, ho, e⟩ <;> nlinarith

theorem lam_mul (h : LF O ϖ nrm q) {δ : Fˣ →* ℂˣ} (hδ : Del nrm δ) {r c : ℕ}
    {k k' : GL (Fin (r + c)) F} (hk : k ∈ parJ O ϖ r c) (hk' : k' ∈ parJ O ϖ r c) :
    lamJ δ (k * k') = lamJ δ k * lamJ δ k' := by
  obtain ⟨-, hϖ, hO, hlt, -, -, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties h
  obtain ⟨-, hD, -⟩ := par_data h hk
  obtain ⟨-, hD', -⟩ := par_data h hk'
  unfold lamJ
  have hC := hk.2
  set M : Matrix (Fin (r + c)) (Fin (r + c)) F := (k : Matrix (Fin (r + c)) (Fin (r + c)) F) with hMdef
  set M' : Matrix (Fin (r + c)) (Fin (r + c)) F := (k' : Matrix (Fin (r + c)) (Fin (r + c)) F) with hM'def
  have hM : IsInt O M := hk.1.1
  have hM' : IsInt O M' := hk'.1.1
  have hprod : ((k * k' : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = M * M' := rfl
  have hblock : bDD (M * M') = bDA M * bAD M' + bDD M * bDD M' :=
    (GlobalTheory.CompanionTheory.QL.BlockMul.blocks_mul r c c c M M').2.2.2
  rw [hprod, hblock]
  choose o ho e using hC
  have hCB : ∀ i j, ∃ t ∈ O, (bDA M * bAD M') i j = ϖ * t := by
    intro i j
    refine ⟨∑ l, o i l * bAD M' l j, O.sum_mem fun l _ => O.mul_mem (ho i l) (hM' _ _), ?_⟩
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [e i l, mul_assoc]
  have hDD : ∀ i j, (bDD M * bDD M') i j ∈ O := by
    intro i j
    rw [Matrix.mul_apply]
    exact O.sum_mem fun l _ => O.mul_mem (hM _ _) (hM' _ _)
  obtain ⟨t, ht, et⟩ := det_congr_mod O hϖ (bDA M * bAD M' + bDD M * bDD M') (bDD M * bDD M')
    (by
      intro i j
      obtain ⟨t, ht, et⟩ := hCB i j
      rw [Matrix.add_apply, et]
      exact O.add_mem (O.mul_mem hϖ ht) (hDD i j))
    hDD
    (by
      intro i j
      obtain ⟨t, ht, et⟩ := hCB i j
      exact ⟨t, ht, by rw [Matrix.add_apply, et]; ring⟩)
  have hn : nrm (bDD M * bDD M').det = 1 := by
    rw [Matrix.det_mul, map_mul, hD, hD', one_mul]
  have hne : ∀ {x : F}, nrm x = 1 → x ≠ 0 := by
    rintro x hx rfl
    simp at hx
  rw [extendedCharacter_congr_of_tame hδ hn (by rw [et]; exact (hlt _).2 ⟨t, ht, rfl⟩), Matrix.det_mul,
    unitCharExtendedByZero_mul δ (hne hD) (hne hD')]

end Loc

theorem tame_character : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ δ : Fˣ →* ℂˣ, Del nrm δ → ∀ r c : ℕ, lamJ δ (1 : GL (Fin (r + c)) F) = 1 ∧ (∀ k ∈ parJ O ϖ r c, ‖lamJ δ k‖ = 1 ∧ nrm (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧ nrm (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧ ((δ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) = chi0 δ (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * lamJ δ k ∧ ∀ k' ∈ parJ O ϖ r c, lamJ δ (k * k') = lamJ δ k * lamJ δ k') ∧ ContinuousOn (fun k : GL (Fin (r + c)) F => lamJ δ k) (parJ O ϖ r c) := by
  intro F _ _ _ _ O ϖ nrm q h δ hδ r c
  obtain ⟨-, hϖ, hO, hlt, -, -, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties h
  have hne : ∀ {x : F}, nrm x = 1 → x ≠ 0 := by
    rintro x hx rfl
    simp at hx
  refine ⟨?_, ?_, ?_⟩
  · unfold lamJ
    have e : ((1 : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 := rfl
    rw [e, bDD_one, Matrix.det_one]
    have := extendedCharacter_units δ (1 : Fˣ)
    simpa using this
  · intro k hk
    obtain ⟨hA, hD, o, ho, e⟩ := par_data h hk
    refine ⟨?_, hA, hD, ?_, fun k' hk' => lam_mul h hδ hk hk'⟩
    · unfold lamJ
      have : (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det =
          ((Units.mk0 _ (hne hD) : Fˣ) : F) := rfl
      rw [this, extendedCharacter_units]
      exact hδ.unitary _
    · unfold lamJ
      rw [← extendedCharacter_units, ← unitCharExtendedByZero_mul δ (hne hA) (hne hD)]
      apply extendedCharacter_congr_of_tame hδ
      · rw [map_mul, hA, hD, one_mul]
      · rw [Matrix.GeneralLinearGroup.val_det_apply, e]
        exact (hlt _).2 ⟨o, ho, rfl⟩
  · obtain ⟨-, -, -, hcont, -, -⟩ := GlobalTheory.T.localField_topology_norm_balls h
    intro k₀ hk₀
    obtain ⟨-, hD₀, -⟩ := par_data h hk₀
    have hf : Continuous (fun k : GL (Fin (r + c)) F =>
        (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det) :=
      Continuous.matrix_det (Continuous.matrix_submatrix Units.continuous_val _ _)
    have hU : {k : GL (Fin (r + c)) F | nrm ((bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det -
        (bDD (k₀ : Matrix (Fin (r + c)) (Fin (r + c)) F)).det) < 1} ∈ nhds k₀ := by
      refine IsOpen.mem_nhds (isOpen_lt (hcont.comp (hf.sub continuous_const)) continuous_const) ?_
      simp
    refine (continuousWithinAt_const (b := lamJ δ k₀)).congr_of_eventuallyEq ?_ rfl
    filter_upwards [mem_nhdsWithin_of_mem_nhds hU] with k hkU
    exact extendedCharacter_congr_of_tame hδ hD₀ hkU

end GlobalTheory.CompanionTheory.QL.Tame

import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.CellsSub

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.kunf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} {nb : nA σ Y b → G2 σ Y}

theorem toBlocks₁₁_mul' {R : Type} [CommRing R] (X Z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    (X * Z).toBlocks₁₁ = X.toBlocks₁₁ * Z.toBlocks₁₁ + X.toBlocks₁₂ * Z.toBlocks₂₁ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks X, ← Matrix.fromBlocks_toBlocks Z]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁]

theorem incM_GL_mul_inv (t₀ : GL (Fin n) E) : incM F t₀.1 * incM F (t₀⁻¹).1 = 1 := by
  rw [← incM_mul', Units.mul_inv]; ext i j; simp [incM, Matrix.one_apply]

theorem incM_GL_inv_mul (t₀ : GL (Fin n) E) : incM F (t₀⁻¹).1 * incM F t₀.1 = 1 := by
  rw [← incM_mul', Units.inv_mul]; ext i j; simp [incM, Matrix.one_apply]

theorem mem_stabiliser_iff_frame_lower_block (hb : IsFrame2 σ Y b) (p : G2 σ Y) : p ∈ par2 σ Y ↔ (inFrame b p).toBlocks₂₁ = 0 := by
  obtain ⟨-, t₀, ht₀⟩ := hb
  constructor
  · intro h
    obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 h
    exact ((isPar_frame ht₀ p t).1 ht).1
  · intro h
    set P := inFrame b p
    set P' := inFrame b p⁻¹
    have hPP : P' * P = 1 := GlobalTheory.EisBL.DoubledParabolic.inFrame_inv_mul b p
    have h1 : P'.toBlocks₁₁ * P.toBlocks₁₁ = 1 := by
      have := congrArg Matrix.toBlocks₁₁ hPP
      rw [toBlocks₁₁_mul', h, Matrix.mul_zero, add_zero] at this
      rw [this]; ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]
    have h2 : P.toBlocks₁₁ * P'.toBlocks₁₁ = 1 := mul_eq_one_comm.1 h1
    set T0 := incM F t₀.1
    set Ti := incM F (t₀⁻¹).1
    have hT : T0 * Ti = 1 := incM_GL_mul_inv t₀
    let t : GL (Fin n) (AE F E) := ⟨T0 * P.toBlocks₁₁ * Ti, T0 * P'.toBlocks₁₁ * Ti, by
        calc T0 * P.toBlocks₁₁ * Ti * (T0 * P'.toBlocks₁₁ * Ti)
            = T0 * (P.toBlocks₁₁ * (Ti * T0) * P'.toBlocks₁₁) * Ti := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [incM_GL_inv_mul, Matrix.mul_one, h2, Matrix.mul_one, hT], by
        calc T0 * P'.toBlocks₁₁ * Ti * (T0 * P.toBlocks₁₁ * Ti)
            = T0 * (P'.toBlocks₁₁ * (Ti * T0) * P.toBlocks₁₁) * Ti := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [incM_GL_inv_mul, Matrix.mul_one, h1, Matrix.mul_one, hT]⟩
    exact mem_parabolic_GL2_iff.2 ⟨t, (isPar_frame ht₀ p t).2 ⟨h, rfl⟩⟩

theorem big_inj' (hb : IsFrame2 σ Y b) {ε : ℤˣ} {w : G2 σ Y}
    (hw : inFrame b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0) (hnb : IsNMap b nb) {ν ν' : nA σ Y b}
    (h : (w * nb ν) * (w * nb ν')⁻¹ ∈ par2 σ Y) : ν = ν' := by
  set e : AE F E := ((ε : ℤ) : AE F E) with he_def
  have he : e * e = 1 := by
    rw [he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hg : (w * nb ν) * (w * nb ν')⁻¹ = w * nb (ν - ν') * w⁻¹ := by
    have : nb (ν - ν') = nb ν * (nb ν')⁻¹ := eq_mul_inv_of_mul_eq (by rw [← nb_add hnb, sub_add_cancel])
    rw [this]; group
  set W' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := Matrix.fromBlocks 0 (e • 1) 1 0 with hW'
  have hWW : inFrame b w * W' = 1 := by
    rw [hw, hW', Matrix.fromBlocks_multiply]
    simp [smul_smul, he, Matrix.fromBlocks_one]
  have hwinv : inFrame b w⁻¹ = W' := by
    calc inFrame b w⁻¹ = inFrame b w⁻¹ * (inFrame b w * W') := by rw [hWW, Matrix.mul_one]
      _ = W' := by rw [← Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.inFrame_inv_mul, Matrix.one_mul]
  have h21 := (mem_stabiliser_iff_frame_lower_block hb _).1 h
  rw [hg, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hw, hnb, hwinv, hW',
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁] at h21
  simp at h21
  have h3 := congrArg (fun X => e • X) h21
  simp only [smul_smul, he, one_smul, smul_zero] at h3
  exact Subtype.ext (sub_eq_zero.1 h3)

theorem sigma_invol (B : Base F E) (hB : B.IsGood σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]

theorem rat_frame {ε : ℤˣ} (hε : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    {γ : G2 σ Y} (hγ : γ ∈ rat2 σ Y) :
    ∃ M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E, inFrame b γ = incM F M ∧
      Mᵀ * jw n ((ε : ℤ) : E) * M.map σ = jw n ((ε : ℤ) : E) := by
  obtain ⟨g, hg⟩ := hγ
  have hm : mat2 γ = incM F g.1 := (congrArg Units.val hg).symm
  have hM : inFrame b γ = incM F ((b⁻¹).1 * g.1 * b.1) := by
    show incM F (b⁻¹).1 * mat2 γ * incM F b.1 = _
    rw [hm, incM_mul', incM_mul']
  refine ⟨_, hM, ?_⟩
  apply incM_inj (F := F)
  have h := frame_eq hε γ
  rw [hM] at h
  rw [incM_mul', incM_mul', incM_jw, ← incM_map_cA, incM_transpose', map_intCast]
  exact h

theorem inFrame_inv_of_rat {γ : G2 σ Y} {M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E}
    (hM : inFrame b γ = incM F M) (h : M * M' = 1) : inFrame b γ⁻¹ = incM F M' := by
  have h1 : incM F M * incM F M' = 1 := by
    rw [← incM_mul', h]; ext i j; simp [incM, Matrix.one_apply]
  calc inFrame b γ⁻¹ = inFrame b γ⁻¹ * (incM F M * incM F M') := by rw [h1, Matrix.mul_one]
    _ = incM F M' := by rw [← Matrix.mul_assoc, ← hM, GlobalTheory.EisBL.DoubledParabolic.inFrame_inv_mul, Matrix.one_mul]

theorem herm_quot {K : Type} [Field K] (s : K →+* K) {e : K} (he : e * e = 1)
    (c d : Matrix (Fin n) (Fin n) K) (hc : c.det ≠ 0)
    (h : c * (d.map s)ᵀ + d * (e • (c.map s)ᵀ) = 0) : (c⁻¹ * d)ᵀ = -(e • (c⁻¹ * d).map s) := by
  have hu : IsUnit c.det := isUnit_iff_ne_zero.2 hc
  have h1 : c⁻¹ * c = 1 := Matrix.nonsing_inv_mul c hu
  have h2 : c * c⁻¹ = 1 := Matrix.mul_nonsing_inv c hu
  have h3 : (c⁻¹).map s * c.map s = 1 := by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero s) (map_one s)]
  have h4 : c.map s * (c⁻¹).map s = 1 := by rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero s) (map_one s)]
  have h5 : cᵀ * (c⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have h6 : (c⁻¹)ᵀ * cᵀ = 1 := by rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]
  have ht : c.map s * dᵀ = -(e • (d.map s * cᵀ)) := by
    have := congrArg Matrix.transpose h
    rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_smul,
      Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.transpose_zero, Matrix.smul_mul] at this
    have h7 := congrArg (fun X => e • X) (eq_neg_of_add_eq_zero_right this)
    simp only [smul_smul, he, one_smul, smul_neg] at h7
    exact h7
  have key : c.map s * (c⁻¹ * d)ᵀ * cᵀ = c.map s * (-(e • (c⁻¹ * d).map s)) * cᵀ := by
    rw [Matrix.transpose_mul, Matrix.map_mul]
    calc c.map s * (dᵀ * (c⁻¹)ᵀ) * cᵀ = c.map s * dᵀ * ((c⁻¹)ᵀ * cᵀ) := by simp only [Matrix.mul_assoc]
      _ = -(e • (d.map s * cᵀ)) := by rw [h6, Matrix.mul_one, ht]
      _ = c.map s * (-(e • ((c⁻¹).map s * d.map s))) * cᵀ := by
        rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, h4, Matrix.one_mul]
  calc (c⁻¹ * d)ᵀ = (c⁻¹).map s * (c.map s * (c⁻¹ * d)ᵀ * cᵀ) * (c⁻¹)ᵀ := by
        simp only [← Matrix.mul_assoc]; rw [h3, Matrix.one_mul]; simp only [Matrix.mul_assoc]; rw [h5, Matrix.mul_one]
    _ = (c⁻¹).map s * (c.map s * (-(e • (c⁻¹ * d).map s)) * cᵀ) * (c⁻¹)ᵀ := by rw [key]
    _ = -(e • (c⁻¹ * d).map s) := by
        simp only [← Matrix.mul_assoc]; rw [h3, Matrix.one_mul]; simp only [Matrix.mul_assoc]; rw [h5, Matrix.mul_one]

theorem inFrame_w_inv {ε : ℤˣ} {w : G2 σ Y}
    (hw : inFrame b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0) :
    inFrame b w⁻¹ = Matrix.fromBlocks 0 (((ε : ℤ) : AE F E) • 1) 1 0 := by
  set e : AE F E := ((ε : ℤ) : AE F E) with he_def
  have he : e * e = 1 := by
    rw [he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hWW : inFrame b w * Matrix.fromBlocks 0 (e • 1) 1 0 = 1 := by
    rw [hw, Matrix.fromBlocks_multiply]
    simp [smul_smul, he, Matrix.fromBlocks_one]
  calc inFrame b w⁻¹ = inFrame b w⁻¹ * (inFrame b w * Matrix.fromBlocks 0 (e • 1) 1 0) := by rw [hWW, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.inFrame_inv_mul, Matrix.one_mul]

theorem incM_toBlocks {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E} :
    incM F M = Matrix.fromBlocks (incM F M.toBlocks₁₁) (incM F M.toBlocks₁₂) (incM F M.toBlocks₂₁)
      (incM F M.toBlocks₂₂) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  ext (i | i) (j | j) <;> rfl

theorem toBlocks₂₁_mul' {R : Type} [CommRing R] (X Z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    (X * Z).toBlocks₂₁ = X.toBlocks₂₁ * Z.toBlocks₁₁ + X.toBlocks₂₂ * Z.toBlocks₂₁ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks X, ← Matrix.fromBlocks_toBlocks Z]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁]

theorem conj_blocks {R : Type} [CommRing R] (a bb c d a' b' c' d' β : Matrix (Fin n) (Fin n) R) :
    Matrix.fromBlocks a bb c d * Matrix.fromBlocks 0 β 0 0 * Matrix.fromBlocks a' b' c' d' =
      Matrix.fromBlocks (a * β * c') (a * β * d') (c * β * c') (c * β * d') := by
  simp [Matrix.fromBlocks_multiply, Matrix.mul_assoc]

theorem det_one_add_rank_one {R : Type} [CommRing R] (v w : Fin n → R) (h : w ⬝ᵥ v = 0) :
    (1 + Matrix.vecMulVec v w).det = 1 := by
  rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow, h, add_zero]

theorem cells' (B : Base F E) (hB : B.IsGood σ) (hb : IsFrame2 σ Y b) {ε : ℤˣ} {w : G2 σ Y}
    (hw : inFrame b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0) (hnb : IsNMap b nb) (T : nF σ Y b)
    (hT : IsND T) (γ : G2 σ Y) (hγ : γ ∈ rat2 σ Y) :
    (∃ p ∈ par2 σ Y, p ∈ rat2 σ Y ∧ ∃ ν ∈ nF σ Y b, γ = p * (w * nb ν)) ∨
    (∃ β₀ : nA σ Y b, B.ψ (-(Algebra.trace (AF F) (AE F E) (T.1.1 * β₀.1).trace)) ≠ 1 ∧
      ∃ t, IsPar (γ * nb β₀ * γ⁻¹) t ∧ Matrix.GeneralLinearGroup.det t = 1) := by
  have hb0 := hb
  obtain ⟨⟨ε₀, hε₀⟩, t₀, ht₀⟩ := hb
  have hs := sigma_invol B hB
  set e : E := ((ε₀ : ℤ) : E) with he_def
  have he : e * e = 1 := by
    rw [he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hse : σ.toRingHom e = e := map_intCast _ _
  obtain ⟨M, hM, hMf⟩ := rat_frame hε₀ hγ
  obtain ⟨hMM', hM'M⟩ := frame_inv σ.toRingHom hs e he hse M hMf
  have hMi := inFrame_inv_of_rat hM hMM'
  by_cases hc : M.toBlocks₂₁.det ≠ 0
  · left
    have hblk : M.toBlocks₂₁ * (M.toBlocks₂₂.map σ.toRingHom)ᵀ +
        M.toBlocks₂₂ * (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ) = 0 := by
      have h1 := congrArg Matrix.toBlocks₂₁ hMM'
      conv_lhs at h1 => rw [← Matrix.fromBlocks_toBlocks M]
      rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁] at h1
      simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
        Matrix.toBlocks_fromBlocks₂₂] at h1
      rw [h1]; ext i j; simp [Matrix.toBlocks₂₁, Matrix.one_apply]
    have hν := herm_quot σ.toRingHom he _ _ hc hblk
    set νE := M.toBlocks₂₁⁻¹ * M.toBlocks₂₂ with hνE
    have hνA : (incM F νE)ᵀ = -((((ε₀ : ℤ) : AE F E)) • (incM F νE).map (cA σ)) := by
      rw [← incM_transpose', hν, incM_map_cA]
      ext i j; simp [incM, he_def]
    let ν : nA σ Y b := ⟨incM F νE, (mem_nA_iff hε₀ _).2 hνA⟩
    have hνF : ν ∈ nF σ Y b := mem_nF_iff.2 ⟨νE, rfl⟩
    have hwrat : w ∈ rat2 σ Y := rat_of_inFrame (M := jw n ((ε : ℤ) : E)) (by rw [hw, incM_jw, map_intCast]; rfl)
    refine ⟨γ * (w * nb ν)⁻¹, ?_, mul_mem hγ (inv_mem (mul_mem hwrat (nb_rat hnb hνF))), ν, hνF, by group⟩
    rw [mem_stabiliser_iff_frame_lower_block hb0, mul_inv_rev, ← nb_neg hnb, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul,
      GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hM, hnb, inFrame_w_inv hw, incM_toBlocks, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁]
    have hcd : incM F M.toBlocks₂₁ * incM F νE = incM F M.toBlocks₂₂ := by
      rw [← incM_mul', hνE, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hc), Matrix.one_mul]
    show _ = 0
    simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul]
    change incM F M.toBlocks₂₁ * -(incM F νE) + incM F M.toBlocks₂₂ = 0
    rw [Matrix.mul_neg, hcd, neg_add_cancel]
  · right
    push Not at hc
    obtain ⟨T', hT'⟩ := mem_nF_iff.1 T.2
    have hTh : T'ᵀ = -(e • T'.map σ.toRingHom) := by
      have h1 := (mem_nA_iff hε₀ T.1.1).1 T.1.2
      rw [hT'] at h1
      apply incM_inj (F := F)
      rw [incM_transpose', h1, incM_map_cA]
      ext i j; simp [incM, he_def]
    have hTd : T'.det ≠ 0 := by
      intro h0; apply hT
      show T.1.1.det = 0
      rw [hT', incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    have hda : e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ * M.toBlocks₁₁ + (M.toBlocks₁₁.map σ.toRingHom)ᵀ * M.toBlocks₂₁ = 0 := by
      have h1 := congrArg Matrix.toBlocks₂₁ hM'M
      rw [toBlocks₂₁_mul', Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂] at h1
      rw [h1]; ext i j; simp [Matrix.toBlocks₂₁, Matrix.one_apply]
    obtain ⟨β₁, hβh, hcβ, ⟨v, w', hvw, hvw0⟩, htr⟩ :=
      exists_beta σ.toRingHom hs e he hse M.toBlocks₁₁ M.toBlocks₂₁ _ hc hda T' hTh hTd
    have hx0 : Algebra.trace F E (2 : E) ≠ 0 := by
      rw [show (2 : E) = algebraMap F E 2 from (map_ofNat (algebraMap F E) 2).symm, Algebra.trace_algebraMap, nsmul_eq_mul]
      exact mul_ne_zero (Nat.cast_ne_zero.2 Module.finrank_pos.ne') two_ne_zero
    obtain ⟨l, hl⟩ := psi_moves hB.std _ hx0
    set Λ : AE F E := algebraMap (AF F) (AE F E) l with hΛ
    have hcΛ : cA σ Λ = Λ := (cA σ).commutes l
    have hβA : (Λ • incM F β₁)ᵀ = -((((ε₀ : ℤ) : AE F E)) • (Λ • incM F β₁).map (cA σ)) := by
      rw [Matrix.transpose_smul, ← incM_transpose', hβh]
      ext i j
      simp [incM, he_def, hcΛ, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR]
      ring
    let β₀ : nA σ Y b := ⟨Λ • incM F β₁, (mem_nA_iff hε₀ _).2 hβA⟩
    refine ⟨β₀, ?_, ?_⟩
    · have htt : Algebra.trace (AF F) (AE F E) (T.1.1 * β₀.1).trace = l * algebraMap F (AF F) (Algebra.trace F E 2) := by
        show Algebra.trace (AF F) (AE F E) (T.1.1 * (Λ • incM F β₁)).trace = _
        rw [hT', Matrix.mul_smul, Matrix.trace_smul, ← incM_mul', smul_eq_mul, hΛ, ← Algebra.smul_def,
          LinearMap.map_smul, tt_rat, htr, smul_eq_mul]
      rw [htt]; exact hl
    · set Z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E := Matrix.fromBlocks 0 β₁ 0 0 with hZ
      have hN : Matrix.fromBlocks 1 (β₀ : Matrix (Fin n) (Fin n) (AE F E)) 0 1 = 1 + Λ • incM F Z := by
        show Matrix.fromBlocks 1 (Λ • incM F β₁) 0 1 = _
        ext (i | i) (j | j) <;> simp [hZ, incM, Matrix.one_apply]
      have h1 : incM F M * incM F (Matrix.fromBlocks (M.toBlocks₂₂.map σ.toRingHom)ᵀ (e • (M.toBlocks₁₂.map σ.toRingHom)ᵀ)
          (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ) (M.toBlocks₁₁.map σ.toRingHom)ᵀ) = 1 := by
        rw [← incM_mul', hMM']; ext i j; simp [incM, Matrix.one_apply]
      have hX : M * Z * Matrix.fromBlocks (M.toBlocks₂₂.map σ.toRingHom)ᵀ (e • (M.toBlocks₁₂.map σ.toRingHom)ᵀ)
          (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ) (M.toBlocks₁₁.map σ.toRingHom)ᵀ =
          Matrix.fromBlocks (M.toBlocks₁₁ * β₁ * (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ))
            (M.toBlocks₁₁ * β₁ * (M.toBlocks₁₁.map σ.toRingHom)ᵀ)
            (M.toBlocks₂₁ * β₁ * (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ))
            (M.toBlocks₂₁ * β₁ * (M.toBlocks₁₁.map σ.toRingHom)ᵀ) := by
        conv_lhs => enter [1, 1]; rw [← Matrix.fromBlocks_toBlocks M]
        rw [hZ, conj_blocks]
      have hP : inFrame b (γ * nb β₀ * γ⁻¹) = 1 + Λ • incM F (M * Z *
          Matrix.fromBlocks (M.toBlocks₂₂.map σ.toRingHom)ᵀ (e • (M.toBlocks₁₂.map σ.toRingHom)ᵀ)
            (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ) (M.toBlocks₁₁.map σ.toRingHom)ᵀ) := by
        rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hM, hnb, hMi, hN, Matrix.mul_add,
          Matrix.mul_one, Matrix.add_mul, h1, Matrix.mul_smul, Matrix.smul_mul, incM_mul', incM_mul']
      have h21 : (inFrame b (γ * nb β₀ * γ⁻¹)).toBlocks₂₁ = 0 := by
        rw [hP, hX, hcβ]
        ext i j; simp [Matrix.toBlocks₂₁, Matrix.one_apply, incM]
      have h11 : (inFrame b (γ * nb β₀ * γ⁻¹)).toBlocks₁₁ = 1 + Λ • incM F (Matrix.vecMulVec v w') := by
        rw [hP, hX, hvw]
        ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply, incM]
      obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 ((mem_stabiliser_iff_frame_lower_block hb0 _).2 h21)
      have ht1 := ((isPar_frame ht₀ _ t).1 ht).2
      refine ⟨t, ht, Units.ext ?_⟩
      show t.1.det = 1
      have hdet : (1 + Λ • incM F (Matrix.vecMulVec v w')).det = 1 := by
        rw [show Λ • incM F (Matrix.vecMulVec v w') =
          Matrix.vecMulVec (fun i => Λ * inclR (F := F) (AF F) (v i)) (fun j => inclR (F := F) (AF F) (w' j)) by
            ext i j; simp [incM, Matrix.vecMulVec_apply, mul_assoc]]
        apply det_one_add_rank_one
        have : (fun j => inclR (F := F) (AF F) (w' j)) ⬝ᵥ (fun i => Λ * inclR (F := F) (AF F) (v i)) =
            Λ * inclR (F := F) (AF F) (w' ⬝ᵥ v) := by
          simp [dotProduct, Finset.mul_sum, map_sum, mul_left_comm]
        rw [this, hvw0, map_zero, mul_zero]
      rw [ht1, Matrix.det_mul, Matrix.det_mul, h11, hdet, mul_one, ← Matrix.det_mul, incM_GL_mul_inv, Matrix.det_one]

theorem mem_stabiliser_iff_lower_block_zero (hb : IsFrame2 σ Y b) (p : G2 σ Y) : p ∈ par2 σ Y ↔ (inFrame b p).toBlocks₂₁ = 0 :=
  mem_stabiliser_iff_frame_lower_block hb p

theorem big_inj (hb : IsFrame2 σ Y b) {ε : ℤˣ} {w : G2 σ Y}
    (hw : inFrame b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0) (hnb : IsNMap b nb) {ν ν' : nA σ Y b}
    (h : (w * nb ν) * (w * nb ν')⁻¹ ∈ par2 σ Y) : ν = ν' :=
  big_inj' hb hw hnb h

theorem cells (B : Base F E) (hB : B.IsGood σ) (hb : IsFrame2 σ Y b) {ε : ℤˣ} {w : G2 σ Y}
    (hw : inFrame b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0) (hnb : IsNMap b nb) (T : nF σ Y b)
    (hT : IsND T) (γ : G2 σ Y) (hγ : γ ∈ rat2 σ Y) :
    (∃ p ∈ par2 σ Y, p ∈ rat2 σ Y ∧ ∃ ν ∈ nF σ Y b, γ = p * (w * nb ν)) ∨
    (∃ β₀ : nA σ Y b, B.ψ (-(Algebra.trace (AF F) (AE F E) (T.1.1 * β₀.1).trace)) ≠ 1 ∧
      ∃ t, IsPar (γ * nb β₀ * γ⁻¹) t ∧ Matrix.GeneralLinearGroup.det t = 1) :=
  cells' B hB hb hw hnb T hT γ hγ

end PositivityTheory.SiegelWeilFormula.kunf

end

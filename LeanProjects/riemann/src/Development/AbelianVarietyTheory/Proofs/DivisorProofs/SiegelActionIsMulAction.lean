import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsMoreLast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapOfRealAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapOfRealOne
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory.SympUnivGroup

variable {g : ℕ}

def cx {m n : Type} (M : Matrix m n ℝ) : Matrix m n ℂ := M.map (fun t : ℝ => (t : ℂ))

theorem cx_mul {m n k : Type} [Fintype n] (M : Matrix m n ℝ) (N : Matrix n k ℝ) :
    cx (M * N) = cx M * cx N := by
  first
  | exact @_root_.GlobalTheory.RealEmbeddingLemmaFirst.main
  | exact _root_.GlobalTheory.RealEmbeddingLemmaFirst.main
  | (apply _root_.GlobalTheory.RealEmbeddingLemmaFirst.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RealEmbeddingLemmaFirst.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RealEmbeddingLemmaFirst.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RealEmbeddingLemmaFirst.main ..)

theorem cx_add {m n : Type} (M N : Matrix m n ℝ) : cx (M + N) = cx M + cx N := by
  first
  | exact @_root_.GlobalTheory.MapOfRealAdd.map_ofReal_add
  | exact _root_.GlobalTheory.MapOfRealAdd.map_ofReal_add
  | (apply _root_.GlobalTheory.MapOfRealAdd.map_ofReal_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.MapOfRealAdd.map_ofReal_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MapOfRealAdd.map_ofReal_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MapOfRealAdd.map_ofReal_add ..)

theorem cx_sub {m n : Type} (M N : Matrix m n ℝ) : cx (M - N) = cx M - cx N := by
  first
  | exact @_root_.GlobalTheory.RealEmbeddingLemmaSecond.main
  | exact _root_.GlobalTheory.RealEmbeddingLemmaSecond.main
  | (apply _root_.GlobalTheory.RealEmbeddingLemmaSecond.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RealEmbeddingLemmaSecond.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RealEmbeddingLemmaSecond.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RealEmbeddingLemmaSecond.main ..)

theorem cx_one {m : Type} [DecidableEq m] : cx (1 : Matrix m m ℝ) = 1 := by
  first
  | exact @_root_.GlobalTheory.MapOfRealOne.map_ofReal_one
  | exact _root_.GlobalTheory.MapOfRealOne.map_ofReal_one
  | (apply _root_.GlobalTheory.MapOfRealOne.map_ofReal_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.MapOfRealOne.map_ofReal_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MapOfRealOne.map_ofReal_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MapOfRealOne.map_ofReal_one ..)

theorem cx_zero {m n : Type} : cx (0 : Matrix m n ℝ) = 0 := by
  ext i j; simp [cx]

theorem cx_transpose {m n : Type} (M : Matrix m n ℝ) : cx Mᵀ = (cx M)ᵀ := by
  ext i j; simp [cx]

theorem cx_conjTranspose {m n : Type} (M : Matrix m n ℝ) : (cx M)ᴴ = cx Mᵀ := by
  ext i j; simp [cx]

theorem den_eq (γ : Sp g) (τ : Matrix (Fin g) (Fin g) ℂ) :
    den γ τ = cx γ.mat.toBlocks₂₁ * τ + cx γ.mat.toBlocks₂₂ := rfl

theorem moeb_eq (γ : Sp g) (τ : Matrix (Fin g) (Fin g) ℂ) :
    moeb γ τ = (cx γ.mat.toBlocks₁₁ * τ + cx γ.mat.toBlocks₁₂) * (den γ τ)⁻¹ := rfl

theorem rels (γ : Sp g) :
    (cx γ.mat.toBlocks₁₁)ᵀ * cx γ.mat.toBlocks₂₁ = (cx γ.mat.toBlocks₂₁)ᵀ * cx γ.mat.toBlocks₁₁ ∧
    (cx γ.mat.toBlocks₁₂)ᵀ * cx γ.mat.toBlocks₂₂ = (cx γ.mat.toBlocks₂₂)ᵀ * cx γ.mat.toBlocks₁₂ ∧
    (cx γ.mat.toBlocks₁₁)ᵀ * cx γ.mat.toBlocks₂₂ - (cx γ.mat.toBlocks₂₁)ᵀ * cx γ.mat.toBlocks₁₂ = 1 := by
  have h : γ.mat ∈ symplecticGroup (Fin g) ℝ := γ.2
  rw [← fromBlocks_toBlocks γ.mat] at h
  obtain ⟨h1, h2, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 h
  refine ⟨?_, ?_, ?_⟩
  · rw [← cx_transpose, ← cx_transpose, ← cx_mul, ← cx_mul, h1]
  · rw [← cx_transpose, ← cx_transpose, ← cx_mul, ← cx_mul, h2]
  · rw [← cx_transpose, ← cx_transpose, ← cx_mul, ← cx_mul, ← cx_sub, h3, cx_one]

section Skew
variable {A B C D : Matrix (Fin g) (Fin g) ℂ}

theorem skew (h1 : Aᵀ * C = Cᵀ * A) (h2 : Bᵀ * D = Dᵀ * B) (h3 : Aᵀ * D - Cᵀ * B = 1)
    (Y Z : Matrix (Fin g) (Fin g) ℂ) :
    (Y * Cᵀ + Dᵀ) * (A * Z + B) - (Y * Aᵀ + Bᵀ) * (C * Z + D) = Z - Y := by
  have h3' : Dᵀ * A - Bᵀ * C = 1 := by
    have := congrArg Matrix.transpose h3
    simpa [transpose_sub, transpose_mul] using this
  have e : (Y * Cᵀ + Dᵀ) * (A * Z + B) - (Y * Aᵀ + Bᵀ) * (C * Z + D) =
      Y * (Cᵀ * A - Aᵀ * C) * Z - Y * (Aᵀ * D - Cᵀ * B) + (Dᵀ * A - Bᵀ * C) * Z +
        (Dᵀ * B - Bᵀ * D) := by noncomm_ring
  rw [e, h1, h2, h3, h3']
  noncomm_ring

end Skew

theorem eq_zero_of_form {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) {v : Fin g → ℂ}
    (h : star v ⬝ᵥ (cx Y *ᵥ v) = 0) : v = 0 := by
  set x : Fin g → ℝ := fun i => (v i).re
  set y : Fin g → ℝ := fun i => (v i).im
  have hre : (star v ⬝ᵥ (cx Y *ᵥ v)).re = x ⬝ᵥ (Y *ᵥ x) + y ⬝ᵥ (Y *ᵥ y) := by
    simp only [dotProduct, mulVec, cx, Matrix.map_apply, Pi.star_apply, Complex.re_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib, x, y]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im] <;> ring
  rw [h, Complex.zero_re] at hre
  have hx := hY.posSemidef.dotProduct_mulVec_nonneg x
  have hy := hY.posSemidef.dotProduct_mulVec_nonneg y
  simp only [star_trivial] at hx hy
  have hx0 : x = 0 := by
    by_contra hne
    have := hY.dotProduct_mulVec_pos hne
    simp only [star_trivial] at this
    linarith
  have hy0 : y = 0 := by
    by_contra hne
    have := hY.dotProduct_mulVec_pos hne
    simp only [star_trivial] at this
    linarith
  funext i
  apply Complex.ext
  · exact congrFun hx0 i
  · exact congrFun hy0 i

end GlobalTheory.SympUnivGroup

namespace GlobalTheory.SympUnivGroup

variable {g : ℕ}

theorem det_den_ne (γ : Sp g) {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : IsSiegel τ) :
    (den γ τ).det ≠ 0 := by
  obtain ⟨h1, h2, h3⟩ := rels γ
  intro h0
  obtain ⟨v, hv, hq⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hs := skew h1 h2 h3 τᴴ τ
  have hD : (den γ τ)ᴴ = τᴴ * (cx γ.mat.toBlocks₂₁)ᵀ + (cx γ.mat.toBlocks₂₂)ᵀ := by
    rw [den_eq, conjTranspose_add, conjTranspose_mul, cx_conjTranspose, cx_conjTranspose,
      cx_transpose, cx_transpose]
  have hN : (cx γ.mat.toBlocks₁₁ * τ + cx γ.mat.toBlocks₁₂)ᴴ =
      τᴴ * (cx γ.mat.toBlocks₁₁)ᵀ + (cx γ.mat.toBlocks₁₂)ᵀ := by
    rw [conjTranspose_add, conjTranspose_mul, cx_conjTranspose, cx_conjTranspose,
      cx_transpose, cx_transpose]
  rw [← hD, ← hN, ← den_eq] at hs
  have hz : star v ⬝ᵥ ((τ - τᴴ) *ᵥ v) = 0 := by
    rw [← hs, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hq, mulVec_zero, sub_zero,
      dotProduct_mulVec, ← star_mulVec, hq]
    simp
  have hY : τ - τᴴ = (2 * Complex.I) • cx (τ.map Complex.im) := by
    ext i j
    have hij : τ j i = τ i j := by simpa using congrFun (congrFun hτ.1 i) j
    simp only [Matrix.sub_apply, conjTranspose_apply, hij, Matrix.smul_apply, cx, map_apply, smul_eq_mul]
    apply Complex.ext <;> simp [hij] <;> ring
  rw [hY, smul_mulVec, dotProduct_smul, smul_eq_mul, mul_eq_zero] at hz
  rcases hz with hz | hz
  · norm_num [Complex.ext_iff] at hz
  · exact hv (eq_zero_of_form hτ.2 hz)

theorem moeb_symm (γ : Sp g) {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm)
    (hd : (den γ τ).det ≠ 0) : (moeb γ τ).IsSymm := by
  obtain ⟨h1, h2, h3⟩ := rels γ
  have hs := skew h1 h2 h3 τ τ
  rw [sub_self, sub_eq_zero] at hs
  have hτ' : τᵀ = τ := hτ
  have hD : (den γ τ)ᵀ = τ * (cx γ.mat.toBlocks₂₁)ᵀ + (cx γ.mat.toBlocks₂₂)ᵀ := by
    rw [den_eq, transpose_add, transpose_mul, hτ']
  have hN : (cx γ.mat.toBlocks₁₁ * τ + cx γ.mat.toBlocks₁₂)ᵀ =
      τ * (cx γ.mat.toBlocks₁₁)ᵀ + (cx γ.mat.toBlocks₁₂)ᵀ := by
    rw [transpose_add, transpose_mul, hτ']
  rw [← hD, ← hN, ← den_eq] at hs

  have hu : IsUnit (den γ τ).det := Ne.isUnit hd
  have hut : IsUnit (den γ τ)ᵀ.det := by rwa [det_transpose]
  show (moeb γ τ)ᵀ = moeb γ τ
  rw [moeb_eq, transpose_mul, transpose_nonsing_inv]
  set D := den γ τ
  set N := cx γ.mat.toBlocks₁₁ * τ + cx γ.mat.toBlocks₁₂
  calc Dᵀ⁻¹ * Nᵀ = Dᵀ⁻¹ * (Nᵀ * D) * D⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = Dᵀ⁻¹ * (Dᵀ * N) * D⁻¹ := by rw [hs]
    _ = N * D⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hut, Matrix.one_mul]

theorem blocks_mul (γ γ' : Sp g) :
    (γ * γ').mat.toBlocks₁₁ = γ.mat.toBlocks₁₁ * γ'.mat.toBlocks₁₁ + γ.mat.toBlocks₁₂ * γ'.mat.toBlocks₂₁ ∧
    (γ * γ').mat.toBlocks₁₂ = γ.mat.toBlocks₁₁ * γ'.mat.toBlocks₁₂ + γ.mat.toBlocks₁₂ * γ'.mat.toBlocks₂₂ ∧
    (γ * γ').mat.toBlocks₂₁ = γ.mat.toBlocks₂₁ * γ'.mat.toBlocks₁₁ + γ.mat.toBlocks₂₂ * γ'.mat.toBlocks₂₁ ∧
    (γ * γ').mat.toBlocks₂₂ = γ.mat.toBlocks₂₁ * γ'.mat.toBlocks₁₂ + γ.mat.toBlocks₂₂ * γ'.mat.toBlocks₂₂ := by
  have h : (γ * γ').mat = γ.mat * γ'.mat := rfl
  rw [← fromBlocks_toBlocks γ.mat, ← fromBlocks_toBlocks γ'.mat, fromBlocks_multiply] at h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [h] <;> simp

theorem den_mul (γ γ' : Sp g) {τ : Matrix (Fin g) (Fin g) ℂ} (hd : (den γ' τ).det ≠ 0) :
    den (γ * γ') τ = den γ (moeb γ' τ) * den γ' τ := by
  obtain ⟨-, -, m3, m4⟩ := blocks_mul γ γ'
  have hW : moeb γ' τ * den γ' τ = cx γ'.mat.toBlocks₁₁ * τ + cx γ'.mat.toBlocks₁₂ := by
    rw [moeb_eq, Matrix.mul_assoc, nonsing_inv_mul _ (Ne.isUnit hd), Matrix.mul_one]
  have e : den γ (moeb γ' τ) * den γ' τ =
      cx γ.mat.toBlocks₂₁ * (moeb γ' τ * den γ' τ) + cx γ.mat.toBlocks₂₂ * den γ' τ := by
    rw [den_eq γ (moeb γ' τ), Matrix.add_mul, Matrix.mul_assoc]
  rw [den_eq (γ * γ'), m3, m4, cx_add, cx_add, cx_mul, cx_mul, cx_mul, cx_mul, e, hW, den_eq γ']
  noncomm_ring

theorem moeb_mul (γ γ' : Sp g) {τ : Matrix (Fin g) (Fin g) ℂ} (hd : (den γ' τ).det ≠ 0) :
    moeb (γ * γ') τ = moeb γ (moeb γ' τ) := by
  obtain ⟨m1, m2, -, -⟩ := blocks_mul γ γ'
  have hW : moeb γ' τ * den γ' τ = cx γ'.mat.toBlocks₁₁ * τ + cx γ'.mat.toBlocks₁₂ := by
    rw [moeb_eq, Matrix.mul_assoc, nonsing_inv_mul _ (Ne.isUnit hd), Matrix.mul_one]
  have hnum : cx (γ * γ').mat.toBlocks₁₁ * τ + cx (γ * γ').mat.toBlocks₁₂ =
      (cx γ.mat.toBlocks₁₁ * moeb γ' τ + cx γ.mat.toBlocks₁₂) * den γ' τ := by
    have e : (cx γ.mat.toBlocks₁₁ * moeb γ' τ + cx γ.mat.toBlocks₁₂) * den γ' τ =
        cx γ.mat.toBlocks₁₁ * (moeb γ' τ * den γ' τ) + cx γ.mat.toBlocks₁₂ * den γ' τ := by
      rw [Matrix.add_mul, Matrix.mul_assoc]
    rw [m1, m2, cx_add, cx_add, cx_mul, cx_mul, cx_mul, cx_mul, e, hW, den_eq γ']
    noncomm_ring
  rw [moeb_eq (γ * γ'), hnum, den_mul γ γ' hd, Matrix.mul_inv_rev, Matrix.mul_assoc,
    ← Matrix.mul_assoc (den γ' τ), mul_nonsing_inv _ (Ne.isUnit hd), Matrix.one_mul]
  rfl

theorem tauU_symPart {A : Matrix (Fin g) (Fin g) ℂ} (hA : A.IsSymm) : tauU (symPart A) = A := by
  ext i j
  have hij : A j i = A i j := by simpa using congrFun (congrFun hA i) j
  simp [tauU, symPart, hij]

theorem symPart_tauU (s : symMat g) : symPart (tauU s) = s := by
  apply Subtype.ext
  funext i j
  have hij : s.1 j i = s.1 i j := (s.2 i j).symm
  simp [tauU, symPart, hij]

theorem group_action : ∀ g : ℕ, (∀ P ∈ cov (siegel g) g, actU 1 P = P) ∧
    (∀ γ γ' : Sp g, ∀ P ∈ cov (siegel g) g, actU (γ * γ') P = actU γ (actU γ' P)) := by
  intro g
  refine ⟨fun P _ => ?_, fun γ γ' P hP => ?_⟩
  · have h1 : (1 : Sp g).mat = 1 := rfl
    have b11 : (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ).toBlocks₁₁ = 1 := by
      ext i j; simp [toBlocks₁₁, one_apply]
    have b12 : (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ).toBlocks₁₂ = 0 := by
      ext i j; simp [toBlocks₁₂, one_apply]
    have b21 : (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ).toBlocks₂₁ = 0 := by
      ext i j; simp [toBlocks₂₁, one_apply]
    have b22 : (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ).toBlocks₂₂ = 1 := by
      ext i j; simp [toBlocks₂₂, one_apply]
    have hden : den 1 (tauU P.1) = 1 := by
      rw [den_eq, h1, b21, b22, cx_zero, cx_one, Matrix.zero_mul, zero_add]
    have hmoeb : moeb 1 (tauU P.1) = tauU P.1 := by
      rw [moeb_eq, hden, h1, b11, b12, cx_zero, cx_one, Matrix.one_mul, add_zero, inv_one,
        Matrix.mul_one]
    simp only [actU, hmoeb, hden, inv_one, vecMul_one, symPart_tauU]
  · have hτ : IsSiegel (tauU P.1) := hP.1
    have hd := det_den_ne γ' hτ
    have hsym := moeb_symm γ' hτ.1 hd
    simp only [actU, tauU_symPart hsym, moeb_mul γ γ' hd, den_mul γ γ' hd, vecMul_vecMul,
      Matrix.mul_inv_rev]

end GlobalTheory.SympUnivGroup

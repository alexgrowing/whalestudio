import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicWitt

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory GlobalTheory.SWLit

namespace GlobalTheory.SWLit.WittModel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem blk_mul {R : Type} [CommRing R] (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk a b c d * blk a' b' c' d' = blk (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blk_one {R : Type} [CommRing R] : (blk 1 0 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  simp only [blk, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

omit [NumberField F] [NumberField E] in

theorem gram_of_isWittBasis (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} {l : E} (hl : l ≠ 0)
    (hJ : ∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) {T : GL (Fin (n + n)) E} (h : IsWittBasis σ J l T) :
    T.1ᵀ * (l⁻¹ • dblGram finSumFinEquiv J) * T.1.map σ = blk 0 1 (-1) 0 := by
  obtain ⟨Z, hZ, hT⟩ := h
  set S := l⁻¹ • J with hS
  have h1 : S * Z.map σ + S * Z.map σ = 1 := by
    rw [hS, Matrix.smul_mul, ← smul_add, ← two_smul E, hZ, smul_smul, inv_mul_cancel₀ hl, one_smul]
  have hs : (S.map σ)ᵀ = -S := by ext i j; exact hJ i j
  have h2 : Zᵀ * S + Zᵀ * S = -1 := by
    have := congrArg (fun X : Matrix (Fin n) (Fin n) E => (X.map σ)ᵀ) h1
    have hz : (Z.map σ).map σ = Z := by ext i j; exact hσ _
    simp only [Matrix.map_add _ (map_add σ), Matrix.transpose_add, Matrix.map_mul, Matrix.transpose_mul, hz, hs,
      Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one, Matrix.mul_neg] at this
    rw [← this]; abel
  have e1 : l⁻¹ • dblGram finSumFinEquiv J = blk S 0 0 (-S) := by
    ext i j
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
      simp only [dblGram, blkMat, blk, Matrix.smul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, hS,
        Matrix.neg_apply, Matrix.zero_apply, smul_zero, smul_neg]
  have e2 : (blk 1 Z 1 (-Z))ᵀ = blk 1 1 Zᵀ (-Zᵀ) := by
    simp only [blk, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_neg]
  have e3 : (blk 1 Z 1 (-Z)).map σ = blk 1 (Z.map σ) 1 (-Z.map σ) := by
    simp only [blk, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_one _ (map_zero σ) (map_one σ),
      Matrix.map_neg _ (map_neg σ)]
  rw [hT, e1, e2, e3, blk_mul, blk_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
    add_neg_cancel, h1, h2]

omit [NumberField E] in

theorem exists_weyl (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} {l : E} (hl : l ≠ 0)
    (hJ : ∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (h₂ : J₂ = dblGram finSumFinEquiv J) {T : GL (Fin (n + n)) E} (h : IsWittBasis σ J l T) :
    ∃ w ∈ ratU σ J₂, inBasis σ T w = blk 0 1 (-1) 0 := by
  have hG := gram_of_isWittBasis hσ hl hJ h
  rw [← h₂] at hG
  have hm : (blk 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) E) * blk 0 (-1) 1 0 = 1 := by
    rw [blk_mul, ← blk_one]; simp
  let w₀ : GL (Fin (n + n)) E := ⟨_, _, hm, mul_eq_one_comm.1 hm⟩
  have mp : ∀ {S : Type} [CommRing S] (f : E →+* S),
      (blk 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) E).map f = blk 0 1 (-1) 0 := fun f => by
    simp only [blk, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_one _ (map_zero f) (map_one f),
      Matrix.map_neg _ (map_neg f), Matrix.map_zero _ (map_zero f)]
  have hw : w₀.1ᵀ * w₀.1 * w₀.1.map σ = w₀.1 := by
    have e : w₀.1ᵀ = blk 0 (-1) 1 0 := by
      simp only [w₀, blk, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, Matrix.transpose_one,
        Matrix.transpose_neg, Matrix.transpose_zero]
    have e' : w₀.1.map σ = w₀.1 := mp (σ : E →+* E)
    rw [e, e', show blk 0 (-1) 1 0 * w₀.1 = 1 from mul_eq_one_comm.1 hm, Matrix.one_mul]
  have hT : T.1ᵀ * J₂ * T.1.map σ = l • w₀.1 := by
    change _ = l • blk 0 1 (-1) 0
    rw [← hG, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hl, one_smul]
  have i1 : (T⁻¹).1ᵀ * T.1ᵀ = 1 := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have i2 : T.1.map σ * (T⁻¹).1.map σ = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have key : (T * w₀ * T⁻¹).1ᵀ * J₂ * (T * w₀ * T⁻¹).1.map σ = J₂ := by
    calc _ = (T⁻¹).1ᵀ * (w₀.1ᵀ * (T.1ᵀ * J₂ * T.1.map σ) * w₀.1.map σ) * (T⁻¹).1.map σ := by
          simp only [Units.val_mul, Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = (T⁻¹).1ᵀ * (T.1ᵀ * J₂ * T.1.map σ) * (T⁻¹).1.map σ := by
          rw [hT, Matrix.mul_smul, Matrix.smul_mul, hw]
      _ = ((T⁻¹).1ᵀ * T.1ᵀ) * J₂ * (T.1.map σ * (T⁻¹).1.map σ) := by simp only [Matrix.mul_assoc]
      _ = J₂ := by rw [i1, i2, Matrix.one_mul, Matrix.mul_one]
  refine ⟨⟨Matrix.GeneralLinearGroup.map (inclR (AF F)) (T * w₀ * T⁻¹), ?_⟩, ⟨_, rfl⟩, ?_⟩
  · have := congrArg (fun X => incM F X) key
    simp only [incM, Matrix.map_mul, Matrix.transpose_map] at this
    refine Eq.trans ?_ this
    congr 1
  · change incM F (T⁻¹).1 * incM F (T * w₀ * T⁻¹).1 * incM F T.1 = _
    rw [incM, incM, incM, ← Matrix.map_mul, ← Matrix.map_mul, ← Units.val_mul, ← Units.val_mul,
      show T⁻¹ * (T * w₀ * T⁻¹) * T = w₀ by group]
    exact mp _

theorem exists_data (h : IsCMExt F E σ) (n m : ℕ) :
    ∃ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (T : GL (Fin (n + n)) E),
      l ≠ 0 ∧ IsHermND σ (l • JV) ∧ (∀ x, form σ JV x x = 0 → x = 0) ∧
      (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) ∧ IsWittBasis σ J l T := by
  obtain ⟨a, ha, ha'⟩ := exists_integer_conj_eq_neg h
  have ha0 : (a : E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 ha
  generalize (a : E) = b at ha' ha0
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  let Z : Matrix (Fin n) (Fin n) E := (-(b / 2)) • 1
  have hT : blk 1 Z 1 (-Z) * blk ((2 : E)⁻¹ • 1) ((2 : E)⁻¹ • 1) ((-b⁻¹) • 1) (b⁻¹ • 1) = 1 := by
    rw [blk_mul, ← blk_one]
    congr 1 <;> simp only [Z, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul] <;>
      match_scalars <;> field_simp <;> ring
  let T : GL (Fin (n + n)) E := ⟨_, _, hT, mul_eq_one_comm.1 hT⟩
  refine ⟨b, b • 1, 1, T, ha0, ⟨fun i j => ?_, ?_⟩, fun x hx => funext fun i => ?_, fun i j => ?_, Z, ?_, rfl⟩
  · by_cases e : i = j
    · subst e; simp [ha']
    · simp [e, Ne.symm e]
  · simp [smul_smul, ha0]
  · obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    rw [form, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_zero] at hx
    have h1 := congrArg (fun z => (w.embedding z).re) (hx.resolve_left ha0)
    simp only [dotProduct, map_sum, map_mul, h.2.2.2, Complex.star_def, Complex.mul_conj, Complex.re_sum,
      Complex.ofReal_re, map_zero, Complex.zero_re] at h1
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => Complex.normSq_nonneg _).1 h1 i (Finset.mem_univ i)
    simpa using h2
  · by_cases e : i = j
    · subst e; simp [ha', inv_neg]
    · simp [e, Ne.symm e]
  · ext i j
    by_cases e : i = j
    · subst e; simp [Z, ha', map_ofNat]; field_simp
    · simp [Z, e]

end GlobalTheory.SWLit.WittModel

end

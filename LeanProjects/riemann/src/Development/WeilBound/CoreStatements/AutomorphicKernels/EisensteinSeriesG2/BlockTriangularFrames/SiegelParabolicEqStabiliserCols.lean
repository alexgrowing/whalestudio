import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE

set_option linter.unusedSectionVars false

noncomputable section

namespace SiegelEisensteinSeries.Grp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

section Matrix

variable {m R : Type*} [Fintype m] [DecidableEq m] [CommRing R] {b : m → ℕ}

def blkDiag (b : m → ℕ) (M : Matrix m m R) : Matrix m m R := fun i j => if b i = b j then M i j else 0

theorem blkDiag_one : blkDiag b (1 : Matrix m m R) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [blkDiag]
  · simp [blkDiag, Matrix.one_apply_ne h]

theorem blkDiag_mul {M N : Matrix m m R} (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) :
    blkDiag b (M * N) = blkDiag b M * blkDiag b N := by
  ext i j
  simp only [blkDiag, Matrix.mul_apply]
  by_cases h : b i = b j
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hik : b i = b k
    · rw [if_pos hik, if_pos (hik ▸ h)]
    · rw [if_neg hik, zero_mul]
      rcases lt_or_gt_of_ne hik with hlt | hgt
      · rw [hN (show b j < b k from h ▸ hlt), mul_zero]
      · rw [hM hgt, zero_mul]
  · rw [if_neg h]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : b i = b k
    · rw [if_pos hik, if_neg (fun hkj => h (hik.trans hkj)), mul_zero]
    · rw [if_neg hik, zero_mul]

theorem uniCond_iff (M : Matrix m m R) :
    (∀ i j, b j ≤ b i → M i j = (1 : Matrix m m R) i j) ↔ M.BlockTriangular b ∧ blkDiag b M = 1 := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, ?_⟩
    · rw [h i j hij.le, Matrix.one_apply_ne (fun e => (e ▸ hij).false)]
    · ext i j
      simp only [blkDiag]
      split_ifs with hij
      · exact h i j hij.ge
      · rw [Matrix.one_apply_ne (fun e => hij (by rw [e]))]
  · rintro ⟨hM, hD⟩ i j hij
    rcases hij.lt_or_eq with hlt | heq
    · rw [hM hlt, Matrix.one_apply_ne (fun e => (e ▸ hlt).false)]
    · have := congrFun (congrFun hD i) j
      simp only [blkDiag, if_pos heq.symm] at this
      exact this

end Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n}

theorem incM_mul_inv (b : GL (Fin n ⊕ Fin n) E) : incM F b.1 * incM F (b⁻¹).1 = 1 := by
  simp only [incM]
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem incM_inv_mul (b : GL (Fin n ⊕ Fin n) E) : incM F (b⁻¹).1 * incM F b.1 = 1 := by
  simp only [incM]
  rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem inFrame_mul (b : GL (Fin n ⊕ Fin n) E) (x y : G2 σ Y) : inFrame b (x * y) = inFrame b x * inFrame b y := by
  unfold inFrame
  rw [show mat2 (x * y) = mat2 x * mat2 y from rfl]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F b.1) (incM F (b⁻¹).1), incM_mul_inv, Matrix.one_mul]

theorem inFrame_one (b : GL (Fin n ⊕ Fin n) E) : inFrame (σ := σ) (Y := Y) b 1 = 1 := by
  unfold inFrame
  rw [show mat2 (1 : G2 σ Y) = 1 from rfl, Matrix.mul_one, incM_inv_mul]

theorem inFrame_inv_mul (b : GL (Fin n ⊕ Fin n) E) (x : G2 σ Y) : inFrame b x⁻¹ * inFrame b x = 1 := by
  rw [← inFrame_mul, inv_mul_cancel, inFrame_one]

theorem inFrame_mul_inv (b : GL (Fin n ⊕ Fin n) E) (x : G2 σ Y) : inFrame b x * inFrame b x⁻¹ = 1 := by
  rw [← inFrame_mul, mul_inv_cancel, inFrame_one]

theorem matrix_eq_frame_conjugate (b : GL (Fin n ⊕ Fin n) E) (x : G2 σ Y) : mat2 x = incM F b.1 * inFrame b x * incM F (b⁻¹).1 := by
  unfold inFrame
  simp only [Matrix.mul_assoc]
  rw [incM_mul_inv, Matrix.mul_one, ← Matrix.mul_assoc, incM_mul_inv, Matrix.one_mul]

theorem blockTriangular_inFrame_inv (b : GL (Fin n ⊕ Fin n) E) {β : Type*} [LinearOrder β] {lv : Fin n ⊕ Fin n → β}
    {x : G2 σ Y} (hx : (inFrame b x).BlockTriangular lv) : (inFrame b x⁻¹).BlockTriangular lv := by
  let _ : Invertible (inFrame b x) := invertibleOfLeftInverse _ _ (inFrame_inv_mul b x)
  have := Matrix.blockTriangular_inv_of_blockTriangular hx
  rwa [Matrix.inv_eq_left_inv (inFrame_inv_mul b x)] at this

def below (S : Finset (Fin n)) (i : Fin n) : ℕ := (S.filter (· < i)).card

def lev (S : Finset (Fin n)) : Fin n ⊕ Fin n → ℕ
  | Sum.inl i => below S i
  | Sum.inr i => 2 * S.card - below S i

variable (σ Y) in

def parS (b : GL (Fin n ⊕ Fin n) E) (S : Finset (Fin n)) : Subgroup (G2 σ Y) where
  carrier := {g | (inFrame b g).BlockTriangular (lev S)}
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq, inFrame_mul] at *
    exact hx.mul hy
  one_mem' := by
    simp only [Set.mem_ofPred_eq, inFrame_one]
    exact Matrix.blockTriangular_one
  inv_mem' := fun {x} hx => blockTriangular_inFrame_inv b hx

theorem mem_parS {b : GL (Fin n ⊕ Fin n) E} {S : Finset (Fin n)} {g : G2 σ Y} :
    g ∈ parS σ Y b S ↔ (inFrame b g).BlockTriangular (lev S) := Iff.rfl

variable (σ Y) in

def uniS (b : GL (Fin n ⊕ Fin n) E) (S : Finset (Fin n)) : Subgroup (G2 σ Y) where
  carrier := {g | ∀ i j, lev S j ≤ lev S i → inFrame b g i j = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) i j}
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq, uniCond_iff, inFrame_mul] at *
    exact ⟨hx.1.mul hy.1, by rw [blkDiag_mul hx.1 hy.1, hx.2, hy.2, Matrix.one_mul]⟩
  one_mem' := by
    simp [inFrame_one]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_ofPred_eq, uniCond_iff] at *
    have h1 := blockTriangular_inFrame_inv b hx.1
    refine ⟨h1, ?_⟩
    have := blkDiag_mul h1 hx.1
    rw [inFrame_inv_mul, blkDiag_one, hx.2, Matrix.mul_one] at this
    exact this.symm

section Siegel

variable {R : Type*} [CommRing R]

def iota1 (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n) R :=
  Matrix.of fun r c => if r = Sum.inl c then 1 else 0

theorem mul_iota1_of_lowerLeft {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (h : ∀ i j, M (Sum.inr i) (Sum.inl j) = 0) :
    M * iota1 R n = iota1 R n * M.toBlocks₁₁ := by
  ext r c
  rcases r with r | r <;> simp [iota1, Matrix.mul_apply, Matrix.toBlocks₁₁, h]

theorem block_inclusion_left_cancel {C C' : Matrix (Fin n) (Fin n) R} (h : iota1 R n * C = iota1 R n * C') : C = C' := by
  ext i j
  have := congrFun (congrFun h (Sum.inl i)) j
  simpa [iota1, Matrix.mul_apply] using this

end Siegel

def siegelS (hn : 0 < n) : Finset (Fin n) := {⟨n - 1, by omega⟩}

theorem below_siegelS (hn : 0 < n) (i : Fin n) : below (siegelS hn) i = 0 := by
  unfold below siegelS
  rw [Finset.filter_singleton, if_neg]
  · rfl
  · simp only [Fin.lt_def]
    omega

theorem lev_siegelS_inl (hn : 0 < n) (i : Fin n) : lev (siegelS hn) (Sum.inl i) = 0 := below_siegelS hn i

theorem lev_siegelS_inr (hn : 0 < n) (i : Fin n) : lev (siegelS hn) (Sum.inr i) = 2 := by
  show 2 * (siegelS hn).card - below (siegelS hn) i = 2
  rw [below_siegelS]
  simp [siegelS]

theorem mem_parS_siegelS {b : GL (Fin n ⊕ Fin n) E} (hn : 0 < n) {g : G2 σ Y} :
    g ∈ parS σ Y b (siegelS hn) ↔ ∀ i j, inFrame b g (Sum.inr i) (Sum.inl j) = 0 := by
  rw [mem_parS]
  constructor
  · intro h i j
    exact h (by rw [lev_siegelS_inl, lev_siegelS_inr]; omega)
  · intro h r s hrs
    rcases r with r | r <;> rcases s with s | s <;>
      simp only [lev_siegelS_inl, lev_siegelS_inr] at hrs <;> first | omega | exact h r s

theorem isPar_iff {p : G2 σ Y} {t : GL (Fin n) (AE F E)} :
    IsPar p t ↔ mat2 p * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (t : Matrix (Fin n) (Fin n) (AE F E)) := Iff.rfl

theorem incM_diagCols :
    (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E).map (inclR (F := F) (E := E) (AF F)) = diagCols (Fin n) := by
  ext r c
  rcases r with r | r <;> simp [diagCols, Matrix.one_apply]

theorem frame_cols {b : GL (Fin n ⊕ Fin n) E} {t0 : GL (Fin n) E}
    (hb : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) * (t0.1 : Matrix (Fin n) (Fin n) E)) :
    incM F b.1 * iota1 (AE F E) n = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * incM F t0.1 := by
  have h1 : incM F b.1 * iota1 (AE F E) n = (b.1.toCols₁).map (inclR (F := F) (E := E) (AF F)) := by
    ext r c
    simp [incM, iota1, Matrix.mul_apply, Matrix.toCols₁]
  rw [h1, hb, Matrix.map_mul, incM_diagCols]
  rfl

abbrev glA (t0 : GL (Fin n) E) : GL (Fin n) (AE F E) := Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) t0

theorem glA_coe (t0 : GL (Fin n) E) : ((glA (F := F) t0 : GL (Fin n) (AE F E)) : Matrix _ _ _) = incM F t0.1 := rfl

theorem glA_coe_inv (t0 : GL (Fin n) E) :
    incM F t0.1 * (((glA (F := F) t0)⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = 1 := by
  rw [← glA_coe, Units.mul_inv]

theorem diagCols_eq {b : GL (Fin n ⊕ Fin n) E} {t0 : GL (Fin n) E}
    (hb : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) * (t0.1 : Matrix (Fin n) (Fin n) E)) :
    (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) =
      incM F b.1 * iota1 (AE F E) n * (((glA (F := F) t0)⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) := by
  rw [frame_cols hb, Matrix.mul_assoc, glA_coe_inv, Matrix.mul_one]

theorem isPar_of_mem_siegelS {b : GL (Fin n ⊕ Fin n) E} {t0 : GL (Fin n) E}
    (hb : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) * (t0.1 : Matrix (Fin n) (Fin n) E))
    (hn : 0 < n) {p : G2 σ Y} (hp : p ∈ parS σ Y b (siegelS hn)) :
    ∃ t : GL (Fin n) (AE F E), IsPar p t ∧
      ((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) = (inFrame b p).toBlocks₁₁.det := by
  have hp' : p⁻¹ ∈ parS σ Y b (siegelS hn) := inv_mem hp
  have hM := mul_iota1_of_lowerLeft ((mem_parS_siegelS hn).1 hp)
  have hM' := mul_iota1_of_lowerLeft ((mem_parS_siegelS hn).1 hp')
  have hAA : (inFrame b p).toBlocks₁₁ * (inFrame b p⁻¹).toBlocks₁₁ = 1 := by
    refine block_inclusion_left_cancel ?_
    rw [Matrix.mul_one, ← Matrix.mul_assoc, ← hM, Matrix.mul_assoc, ← hM', ← Matrix.mul_assoc, inFrame_mul_inv,
      Matrix.one_mul]
  have hAA' : (inFrame b p⁻¹).toBlocks₁₁ * (inFrame b p).toBlocks₁₁ = 1 := by
    refine block_inclusion_left_cancel ?_
    rw [Matrix.mul_one, ← Matrix.mul_assoc, ← hM', Matrix.mul_assoc, ← hM, ← Matrix.mul_assoc, inFrame_inv_mul,
      Matrix.one_mul]
  let Au : GL (Fin n) (AE F E) := ⟨(inFrame b p).toBlocks₁₁, (inFrame b p⁻¹).toBlocks₁₁, hAA, hAA'⟩
  refine ⟨glA (F := F) t0 * Au * (glA (F := F) t0)⁻¹, ?_, ?_⟩
  · rw [isPar_iff, matrix_eq_frame_conjugate b p, diagCols_eq hb]
    simp only [Units.val_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incM F (b⁻¹).1) (incM F b.1), incM_inv_mul, Matrix.one_mul,
      ← Matrix.mul_assoc (inFrame b p) (iota1 (AE F E) n), hM, Matrix.mul_assoc,
      ← Matrix.mul_assoc (((glA (F := F) t0)⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) ((glA (F := F) t0 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)), Units.inv_mul,
      Matrix.one_mul]
  · rw [map_mul, map_mul, mul_comm (Matrix.GeneralLinearGroup.det (glA (F := F) t0)), mul_assoc, map_inv, mul_inv_cancel, mul_one,
      Matrix.GeneralLinearGroup.val_det_apply]

structure IsHS (b : GL (Fin n ⊕ Fin n) E) (S : Finset (Fin n)) (K : Subgroup (G2 σ Y)) (H : G2 σ Y → Fin S.card → ℝ) :
    Prop where
  iwa : ∀ x : G2 σ Y, ∃ p ∈ parS σ Y b S, ∃ k ∈ K, x = p * k
  val : ∀ p ∈ parS σ Y b S, ∀ k ∈ K, ∀ (ℓ : Fin S.card) (u : (AE F E)ˣ),
    (u : AE F E) = ((inFrame b p).toSquareBlock (lev S) (ℓ : ℕ)).det → H (p * k) ℓ = Real.log (absE F E u)

def siegelLevelZeroEquiv (hn : 0 < n) : Fin n ≃ {a : Fin n ⊕ Fin n // lev (siegelS hn) a = 0} where
  toFun i := ⟨Sum.inl i, lev_siegelS_inl hn i⟩
  invFun a := Sum.elim id (fun _ => ⟨0, hn⟩) a.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨a | a, h⟩
    · rfl
    · rw [lev_siegelS_inr] at h
      exact absurd h (by norm_num)

open scoped Classical in
variable (F) in

def archInf : ℝ →+* InfiniteAdeleRing F :=
  RingHom.pi fun v => if h : v.IsReal then (InfinitePlace.Completion.ringEquivRealOfIsReal h).symm.toRingHom
    else (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.1 h)).symm.toRingHom.comp Complex.ofRealHom

variable (F) in

def archA (r : ℝ) : AF F := ((archInf F r, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

theorem archA_mul (r s : ℝ) : archA F (r * s) = archA F r * archA F s :=
  Prod.ext (map_mul (archInf F) r s) (mul_one 1).symm

theorem archA_one : archA F 1 = 1 :=
  Prod.ext (map_one (archInf F)) rfl

def scl (S : Finset (Fin n)) (t : Fin S.card → ℝ) : Fin n ⊕ Fin n → ℝ
  | Sum.inl i => if h : below S i < S.card then Real.exp (t ⟨below S i, h⟩) else 1
  | Sum.inr i => if h : below S i < S.card then Real.exp (-t ⟨below S i, h⟩) else 1

theorem scl_mul_neg (S : Finset (Fin n)) (t : Fin S.card → ℝ) (i : Fin n ⊕ Fin n) : scl S t i * scl S (-t) i = 1 := by
  rcases i with i | i <;> simp only [scl, Pi.neg_apply, neg_neg] <;> split_ifs <;> simp [← Real.exp_add]

variable (F E) in

def aDiag (S : Finset (Fin n)) (t : Fin S.card → ℝ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) :=
  Matrix.diagonal fun i => algebraMap (AF F) (AE F E) (archA F (scl S t i))

theorem aDiag_mul_neg (S : Finset (Fin n)) (t : Fin S.card → ℝ) : aDiag F E S t * aDiag F E S (-t) = 1 := by
  simp only [aDiag, Matrix.diagonal_mul_diagonal, ← map_mul, ← archA_mul, scl_mul_neg, archA_one, map_one,
    Matrix.diagonal_one]

theorem aDiag_neg_mul (S : Finset (Fin n)) (t : Fin S.card → ℝ) : aDiag F E S (-t) * aDiag F E S t = 1 := by
  simpa using aDiag_mul_neg (F := F) (E := E) S (-t)

theorem conj_mul_conj (b : GL (Fin n ⊕ Fin n) E) (X Z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :
    incM F b.1 * X * incM F (b⁻¹).1 * (incM F b.1 * Z * incM F (b⁻¹).1) = incM F b.1 * (X * Z) * incM F (b⁻¹).1 := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F (b⁻¹).1) (incM F b.1), incM_inv_mul, Matrix.one_mul]

def IsAS (b : GL (Fin n ⊕ Fin n) E) (S : Finset (Fin n)) (t : Fin S.card → ℝ) (g : G2 σ Y) : Prop :=
  inFrame b g = aDiag F E S t

variable (F) in

def aU (b : GL (Fin n ⊕ Fin n) E) (S : Finset (Fin n)) (t : Fin S.card → ℝ) : GL (Fin n ⊕ Fin n) (AE F E) where
  val := incM F b.1 * aDiag F E S t * incM F (b⁻¹).1
  inv := incM F b.1 * aDiag F E S (-t) * incM F (b⁻¹).1
  val_inv := (conj_mul_conj b _ _).trans (by rw [aDiag_mul_neg, Matrix.mul_one, incM_mul_inv])
  inv_val := (conj_mul_conj b _ _).trans (by rw [aDiag_neg_mul, Matrix.mul_one, incM_mul_inv])

theorem incM_alt_alt (e : E) :
    incM F (Matrix.fromBlocks 0 1 (e • 1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) =
      Matrix.fromBlocks 0 1 (inclR (F := F) (E := E) (AF F) e • 1) 0 := by
  ext r s
  rcases r with i | i <;> rcases s with j | j <;> simp [incM, Matrix.one_apply] <;> split_ifs <;> simp

theorem incM_dbl (J : Matrix (Fin n) (Fin n) E) : (dbl J).map (inclR (F := F) (E := E) (AF F)) = dbl (incM F J) := by
  unfold dbl incM
  rw [Matrix.fromBlocks_map]
  congr 1 <;> ext <;> simp

theorem map_sigma_incM (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) :
    (M.map σ).map (inclR (F := F) (E := E) (AF F)) = (incM F M).map (cA σ) := by
  ext r s
  simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]

theorem map_cA_mul (X Z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :
    (X * Z).map (cA σ) = X.map (cA σ) * Z.map (cA σ) :=
  Matrix.map_mul (f := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E))

theorem frame_adelic {b : GL (Fin n ⊕ Fin n) E} {ε : ℤˣ}
    (h : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    (incM F b.1)ᵀ * dbl (incM F Y.J) * (incM F b.1).map (cA σ) =
      Matrix.fromBlocks 0 1 (inclR (F := F) (E := E) (AF F) ((ε : ℤ) : E) • 1) 0 := by
  have := congrArg (fun M => M.map (inclR (F := F) (E := E) (AF F))) h
  simp only [Matrix.map_mul, incM_dbl, map_sigma_incM] at this
  rw [← incM_alt_alt]
  exact this

variable (σ Y) in

def aS (b : GL (Fin n ⊕ Fin n) E) (S : Finset (Fin n)) (t : Fin S.card → ℝ) : G2 σ Y := by
  classical
  exact if h : aU F b S t ∈ UG (cA σ) (dbl (incM F Y.J)) then ⟨aU F b S t, h⟩ else 1

structure IsCTData (b : GL (Fin n ⊕ Fin n) E) (S : Finset (Fin n)) (μ : Measure (uniS σ Y b S))
    (D : Set (uniS σ Y b S)) : Prop where
  inv : ∀ (u : uniS σ Y b S) (A : Set (uniS σ Y b S)), MeasurableSet A → μ ((u * ·) ⁻¹' A) = μ A
  fund : IsFundamentalDomain ((rat2 σ Y).subgroupOf (uniS σ Y b S)) D μ
  vol : μ D = 1

def constTerm {b : GL (Fin n ⊕ Fin n) E} {S : Finset (Fin n)} (μ : Measure (uniS σ Y b S)) (D : Set (uniS σ Y b S))
    (φ : G2 σ Y → ℂ) (g : G2 σ Y) : ℂ :=
  ∫ u in D, φ ((u : G2 σ Y) * g) ∂μ

def conv (μ : Measure (G2 σ Y)) (h φ : G2 σ Y → ℂ) (x : G2 σ Y) : ℂ := ∫ y, h y * φ (x * y) ∂μ

end SiegelEisensteinSeries.Grp

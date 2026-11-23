import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Definitions.Divisors.GenSubHwOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLiftCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartInvariantSubmoduleEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviLiftMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerOfCoef
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.TwCoef

open Matrix Formalism.BasicNotions.TH

variable {R S : ℕ}

def splitIx (A : Fin (R + 1)) : Ix (R + 1) (S + 1) ≃ Ix R S ⊕ (Unit ⊕ Unit) :=
  (Equiv.sumCongr ((finSuccEquiv' A).trans (Equiv.optionEquivSumPUnit.{0, 0} (Fin R)))
    ((finSuccEquiv' (Fin.last S)).trans (Equiv.optionEquivSumPUnit.{0, 0} (Fin S)))).trans
    (Equiv.sumSumSumComm (Fin R) Unit (Fin S) Unit)

@[simp] theorem splitIx_inl_self (A : Fin (R + 1)) : splitIx (S := S) A (.inl A) = .inr (.inl ()) := by
  simp [splitIx, Equiv.sumSumSumComm, finSuccEquiv'_at, Equiv.optionEquivSumPUnit]

@[simp] theorem splitIx_inl_succAbove (A : Fin (R + 1)) (i : Fin R) :
    splitIx (S := S) A (.inl (A.succAbove i)) = .inl (.inl i) := by
  simp [splitIx, Equiv.sumSumSumComm, finSuccEquiv'_succAbove, Equiv.optionEquivSumPUnit]

@[simp] theorem splitIx_inr_last (A : Fin (R + 1)) : splitIx (S := S) A (.inr (Fin.last S)) = .inr (.inr ()) := by
  simp [splitIx, Equiv.sumSumSumComm, finSuccEquiv'_at, Equiv.optionEquivSumPUnit]

@[simp] theorem splitIx_inr_castSucc (A : Fin (R + 1)) (j : Fin S) :
    splitIx (S := S) A (.inr j.castSucc) = .inl (.inr j) := by
  have : finSuccEquiv' (Fin.last S) j.castSucc = some j := by
    rw [← Fin.succAbove_last, finSuccEquiv'_succAbove]
  simp [splitIx, Equiv.sumSumSumComm, this, Equiv.optionEquivSumPUnit]

def newCols {n : ℕ} (ε φ : Fin n → ℂ) : Matrix (Fin n) (Unit ⊕ Unit) ℂ :=
  fun r u => Sum.elim (fun _ => ε r) (fun _ => φ r) u

def extFrame {n : ℕ} (A : Fin (R + 1)) (C : Matrix (Fin n) (Ix R S) ℂ) (ε φ : Fin n → ℂ) :
    Matrix (Fin n) (Ix (R + 1) (S + 1)) ℂ :=
  (Matrix.fromCols C (newCols ε φ)).submatrix id (splitIx A)

def extM (A : Fin (R + 1)) (g : Matrix (Ix R S) (Ix R S) ℂ) (c : ℂ) : Matrix (Ix (R + 1) (S + 1)) (Ix (R + 1) (S + 1)) ℂ :=
  (Matrix.fromBlocks g 0 0 (c • (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ))).submatrix (splitIx A) (splitIx A)

section Entries

variable (A : Fin (R + 1)) (g : Matrix (Ix R S) (Ix R S) ℂ) (c : ℂ)

@[simp] theorem extM_pp (i j : Fin R) : extM A g c (.inl (A.succAbove i)) (.inl (A.succAbove j)) = g (.inl i) (.inl j) := by
  simp [extM]

@[simp] theorem extM_AA : extM A g c (.inl A) (.inl A) = c := by simp [extM]

@[simp] theorem extM_Ap (j : Fin R) : extM A g c (.inl A) (.inl (A.succAbove j)) = 0 := by simp [extM]

@[simp] theorem extM_pA (i : Fin R) : extM A g c (.inl (A.succAbove i)) (.inl A) = 0 := by simp [extM]

@[simp] theorem extM_nn (i j : Fin S) : extM A g c (.inr i.castSucc) (.inr j.castSucc) = g (.inr i) (.inr j) := by
  simp [extM]

@[simp] theorem extM_LL : extM A g c (.inr (Fin.last S)) (.inr (Fin.last S)) = c := by simp [extM]

@[simp] theorem extM_Ln (j : Fin S) : extM A g c (.inr (Fin.last S)) (.inr j.castSucc) = 0 := by simp [extM]

@[simp] theorem extM_nL (i : Fin S) : extM A g c (.inr i.castSucc) (.inr (Fin.last S)) = 0 := by simp [extM]

end Entries

def posEquiv (A : Fin (R + 1)) : Fin R ⊕ Unit ≃ Fin (R + 1) :=
  ((finSuccEquiv' A).trans (Equiv.optionEquivSumPUnit.{0, 0} (Fin R))).symm

@[simp] theorem posEquiv_inl (A : Fin (R + 1)) (i : Fin R) : posEquiv A (.inl i) = A.succAbove i := by
  rw [posEquiv, Equiv.symm_apply_eq]; simp [finSuccEquiv'_succAbove, Equiv.optionEquivSumPUnit]

@[simp] theorem posEquiv_inr (A : Fin (R + 1)) (u : Unit) : posEquiv A (.inr u) = A := by
  rw [posEquiv, Equiv.symm_apply_eq]; simp [finSuccEquiv'_at, Equiv.optionEquivSumPUnit]

theorem det_toBlocks₁₁_extM (A : Fin (R + 1)) (g : Matrix (Ix R S) (Ix R S) ℂ) (c : ℂ) :
    (toBlocks₁₁ (extM A g c)).det = (toBlocks₁₁ g).det * c := by
  rw [← Matrix.det_submatrix_equiv_self (posEquiv A)]
  have : (toBlocks₁₁ (extM A g c)).submatrix (posEquiv A) (posEquiv A) =
      Matrix.fromBlocks (toBlocks₁₁ g) 0 0 (Matrix.of fun (_ _ : Unit) => c) := by
    ext (i | i) (j | j) <;> simp [toBlocks₁₁, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  rw [this, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique (Matrix.of fun (_ _ : Unit) => c)]; rfl

def negEquiv : Fin S ⊕ Unit ≃ Fin (S + 1) :=
  ((finSuccEquiv' (Fin.last S)).trans (Equiv.optionEquivSumPUnit.{0, 0} (Fin S))).symm

theorem fse_last_castSucc (i : Fin S) : finSuccEquiv' (Fin.last S) i.castSucc = some i := by
  rw [← Fin.succAbove_last, finSuccEquiv'_succAbove]

@[simp] theorem negEquiv_inl (i : Fin S) : negEquiv (.inl i) = i.castSucc := by
  rw [negEquiv, Equiv.symm_apply_eq]; simp [fse_last_castSucc, Equiv.optionEquivSumPUnit]

@[simp] theorem negEquiv_inr (u : Unit) : negEquiv (S := S) (.inr u) = Fin.last S := by
  rw [negEquiv, Equiv.symm_apply_eq]; simp [finSuccEquiv'_at, Equiv.optionEquivSumPUnit]

theorem det_toBlocks₂₂_extM (A : Fin (R + 1)) (g : Matrix (Ix R S) (Ix R S) ℂ) (c : ℂ) :
    (toBlocks₂₂ (extM A g c)).det = (toBlocks₂₂ g).det * c := by
  rw [← Matrix.det_submatrix_equiv_self negEquiv]
  have : (toBlocks₂₂ (extM A g c)).submatrix negEquiv negEquiv =
      Matrix.fromBlocks (toBlocks₂₂ g) 0 0 (Matrix.of fun (_ _ : Unit) => c) := by
    ext (i | i) (j | j) <;> simp [toBlocks₂₂, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  rw [this, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique (Matrix.of fun (_ _ : Unit) => c)]; rfl

def lowEquiv (A : Fin (R + 1)) : {i : Fin R // (i : ℕ) < A} ⊕ Unit ≃ {i : Fin (R + 1) // (i : ℕ) < (A : ℕ) + 1} :=
  Equiv.ofBijective
    (fun x => match x with
      | .inl i => ⟨A.succAbove i.1, by
          rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; exact i.2)]; simp only [Fin.coe_castSucc]; omega⟩
      | .inr _ => ⟨A, by omega⟩)
    (by
      constructor
      · rintro (i | i) (j | j) h <;> simp only [Subtype.mk.injEq] at h
        · exact congrArg Sum.inl (Subtype.ext (Fin.succAbove_right_injective h))
        · exact absurd h (Fin.succAbove_ne _ _)
        · exact absurd h.symm (Fin.succAbove_ne _ _)
        · rfl
      · rintro ⟨j, hj⟩
        by_cases h : j = A
        · exact ⟨.inr (), by simp [h]⟩
        · have hjA : (j : ℕ) < A := by
            rcases Nat.lt_or_ge (j : ℕ) A with h1 | h1
            · exact h1
            · exact absurd (Fin.ext (by omega)) h
          refine ⟨.inl ⟨⟨j, by omega⟩, hjA⟩, ?_⟩
          simp only [Subtype.mk.injEq]
          rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using hjA)]
          rfl)

@[simp] theorem lowEquiv_inl (A : Fin (R + 1)) (i : {i : Fin R // (i : ℕ) < A}) :
    (lowEquiv A (.inl i) : Fin (R + 1)) = A.succAbove i.1 := rfl

@[simp] theorem lowEquiv_inr (A : Fin (R + 1)) (u : Unit) : (lowEquiv A (.inr u) : Fin (R + 1)) = A := rfl

theorem leadMinor_extM (A : Fin (R + 1)) (g : Matrix (Ix R S) (Ix R S) ℂ) (c : ℂ) :
    GlobalTheory.HwCoef.leadMinor ((A : ℕ) + 1) (extM A g c) = GlobalTheory.HwCoef.leadMinor A g * c := by
  unfold GlobalTheory.HwCoef.leadMinor
  rw [← Matrix.det_submatrix_equiv_self (lowEquiv A)]
  have : ((toBlocks₁₁ (extM A g c)).submatrix (fun i : {i : Fin (R + 1) // (i : ℕ) < (A : ℕ) + 1} => i.1)
      (fun i => i.1)).submatrix (lowEquiv A) (lowEquiv A) =
      Matrix.fromBlocks ((toBlocks₁₁ g).submatrix (fun i : {i : Fin R // (i : ℕ) < A} => i.1) (fun i => i.1)) 0 0
        (Matrix.of fun (_ _ : Unit) => c) := by
    ext (i | i) (j | j) <;> simp [toBlocks₁₁, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  rw [this, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique (Matrix.of fun (_ _ : Unit) => c)]; rfl

theorem coef_extM_one (A : Fin (R + 1)) (g : Matrix (Ix R S) (Ix R S) ℂ) (e₁ e₂ e₃ : ℤ) :
    GlobalTheory.HwCoef.coef ((A : ℕ) + 1) e₁ e₂ e₃ (extM A g 1) = GlobalTheory.HwCoef.coef A e₁ e₂ e₃ g := by
  simp only [GlobalTheory.HwCoef.coef, leadMinor_extM, det_toBlocks₁₁_extM, det_toBlocks₂₂_extM, mul_one]

def dExt (A : Fin (R + 1)) (c : ℂ) (i : Ix (R + 1) (S + 1)) : ℂ := Sum.elim (fun _ => 1) (fun _ => c) (splitIx A i)

theorem extM_one_eq_diagonal (A : Fin (R + 1)) (c : ℂ) : extM (S := S) A 1 c = Matrix.diagonal (dExt A c) := by
  rw [extM, Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_one, Matrix.fromBlocks_diagonal,
    Matrix.submatrix_diagonal_equiv]
  rfl

theorem leadMinor_mul_diagonal {R' S' : ℕ} (m : ℕ) (M : Matrix (Ix R' S') (Ix R' S') ℂ) (d : Ix R' S' → ℂ) :
    GlobalTheory.HwCoef.leadMinor m (M * Matrix.diagonal d) =
      GlobalTheory.HwCoef.leadMinor m M * ∏ i : {i : Fin R' // (i : ℕ) < m}, d (.inl i.1) := by
  unfold GlobalTheory.HwCoef.leadMinor
  rw [← Matrix.det_diagonal, ← Matrix.det_mul]
  congr 1
  ext i j
  simp [toBlocks₁₁, Matrix.mul_diagonal]

theorem toBlocks₁₁_mul_diagonal {R' S' : ℕ} (M : Matrix (Ix R' S') (Ix R' S') ℂ) (d : Ix R' S' → ℂ) :
    toBlocks₁₁ (M * Matrix.diagonal d) = toBlocks₁₁ M * Matrix.diagonal (fun i => d (.inl i)) := by
  ext i j; simp [toBlocks₁₁, Matrix.mul_diagonal]

theorem toBlocks₂₂_mul_diagonal {R' S' : ℕ} (M : Matrix (Ix R' S') (Ix R' S') ℂ) (d : Ix R' S' → ℂ) :
    toBlocks₂₂ (M * Matrix.diagonal d) = toBlocks₂₂ M * Matrix.diagonal (fun i => d (.inr i)) := by
  ext i j; simp [toBlocks₂₂, Matrix.mul_diagonal]

theorem dExt_inl (A : Fin (R + 1)) (c : ℂ) (i : Fin (R + 1)) : dExt (S := S) A c (.inl i) = if i = A then c else 1 := by
  by_cases h : i = A
  · subst h; simp [dExt]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq h
    simp [dExt, Fin.succAbove_ne]

theorem dExt_inr (A : Fin (R + 1)) (c : ℂ) (i : Fin (S + 1)) :
    dExt (S := S) A c (.inr i) = if i = Fin.last S then c else 1 := by
  by_cases h : i = Fin.last S
  · subst h; simp [dExt]
  · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 h
    simp [dExt, Fin.castSucc_ne_last]

theorem coef_mul_extM (A : Fin (R + 1)) (M : Matrix (Ix (R + 1) (S + 1)) (Ix (R + 1) (S + 1)) ℂ) (c : ℂ) (e₁ e₂ e₃ : ℤ) :
    GlobalTheory.HwCoef.coef ((A : ℕ) + 1) e₁ e₂ e₃ (M * extM A 1 c) =
      GlobalTheory.HwCoef.coef ((A : ℕ) + 1) e₁ e₂ e₃ M * (c ^ e₁ * c ^ e₂ * c ^ e₃) := by
  have h1 : ∏ i : {i : Fin (R + 1) // (i : ℕ) < (A : ℕ) + 1}, dExt (S := S) A c (.inl i.1) = c := by
    rw [Fintype.prod_eq_single ⟨A, by omega⟩]
    · simp [dExt_inl]
    · intro i hi
      rw [dExt_inl, if_neg (fun h => hi (Subtype.ext h))]
  have h2 : ∏ i : Fin (R + 1), dExt (S := S) A c (.inl i) = c := by
    rw [Fintype.prod_eq_single A]
    · simp [dExt_inl]
    · intro i hi; rw [dExt_inl, if_neg hi]
  have h3 : ∏ i : Fin (S + 1), dExt (S := S) A c (.inr i) = c := by
    rw [Fintype.prod_eq_single (Fin.last S)]
    · simp [dExt_inr]
    · intro i hi; rw [dExt_inr, if_neg hi]
  simp only [GlobalTheory.HwCoef.coef, extM_one_eq_diagonal, leadMinor_mul_diagonal, toBlocks₁₁_mul_diagonal,
    toBlocks₂₂_mul_diagonal, Matrix.det_mul, Matrix.det_diagonal, h1, h2, h3, mul_zpow]
  ring

theorem mul_extFrame {n : ℕ} (A : Fin (R + 1)) {K : Matrix (Fin n) (Fin n) ℂ} {C : Matrix (Fin n) (Ix R S) ℂ}
    {g : Matrix (Ix R S) (Ix R S) ℂ} {ε φ : Fin n → ℂ} {c : ℂ} (hC : K * C = C * g) (hε : K *ᵥ ε = c • ε)
    (hφ : K *ᵥ φ = c • φ) : K * extFrame A C ε φ = extFrame A C ε φ * extM A g c := by
  have hN : K * newCols ε φ = newCols ε φ * (c • (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ)) := by
    ext r (u | u)
    · have := congrFun hε r
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      simp [newCols, Matrix.mul_apply, this, mul_comm]
    · have := congrFun hφ r
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      simp [newCols, Matrix.mul_apply, this, mul_comm]
  have e1 : K * extFrame A C ε φ = (K * Matrix.fromCols C (newCols ε φ)).submatrix id (splitIx A) := by
    ext r i; simp only [extFrame, Matrix.submatrix_apply, Matrix.mul_apply, id]
  rw [e1, extFrame, extM, Matrix.submatrix_mul_equiv, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, hC, hN]
  simp

theorem isReading_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (τ : ∀ w : InfinitePlace F, EmbOver E w) {n R' S' : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {C : InfinitePlace F → Matrix (Fin n) (Ix R' S') ℂ} {k k' : UA σ J}
    {g g' : InfinitePlace F → Matrix (Ix R' S') (Ix R' S') ℂ} (h : GlobalTheory.HwCoef.IsReading τ C k g)
    (h' : GlobalTheory.HwCoef.IsReading τ C k' g') : GlobalTheory.HwCoef.IsReading τ C (k * k') (fun w => g w * g' w) := by
  intro w
  change (mat k * mat k').map _ * C w = _
  rw [Matrix.map_mul, Matrix.mul_assoc, h' w, ← Matrix.mul_assoc, h w, Matrix.mul_assoc]

end GlobalTheory.TwCoef

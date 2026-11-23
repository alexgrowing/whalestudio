import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

noncomputable section

namespace GlobalTheory.RealLift.QuadFock

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

def atPlLin (w : ι) : Module.End ℂ (V w) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] i, V i) :=
  (PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun _ => LinearMap.id) w

theorem atPlLin_apply (w : ι) (L : Module.End ℂ (V w)) : atPlLin w L = atPl w L := by
  simp only [atPlLin, MultilinearMap.toLinearMap_apply, PiTensorProduct.mapMultilinear_apply, atPl]

theorem atPl_zero (w : ι) : atPl w (0 : Module.End ℂ (V w)) = 0 := by
  rw [← atPlLin_apply, map_zero]

theorem atPl_mul (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L * L') = atPl w L * atPl w L' := by
  unfold atPl
  rw [← PiTensorProduct.map_mul]
  congr 1
  funext i
  by_cases h : i = w
  · subst h
    simp
  · rw [Function.update_of_ne h, Function.update_of_ne h, Function.update_of_ne h]
    rfl

end Tensor

variable {P Q R S : ℕ}

theorem heisOp_smul (r : ℝ) (c : Matrix (Ix P Q) (Ix R S) ℂ) : heisOp (r • c) = (r : ℂ) • heisOp c := by
  unfold heisOp
  rw [smul_comm (r : ℂ) ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Matrix.smul_apply, Complex.real_smul, star_mul', Complex.star_def, Complex.conj_ofReal, smul_sub, smul_smul]
  congr 2 <;> ring

theorem heisOp_zero : heisOp (0 : Matrix (Ix P Q) (Ix R S) ℂ) = 0 := by
  simpa using heisOp_smul (P := P) (Q := Q) (R := R) (S := S) 0 0

theorem sumPl_single {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι) (M : Matrix (Ix P Q) (Ix R S) ℂ) :
    sumPl (V := fun _ : ι => Pol P Q R S) (fun w' => heisOp ((Pi.single w M : ι → Matrix (Ix P Q) (Ix R S) ℂ) w')) = atPl w (heisOp M) := by
  unfold sumPl
  rw [Finset.sum_eq_single w]
  · simp
  · intro b _ hb
    dsimp only
    rw [Pi.single_eq_of_ne hb, heisOp_zero, atPl_zero]
  · simp

end GlobalTheory.RealLift.QuadFock

namespace GlobalTheory.RealLift.QuadFock

variable {P Q R S : ℕ}

def sgn (a : Ix P Q) (b : Ix R S) : ℝ := (lineSign a b).re

theorem lineSign_eq_sgn (a : Ix P Q) (b : Ix R S) : lineSign a b = ((sgn a b : ℝ) : ℂ) := by
  rcases a with a | a <;> rcases b with b | b <;> simp [sgn, lineSign]

theorem sgn_mul_self (a : Ix P Q) (b : Ix R S) : sgn a b * sgn a b = 1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [sgn, lineSign]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def eS (w : ι) (a : Ix P Q) (b : Ix R S) (x : ℂ) : ι → Matrix (Ix P Q) (Ix R S) ℂ :=
  Pi.single w (Matrix.single a b x)

theorem eS_apply (w : ι) (a : Ix P Q) (b : Ix R S) (x : ℂ) (w' : ι) (a' : Ix P Q) (b' : Ix R S) :
    eS w a b x w' a' b' = if w' = w ∧ a' = a ∧ b' = b then x else 0 := by
  by_cases hw : w' = w
  · subst hw
    simp only [eS, Pi.single_eq_same, Matrix.single_apply, true_and]
    by_cases h : a' = a ∧ b' = b
    · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]
  · simp [eS, hw]

theorem sum_eS (w : ι) (a : Ix P Q) (b : Ix R S) (x : ℂ) (c : ι → Matrix (Ix P Q) (Ix R S) ℂ) :
    (∑ w', ∑ a', ∑ b', lineSign a' b' * eS w a b x w' a' b' * star (c w' a' b')) =
      lineSign a b * x * star (c w a b) := by
  rw [Finset.sum_eq_single w, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [eS_apply]
  all_goals first
    | (intro y _ hy; simp [eS_apply, hy, Ne.symm hy]; done)
    | simp

theorem decomp (c : ι → Matrix (Ix P Q) (Ix R S) ℂ) :
    c = ∑ w, ∑ a, ∑ b, ((c w a b).re • eS w a b 1 + (c w a b).im • eS w a b Complex.I) := by
  funext w
  ext a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Pi.add_apply, Pi.smul_apply, Matrix.add_apply,
    Matrix.smul_apply]
  rw [Finset.sum_eq_single w, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp only [eS_apply, and_self, if_true, Complex.real_smul, mul_one]
    exact (Complex.re_add_im _).symm
  all_goals first
    | (intro y _ hy; simp [eS_apply, hy, Ne.symm hy]; done)
    | simp

end GlobalTheory.RealLift.QuadFock

namespace GlobalTheory.RealLift.QuadFock

variable {P Q R S : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def cu (i : ι × Ix P Q × Ix R S × Bool) : ι → Matrix (Ix P Q) (Ix R S) ℂ :=
  if i.2.2.2 then (sgn i.2.1 i.2.2.1 / 2) • eS i.1 i.2.1 i.2.2.1 1
  else (-(sgn i.2.1 i.2.2.1 / 2)) • eS i.1 i.2.1 i.2.2.1 Complex.I

def cv (i : ι × Ix P Q × Ix R S × Bool) : ι → Matrix (Ix P Q) (Ix R S) ℂ :=
  if i.2.2.2 then eS i.1 i.2.1 i.2.2.1 Complex.I else eS i.1 i.2.1 i.2.2.1 1

theorem dual {l : Type} [Fintype l] (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (hφ : ∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im)
    (x : l ⊕ l → ℝ) : ∑ i, sympl (φ (cv i)) x • φ (cu i) = x := by
  obtain ⟨c, rfl⟩ := φ.surjective x
  have e1 : ∀ i, sympl (φ (cv i)) (φ c) • φ (cu i) = φ (sympl (φ (cv i)) (φ c) • cu i) :=
    fun i => (map_smul φ _ _).symm
  simp only [e1, ← map_sum]
  congr 1
  conv_rhs => rw [decomp c]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, cu, cv, if_true, Bool.false_eq_true, if_false, hφ, sum_eS]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul, smul_smul, lineSign_eq_sgn]
  have h2 := sgn_mul_self a b
  congr 2
  · simp [Complex.mul_im, Complex.mul_re]
    linear_combination (c w a b).re * h2
  · simp [Complex.mul_im, Complex.mul_re]
    linear_combination (c w a b).im * h2

theorem cu_true_mul (Y : ι → Mat R S) (w : ι) (a : Ix P Q) (b : Ix R S) (w' : ι) :
    cu (w, a, b, true) w' * (Y w')ᵀ =
      (Pi.single w ((sgn a b / 2) • (Matrix.single a b (1 : ℂ) * (Y w)ᵀ)) : ι → Matrix (Ix P Q) (Ix R S) ℂ) w' := by
  by_cases h : w' = w
  · subst h
    simp only [cu, eS, if_true, Bool.false_eq_true, if_false, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_mul]
  · simp [cu, eS, h]

theorem cu_false_mul (Y : ι → Mat R S) (w : ι) (a : Ix P Q) (b : Ix R S) (w' : ι) :
    cu (w, a, b, false) w' * (Y w')ᵀ =
      (Pi.single w ((-(sgn a b / 2)) • (Matrix.single a b Complex.I * (Y w)ᵀ)) : ι → Matrix (Ix P Q) (Ix R S) ℂ) w' := by
  by_cases h : w' = w
  · subst h
    simp only [cu, eS, if_true, Bool.false_eq_true, if_false, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_mul]
  · simp [cu, eS, h]

theorem cv_true (w : ι) (a : Ix P Q) (b : Ix R S) :
    cv (w, a, b, true) = (Pi.single w (Matrix.single a b Complex.I) : ι → Matrix (Ix P Q) (Ix R S) ℂ) := by
  simp [cv, eS]

theorem cv_false (w : ι) (a : Ix P Q) (b : Ix R S) :
    cv (w, a, b, false) = (Pi.single w (Matrix.single a b (1 : ℂ)) : ι → Matrix (Ix P Q) (Ix R S) ℂ) := by
  simp [cv, eS]

theorem atPlLin_mul {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (w : ι) (L L' : Module.End ℂ (V w)) :
    atPlLin w (L * L') = atPlLin w L * atPlLin w L' := by
  simp only [atPlLin_apply, atPl_mul]

end GlobalTheory.RealLift.QuadFock

namespace GlobalTheory.RealLift.QuadFock

theorem quad_fock : (∀ (l κ : Type) [Fintype l] [DecidableEq l] [Fintype κ] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : κ → (l ⊕ l → ℝ)),
    (∀ w, ∑ i, sympl (v i) w • u i = w) →
    quad X = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
      (dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i))) → (∀ (P Q R S : ℕ) (Y : Mat R S), Y ∈ upq R S →
    fockAct2 P Q R S Y = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ a : Ix P Q, ∑ b : Ix R S, (lineSign a b / 4) •
      ((heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) * heisOp (Matrix.single a b Complex.I) +
          heisOp (Matrix.single a b Complex.I) * heisOp (Matrix.single a b (1 : ℂ) * Yᵀ)) -
        (heisOp (Matrix.single a b Complex.I * Yᵀ) * heisOp (Matrix.single a b (1 : ℂ)) +
          heisOp (Matrix.single a b (1 : ℂ)) * heisOp (Matrix.single a b Complex.I * Yᵀ)))) → ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (Ψ : (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) →ₗ[ℂ] Sch l),
    (∀ c T, Ψ (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) (Ψ T)) →
    ∀ Y : ι → Mat R S, (∀ w, Y w ∈ upq R S) → ∀ Z : Matrix (l ⊕ l) (l ⊕ l) ℝ,
    (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) →
    ∀ T, quad Z (Ψ T) = Ψ (sumPl (fun w => fockAct2 P Q R S (Y w)) T) := by
  intro H1 H2 ι l _ _ _ _ P Q R S φ hφ Ψ hΨ Y hY Z hZ T
  have hq := H1 l (ι × Ix P Q × Ix R S × Bool) Z (fun i => φ (cu i)) (fun i => φ (cv i)) (dual φ hφ)
  have hop : sumPl (V := fun _ : ι => Pol P Q R S) (fun w => fockAct2 P Q R S (Y w)) =
      (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
        (sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (cu i w * (Y w)ᵀ)) *
            sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (cv i w)) +
          sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (cv i w)) *
            sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (cu i w * (Y w)ᵀ))) := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, cu_true_mul, cu_false_mul, cv_true, cv_false, sumPl_single,
      heisOp_smul]
    unfold sumPl
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    dsimp only
    rw [H2 P Q R S (Y w) (hY w)]
    simp only [← atPlLin_apply, map_smul, map_sum, map_sub, map_add, atPlLin_mul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [lineSign_eq_sgn]
    simp only [smul_mul_assoc, mul_smul_comm]
    push_cast
    module
  rw [hop, hq]
  clear H1 H2 hq hop hφ hY
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.add_apply, Module.End.mul_apply, map_smul, map_sum, map_add, hΨ, hZ]

end GlobalTheory.RealLift.QuadFock

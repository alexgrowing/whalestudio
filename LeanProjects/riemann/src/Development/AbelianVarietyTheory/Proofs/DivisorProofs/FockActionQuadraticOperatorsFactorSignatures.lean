import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchwartzIntertwinesMetaplecticQuadratic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticQuadraticOperatorEqSumSymplecticDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAct2EqSymmetrisedHeisenbergQuadraticStatement
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.HoweD.QuadFockD

open GlobalTheory.RealLift.QuadFock

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}

abbrev MD (P Q R S : ι → ℕ) (w : ι) : Type := Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ

theorem sumPl_singleD (w : ι) (M : MD P Q R S w) :
    sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w))
      (fun w' => heisOp ((Pi.single w M : ∀ w', MD P Q R S w') w')) = atPl w (heisOp M) := by
  unfold sumPl
  rw [Finset.sum_eq_single w]
  · simp
  · intro b _ hb
    dsimp only
    rw [Pi.single_eq_of_ne hb, heisOp_zero, atPl_zero]
  · simp

def eS (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (x : ℂ) : ∀ w', MD P Q R S w' :=
  Pi.single w (Matrix.single a b x)

theorem eS_ne (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (x : ℂ) {w' : ι} (h : w' ≠ w) :
    eS w a b x w' = 0 := by
  simp [eS, Pi.single_eq_of_ne h]

theorem eS_same (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (x : ℂ) :
    eS w a b x w = Matrix.single a b x := by
  simp [eS]

theorem sum_eS (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (x : ℂ) (c : ∀ w', MD P Q R S w') :
    (∑ w', ∑ a', ∑ b', lineSign a' b' * eS w a b x w' a' b' * star (c w' a' b')) =
      lineSign a b * x * star (c w a b) := by
  rw [Finset.sum_eq_single w]
  · rw [eS_same, Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp [Matrix.single_apply]
    · intro y _ hy; simp [Matrix.single_apply, hy, Ne.symm hy]
    · simp
    · intro y _ hy
      refine Finset.sum_eq_zero fun b' _ => ?_
      simp [Matrix.single_apply, hy, Ne.symm hy]
    · simp
  · intro y _ hy
    simp [eS_ne w a b x hy]
  · simp

theorem decomp (c : ∀ w, MD P Q R S w) :
    c = ∑ w, ∑ a, ∑ b, ((c w a b).re • eS w a b 1 + (c w a b).im • eS w a b Complex.I) := by
  funext w
  ext a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Pi.add_apply, Pi.smul_apply, Matrix.add_apply,
    Matrix.smul_apply]
  rw [Finset.sum_eq_single w]
  · simp only [eS_same]
    rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp only [Matrix.single_apply, and_self, if_true, Complex.real_smul, mul_one]
      exact (Complex.re_add_im _).symm
    · intro y _ hy; simp [Matrix.single_apply, hy, Ne.symm hy]
    · simp
    · intro y _ hy
      refine Finset.sum_eq_zero fun b' _ => ?_
      simp [Matrix.single_apply, hy, Ne.symm hy]
    · simp
  · intro y _ hy
    refine Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun b' _ => ?_
    simp [eS_ne _ _ _ _ (Ne.symm hy)]
  · simp

abbrev Idx (P Q R S : ι → ℕ) : Type := Σ w : ι, Ix (P w) (Q w) × Ix (R w) (S w) × Bool

def cu (i : Idx P Q R S) : ∀ w, MD P Q R S w :=
  if i.2.2.2 then (sgn i.2.1 i.2.2.1 / 2) • eS i.1 i.2.1 i.2.2.1 1
  else (-(sgn i.2.1 i.2.2.1 / 2)) • eS i.1 i.2.1 i.2.2.1 Complex.I

def cv (i : Idx P Q R S) : ∀ w, MD P Q R S w :=
  if i.2.2.2 then eS i.1 i.2.1 i.2.2.1 Complex.I else eS i.1 i.2.1 i.2.2.1 1

theorem sum_idx {M : Type} [AddCommMonoid M] (f : Idx P Q R S → M) :
    ∑ i, f i = ∑ w, ∑ a, ∑ b, (f ⟨w, a, b, true⟩ + f ⟨w, a, b, false⟩) := by
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]

theorem dual {l : Type} [Fintype l] (φ : (∀ w, MD P Q R S w) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (hφ : ∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im)
    (x : l ⊕ l → ℝ) : ∑ i, sympl (φ (cv i)) x • φ (cu i) = x := by
  obtain ⟨c, rfl⟩ := φ.surjective x
  have e1 : ∀ i, sympl (φ (cv i)) (φ c) • φ (cu i) = φ (sympl (φ (cv i)) (φ c) • cu i) :=
    fun i => (map_smul φ _ _).symm
  simp only [e1, ← map_sum]
  congr 1
  conv_rhs => rw [decomp c]
  rw [sum_idx]
  simp only [cu, cv, if_true, Bool.false_eq_true, if_false, hφ, sum_eS]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul, smul_smul, lineSign_eq_sgn]
  have h2 := sgn_mul_self a b
  congr 2
  · simp [Complex.mul_im, Complex.mul_re]
    linear_combination (c w a b).re * h2
  · simp [Complex.mul_im, Complex.mul_re]
    linear_combination (c w a b).im * h2

end GlobalTheory.HoweD.QuadFockD

namespace GlobalTheory.HoweD.QuadFockD

open GlobalTheory.RealLift.QuadFock

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}

theorem cu_true_mul (Y : ∀ w, Mat (R w) (S w)) (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (w' : ι) :
    cu (P := P) (Q := Q) ⟨w, a, b, true⟩ w' * (Y w')ᵀ =
      (Pi.single w ((sgn a b / 2) • (Matrix.single a b (1 : ℂ) * (Y w)ᵀ)) : ∀ w', MD P Q R S w') w' := by
  by_cases h : w' = w
  · subst h
    simp only [cu, eS, if_true, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_mul]
  · simp [cu, eS, h]

theorem cu_false_mul (Y : ∀ w, Mat (R w) (S w)) (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (w' : ι) :
    cu (P := P) (Q := Q) ⟨w, a, b, false⟩ w' * (Y w')ᵀ =
      (Pi.single w ((-(sgn a b / 2)) • (Matrix.single a b Complex.I * (Y w)ᵀ)) : ∀ w', MD P Q R S w') w' := by
  by_cases h : w' = w
  · subst h
    simp only [cu, eS, Bool.false_eq_true, if_false, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_mul]
  · simp [cu, eS, h]

theorem cv_true (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) :
    cv (P := P) (Q := Q) (R := R) (S := S) ⟨w, a, b, true⟩ =
      (Pi.single w (Matrix.single a b Complex.I) : ∀ w', MD P Q R S w') := by
  simp [cv, eS]

theorem cv_false (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) :
    cv (P := P) (Q := Q) (R := R) (S := S) ⟨w, a, b, false⟩ =
      (Pi.single w (Matrix.single a b (1 : ℂ)) : ∀ w', MD P Q R S w') := by
  simp [cv, eS]

end GlobalTheory.HoweD.QuadFockD

namespace GlobalTheory.HoweD

open GlobalTheory.RealLift.QuadFock GlobalTheory.HoweD.QuadFockD

theorem quad_fockD : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (Ψ : (⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) →ₗ[ℂ] Sch l),
    (∀ c T, Ψ (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) (Ψ T)) →
    ∀ Y : ∀ w : ι, Mat (R w) (S w), (∀ w, Y w ∈ upq (R w) (S w)) → ∀ Z : Matrix (l ⊕ l) (l ⊕ l) ℝ,
    (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) →
    ∀ T, quad Z (Ψ T) = Ψ (sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w)) T) := by
  intro ι l _ _ _ _ P Q R S φ hφ Ψ hΨ Y hY Z hZ T
  have hq := GlobalTheory.T.metaplecticQuadraticOperator_eq_sum_symplectic_dual l (Idx P Q R S) Z (fun i => φ (QuadFockD.cu i)) (fun i => φ (QuadFockD.cv i))
    (QuadFockD.dual φ hφ)
  have hop : sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w)) =
      (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i : Idx P Q R S, (1 / 2 : ℂ) •
        (sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (QuadFockD.cu i w * (Y w)ᵀ)) *
            sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (QuadFockD.cv i w)) +
          sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (QuadFockD.cv i w)) *
            sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (QuadFockD.cu i w * (Y w)ᵀ))) := by
    rw [sum_idx]
    simp only [QuadFockD.cu_true_mul, QuadFockD.cu_false_mul, QuadFockD.cv_true, QuadFockD.cv_false, sumPl_singleD,
      heisOp_smul]
    unfold sumPl
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    dsimp only
    rw [GlobalTheory.T.fockAct2_eq_symmetrised_heisenbergQuadratic (P w) (Q w) (R w) (S w) (Y w) (hY w)]
    simp only [← atPlLin_apply, map_smul, map_sum, map_sub, map_add, atPlLin_mul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [lineSign_eq_sgn]
    simp only [smul_mul_assoc, mul_smul_comm]
    push_cast
    module
  rw [hop, hq]
  clear hq hop hφ hY
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.add_apply, Module.End.mul_apply, map_smul, map_sum, map_add, hΨ, hZ]

end GlobalTheory.HoweD

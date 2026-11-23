import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyChern
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace Proportionality

open MvPolynomial Finset Filter Topology

noncomputable section

def RegMaxHessian.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι], ∃ C : ℝ, ∀ η : ℝ, 0 < η →
    ContDiff ℝ 2 (ReciprocityTheory.AnForm.A.regMax (ι := ι) η) ∧
    ∀ (t : ι → ℝ) (i j : ι),
      |fderiv ℝ (fderiv ℝ (ReciprocityTheory.AnForm.A.regMax (ι := ι) η)) t (Pi.single i 1)
          (Pi.single j 1)| ≤ C / η

example : Nonempty (Fintype (Fin 2)) ∧ Nonempty (Fin 2) ∧ Nonempty (DecidableEq (Fin 2)) :=
  ⟨⟨inferInstance⟩, inferInstance, ⟨inferInstance⟩⟩

def CurvaturePlus.Statement : Prop :=
  ∀ z : Fin 1 → ℂ,
    wirtinger (fun w => wirtingerBar (fun u : Fin 1 → ℂ =>
        ((Real.log (1 + ‖u 0‖ ^ 2) : ℝ) : ℂ)) 0 w) 0 z =
      ((((1 + ‖z 0‖ ^ 2) ^ 2)⁻¹ : ℝ) : ℂ)

def CurvatureMinus.Statement : Prop :=
  ∀ z : Fin 1 → ℂ, ‖z 0‖ < 1 →
    wirtinger (fun w => wirtingerBar (fun u : Fin 1 → ℂ =>
        ((-Real.log (1 - ‖u 0‖ ^ 2) : ℝ) : ℂ)) 0 w) 0 z =
      ((((1 - ‖z 0‖ ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) ∧
    0 < ((1 - ‖z 0‖ ^ 2) ^ 2)⁻¹

example : ‖(fun _ : Fin 1 => (1 / 2 : ℂ)) 0‖ < 1 := by
  norm_num

def TopPowerDiagonal.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (D : ℕ) (e a : Fin D → R), (∀ j, e j ^ 2 = 0) →
    (∑ j, a j * e j) ^ D = (D.factorial : R) * (∏ j, a j) * ∏ j, e j

abbrev sqZeroPair : Fin 2 → DualNumber (DualNumber ℚ) :=
  ![TrivSqZeroExt.inl DualNumber.eps, DualNumber.eps]

example : (∀ j, sqZeroPair j ^ 2 = 0) ∧ ∏ j, sqZeroPair j ≠ 0 := by
  refine ⟨?_, ?_⟩
  · intro j
    fin_cases j
    · simp [sqZeroPair, pow_two, ← TrivSqZeroExt.inl_mul]
    · simp [sqZeroPair, pow_two]
  · rw [Fin.prod_univ_two]
    intro h
    have h1 := congrArg TrivSqZeroExt.snd h
    have h2 : (sqZeroPair 0 * sqZeroPair 1).snd = DualNumber.eps := by
      simp only [sqZeroPair, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, DualNumber.fst_eps,
        DualNumber.snd_eps, smul_zero, add_zero, smul_eq_mul, mul_one]
    rw [h2, TrivSqZeroExt.snd_zero] at h1
    exact absurd (congrArg TrivSqZeroExt.snd h1) (by rw [DualNumber.snd_eps, TrivSqZeroExt.snd_zero]; exact one_ne_zero)

def TopPowerPairs.Statement : Prop :=
  ∀ (R ι : Type) [CommRing R] (P : Finset (ι × ι)) (e : ι × ι → R) (lam : ι → R),
    (∀ p ∈ P, e p ^ 2 = 0) →
    (∑ p ∈ P, (lam p.1 - lam p.2) * e p) ^ P.card =
      (P.card.factorial : R) * (∏ p ∈ P, (lam p.1 - lam p.2)) * ∏ p ∈ P, e p

def pairsLT (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun p => p.1 < p.2

def TopPowerPairsVandermonde.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (N : ℕ) (e : Fin N × Fin N → R) (lam : Fin N → R),
    (∀ p ∈ pairsLT N, e p ^ 2 = 0) →
    (∑ p ∈ pairsLT N, (lam p.1 - lam p.2) * e p) ^ N.choose 2 =
      ((N.choose 2).factorial : R) * RestTerms.vandermondeOf lam * ∏ p ∈ pairsLT N, e p ∧
    RestTerms.vandermondeOf lam = (-1) ^ N.choose 2 * (Matrix.vandermonde lam).det

example : ∀ p ∈ pairsLT 2, (fun _ : Fin 2 × Fin 2 => (DualNumber.eps : DualNumber ℚ)) p ^ 2 = 0 :=
  fun _ _ => by simp [pow_two]

def sum₂ {n : ℕ} (lam : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, C (lam i) * X i

def PolarisationPowers.Statement : Prop :=
  ∀ (n D : ℕ) (A B : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ),
    (∀ lam : Fin n → ℝ, A (sum₂ lam ^ D) = B (sum₂ lam ^ D)) →
    ∀ p ∈ homogeneousSubmodule (Fin n) ℝ D, A p = B p

example : ∀ lam : Fin 2 → ℝ,
    (aeval (fun _ : Fin 2 => (1 : ℝ))).toLinearMap (sum₂ lam ^ 3) =
      (aeval (fun _ : Fin 2 => (1 : ℝ))).toLinearMap (sum₂ lam ^ 3) :=
  fun _ => rfl

def UniformIntegrabilityCore.Hyp (J : ℕ → ℝ → ℝ → ℝ) (j₀ Cst E : ℝ → ℝ) : Prop :=
  (∀ ε t, 0 < ε → 0 < t → J 0 ε t ≤ j₀ ε) ∧ Tendsto j₀ (𝓝[>] 0) (𝓝 0) ∧
    (∀ t₀, 0 ≤ Cst t₀) ∧ Tendsto E (𝓝[>] 0) (𝓝 0) ∧
    ∀ a ε t₀ t, 0 < ε → 0 < t → t ≤ t₀ → J (a + 1) ε t ≤ (1 + Cst t₀) * J a ε t + E t₀

def UniformIntegrabilityCore.Statement : Prop :=
  ∀ (J : ℕ → ℝ → ℝ → ℝ) (j₀ Cst E : ℝ → ℝ), UniformIntegrabilityCore.Hyp J j₀ Cst E →
    ∀ (a : ℕ) (η : ℝ), 0 < η → ∃ ε₀ t₁ : ℝ, 0 < ε₀ ∧ 0 < t₁ ∧
      ∀ ε t, 0 < ε → ε ≤ ε₀ → 0 < t → t ≤ t₁ → J a ε t ≤ η

example : UniformIntegrabilityCore.Hyp (fun a ε t => ε + a * t) id (fun _ => 0) id := by
  have h : Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  refine ⟨fun ε t _ _ => by simp, h, fun _ => le_rfl, h, ?_⟩
  intro a ε t₀ t _ _ ht
  simp only [id, Nat.cast_add, Nat.cast_one]
  nlinarith

def CoefficientwiseLimit.Hyp (n D : ℕ) (F : ℝ → MvPolynomial (Fin n) ℝ) (δ : ℝ → ℝ) (R : ℝ) :
    Prop :=
  (∀ t, 0 < t → t ≤ 1 → (F t).totalDegree ≤ D) ∧ Tendsto δ (𝓝[>] 0) (𝓝 0) ∧ 0 < R ∧
    ∀ t t' (lam : Fin n → ℝ), 0 < t' → t' ≤ t → t ≤ 1 → ‖lam‖ ≤ R →
      |eval lam (F t) - eval lam (F t')| ≤ δ t

def CoefficientwiseLimit.Statement : Prop :=
  ∀ (n D : ℕ) (F : ℝ → MvPolynomial (Fin n) ℝ) (δ : ℝ → ℝ) (R : ℝ),
    CoefficientwiseLimit.Hyp n D F δ R →
    ∃ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ D ∧
      (∀ m, Tendsto (fun t => coeff m (F t)) (𝓝[>] 0) (𝓝 (coeff m P))) ∧
      ∀ lam : Fin n → ℝ, Tendsto (fun t => eval lam (F t)) (𝓝[>] 0) (𝓝 (eval lam P))

example : CoefficientwiseLimit.Hyp 1 1 (fun t => C t * X 0) id 1 := by
  refine ⟨fun t _ _ => ?_, tendsto_nhdsWithin_of_tendsto_nhds tendsto_id, one_pos, ?_⟩
  · exact (totalDegree_mul _ _).trans (by simp [totalDegree_C, totalDegree_X])
  · intro t t' lam ht' htt' _ hlam
    have h0 : |lam 0| ≤ 1 := by
      have := norm_le_pi_norm lam 0
      rw [Real.norm_eq_abs] at this
      linarith
    simp only [eval_mul, eval_C, eval_X, id]
    rw [← sub_mul, abs_mul, abs_of_nonneg (by linarith)]
    nlinarith [abs_nonneg (lam 0)]

def IsSymmetricForm {V : Type*} [AddCommGroup V] [Module ℝ V] {D : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin D => V) ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin D)) (v : Fin D → V), I (v ∘ σ) = I v

def AmplePerturbation.Hyp {V : Type*} [AddCommGroup V] [Module ℝ V] (D : ℕ)
    (I : MultilinearMap ℝ (fun _ : Fin D => V) ℝ) (L : V) : Prop :=
  1 ≤ D ∧ IsSymmetricForm I ∧ 0 < I (fun _ => L)

def AmplePerturbation.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (D : ℕ)
    (I : MultilinearMap ℝ (fun _ : Fin D => V) ℝ) (L : V) (hyp : AmplePerturbation.Hyp D I L)
    (H b : V), ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ →
      (D : ℝ) * I (Function.update (fun _ => L + ε • H) ⟨0, hyp.1⟩ (ε • ((2 : ℝ) • H + b))) <
        I (fun _ => L + ε • H)

example : AmplePerturbation.Hyp 2 (MultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ) (1 : ℝ) := by
  refine ⟨by norm_num, fun σ v => ?_, by simp⟩
  simp only [MultilinearMap.mkPiAlgebra_apply, Function.comp_apply]
  exact Equiv.prod_comp σ v

def weightCoeff (N : ℕ) (lam : ℕ → ℝ) (l : ℕ) : ℝ :=
  if l = N then lam N else lam l - lam (l + 1)

def weightClass {M : Type*} [AddCommGroup M] [Module ℝ M] (N : ℕ) (y : ℕ → M) (lam : ℕ → ℝ) :
    M :=
  ∑ l ∈ Finset.Icc 1 N, weightCoeff N lam l • y l

def swapAdjacent (i : ℕ) (lam : ℕ → ℝ) : ℕ → ℝ :=
  lam ∘ Equiv.swap i (i + 1)

def reflectionDefect {M : Type*} [AddCommGroup M] [Module ℝ M] (y : ℕ → M) (i : ℕ) : M :=
  (1 / 2 : ℝ) • (y (i - 1) + y (i + 1)) - y i

def invariantPart {M : Type*} [AddCommGroup M] [Module ℝ M] (N : ℕ) (y : ℕ → M) (lam : ℕ → ℝ)
    (i : ℕ) : M :=
  ∑ l ∈ (Finset.Icc 1 N).erase i, weightCoeff N lam l • y l +
    weightCoeff N lam i • ((1 / 2 : ℝ) • (y (i - 1) + y (i + 1)))

def invariantCoord (N : ℕ) (lam : ℕ → ℝ) (i l : ℕ) : ℝ :=
  if l + 1 = i ∨ l = i + 1 then weightCoeff N lam l + weightCoeff N lam i / 2
  else weightCoeff N lam l

def ReflectionWeights.Statement : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℝ M] (y : ℕ → M) (N i : ℕ) (lam : ℕ → ℝ),
    y 0 = 0 → 2 ≤ N → 1 ≤ i → i < N →
    weightClass N y lam = invariantPart N y lam i - weightCoeff N lam i • reflectionDefect y i ∧
    weightClass N y (swapAdjacent i lam) =
      invariantPart N y lam i + weightCoeff N lam i • reflectionDefect y i ∧
    invariantPart N y lam i = ∑ l ∈ (Finset.Icc 1 N).erase i, invariantCoord N lam i l • y l ∧
    invariantPart N y (swapAdjacent i lam) i = invariantPart N y lam i

example : (fun l : ℕ => (l : ℝ)) 0 = 0 ∧ 2 ≤ 2 ∧ 1 ≤ 1 ∧ 1 < 2 := by
  norm_num

end

end Proportionality

end GroundTheory.Heights₂.Heights

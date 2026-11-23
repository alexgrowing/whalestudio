import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Imports
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncidenceZeroLocus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartHomogenise.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    Q.IsPrime → linForm t - 1 ∈ Q →
      ∃ W : Ideal (MvPolynomial (Fin n) F), IsProjPrime W ∧ linForm t ∉ W ∧
        W ⊔ Ideal.span {linForm t - 1} = Q ∧
        ∀ J : Ideal (MvPolynomial (Fin n) F), IsHomogIdeal J → J ≤ Q → J ≤ W

def ChartDehomog.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (W : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
    (G : MvPolynomial (Fin n) F) (d : ℕ),
    W.IsPrime → IsHomogIdeal W → linForm t ∉ W → G.IsHomogeneous d →
      G ∈ W ⊔ Ideal.span {linForm t - 1} → G ∈ W

def ComponentOfIncIdeal.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F)) (u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((e + 1 : ℕ) : WithBot ℕ∞) →
      linForm u ∉ I → IsProjPrime W → I ⊔ Ideal.span {linForm u} ≤ W → Prime q →
        incIdeal W e ≤ Ideal.span {q} →
          W ∈ relComps (I ⊔ Ideal.span {linForm u}) ∧ incIdeal W e = Ideal.span {q}

section Inhabitants

def pointIdealZeroOne : Ideal (MvPolynomial (Fin 2) ℚ) :=
  RingHom.ker (MvPolynomial.eval ![(0 : ℚ), 1])

theorem ChartHomogenise.hypotheses_inhabited :
    pointIdealZeroOne.IsPrime ∧ linForm tLine - 1 ∈ pointIdealZeroOne := by
  refine ⟨RingHom.ker_isPrime _, ?_⟩
  rw [pointIdealZeroOne, RingHom.mem_ker, linForm_tLine]
  simp

theorem ChartDehomog.hypotheses_inhabited :
    (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}).IsPrime ∧
      IsHomogIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) ∧
      linForm tLine ∉ Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} ∧
      (X 0 : MvPolynomial (Fin 2) ℚ).IsHomogeneous 1 ∧
      (X 0 : MvPolynomial (Fin 2) ℚ) ∈
        Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} ⊔ Ideal.span {linForm tLine - 1} :=
  ⟨(isProjPrime_span_X_zero ℚ).isPrime, (isProjPrime_span_X_zero ℚ).isHomog, linearFormLine_not_mem_span_X0,
    isHomogeneous_X _ _, Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)⟩

def substZeroOne : MvPolynomial (Fin 1 × Fin 2) ℚ →ₐ[ℚ] MvPolynomial (Fin 1 × Fin 2) ℚ :=
  aeval fun ij => if ij = ((0 : Fin 1), (1 : Fin 2)) then 0 else X ij

theorem X_zero_one_dvd_sub_substZeroOne (g : MvPolynomial (Fin 1 × Fin 2) ℚ) : X (0, 1) ∣ g - substZeroOne g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [substZeroOne]
  | add p q hp hq =>
    have e : p + q - substZeroOne (p + q) = (p - substZeroOne p) + (q - substZeroOne q) := by
      simp only [map_add]; ring
    rw [e]; exact dvd_add hp hq
  | mul_X p i hp =>
    have e : p * X i - substZeroOne (p * X i) =
        (p - substZeroOne p) * X i + substZeroOne p * (X i - substZeroOne (X i)) := by
      simp only [map_mul]; ring
    rw [e]
    refine dvd_add (hp.mul_right _) (Dvd.dvd.mul_left ?_ _)
    by_cases hi : i = (0, 1)
    · subst hi; simp [substZeroOne]
    · simp [substZeroOne, hi]

theorem incidenceIdeal_pointZeroOne_le_span :
    incIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 ≤ Ideal.span {qLine} := by
  intro g hg
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hg
  rw [Ideal.mem_span_singleton, qLine]
  have hz : substZeroOne g = 0 := by
    apply MvPolynomial.map_injective (algebraMap ℚ (AlgebraicClosure ℚ)) (algebraMap ℚ _).injective
    rw [map_zero]
    apply MvPolynomial.funext
    intro v
    rw [eval_map, ← aeval_def, map_zero, substZeroOne, ← AlgHom.comp_apply, comp_aeval]
    have hw : (fun ij : Fin 1 × Fin 2 => aeval v (if ij = ((0 : Fin 1), (1 : Fin 2)) then (0 : MvPolynomial (Fin 1 × Fin 2) ℚ) else X ij)) ∈
        incidence (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 := by
      refine ⟨![0, 1], fun h => one_ne_zero (congrFun h 1), fun g hg => ?_, fun i => ?_⟩
      · obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hg
        simp
      · obtain rfl : i = 0 := Subsingleton.elim _ _
        simp [Fin.sum_univ_two]
    exact hg _ hw
  simpa [hz] using X_zero_one_dvd_sub_substZeroOne g

theorem ComponentOfIncIdeal.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      ringKrullDim (MvPolynomial (Fin 2) ℚ ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ))) =
        ((1 + 1 : ℕ) : WithBot ℕ∞) ∧
      linForm uLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsProjPrime (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) ∧
      (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ⊔ Ideal.span {linForm uLine} ≤
        Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} ∧
      Prime qLine ∧
      incIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 ≤ Ideal.span {qLine} :=
  ⟨LineChowForm.isProjPrime_line, ringKrullDim_quot_bot ℚ 2, linForm_uLine_not_mem_bot,
    isProjPrime_span_X_zero ℚ, by rw [bot_sup_eq, linForm_uLine], prime_qLine, incidenceIdeal_pointZeroOne_le_span⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights

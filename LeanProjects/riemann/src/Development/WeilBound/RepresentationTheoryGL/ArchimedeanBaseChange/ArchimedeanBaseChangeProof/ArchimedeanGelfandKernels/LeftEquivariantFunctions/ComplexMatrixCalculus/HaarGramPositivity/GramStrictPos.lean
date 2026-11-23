import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.HasCompactSupportUK

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgBcC.CxeAvg

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem adjoint_clm (lam : Fin n → ℤ) (U : Matrix (Ix n lam) (Ix n lam) ℂ) :
    ContinuousLinearMap.adjoint (clm lam U) = clm lam (star U) := by
  unfold clm
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact (map_star toEuclideanCLM U).symm

theorem gram_comm (hF : MatrixFrechetDerivativeAtZeroLaws) (lam : Fin n → ℤ) (U : Matrix (Ix n lam) (Ix n lam) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Ix n lam) ℂ) (hc : ∀ k : UK n, U * fr0 lam k.1 = fr0 lam k.1 * U) :
    clm lam U * sqQ lam = sqQ lam * clm lam U := by
  have hm : ∀ P Q : Matrix (Ix n lam) (Ix n lam) ℂ, clm lam P * clm lam Q = clm lam (P * Q) :=
    fun P Q => (map_mul toEuclideanCLM P Q).symm
  have hu1 : star U * U = 1 := Unitary.star_mul_self_of_mem hU
  have hu2 : U * star U = 1 := Unitary.mul_star_self_of_mem hU
  have hpt : ∀ k : UK n, clm lam U * Fk lam k = Fk lam k * clm lam U := by
    intro k
    set X := fr0 lam k.1
    have hs : star X * star U = star U * star X := by
      rw [← star_mul, ← star_mul, hc k]
    have hx : U * star X = star X * U := by
      calc U * star X = U * star X * (star U * U) := by rw [hu1, mul_one]
        _ = U * (star X * star U) * U := by simp only [mul_assoc]
        _ = U * (star U * star X) * U := by rw [hs]
        _ = star X * U := by rw [← mul_assoc U, hu2, one_mul]
    simp only [Fk, Ak, adjoint_clm, hm]
    congr 1
    rw [← mul_assoc, hx, mul_assoc, hc k, ← mul_assoc]
  have hint := Fk_int hF lam
  have hL : clm lam U * gramQ lam = ∫ k, clm lam U * Fk lam k ∂(Measure.haar : Measure (UK n)) := by
    rw [gramQ_def]
    exact ((ContinuousLinearMap.mul ℂ _ (clm lam U)).integral_comp_comm hint).symm
  have hR : gramQ lam * clm lam U = ∫ k, Fk lam k * clm lam U ∂(Measure.haar : Measure (UK n)) := by
    rw [gramQ_def]
    exact (((ContinuousLinearMap.mul ℂ _).flip (clm lam U)).integral_comp_comm hint).symm
  have hG : Commute (gramQ lam) (clm lam U) := by
    show gramQ lam * clm lam U = clm lam U * gramQ lam
    rw [hL, hR]
    simp only [hpt]
  exact (Commute.cfcₙ_nnreal hG _).symm.eq

theorem gram_nonneg (hF : MatrixFrechetDerivativeAtZeroLaws) (lam : Fin n → ℤ) : 0 ≤ gramQ (n := n) lam :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (gram_isPositive hF lam)

theorem gram_strictPos (hF : MatrixFrechetDerivativeAtZeroLaws) (lam : Fin n → ℤ) : IsStrictlyPositive (gramQ (n := n) lam) := by
  exact ⟨gram_nonneg hF lam, gram_isUnit hF lam⟩

end PositivityTheory.RgBcC.CxeAvg

namespace PositivityTheory.RgBcC

open PositivityTheory.RgBcC.CxeAvg

theorem avg_of (hF : MatrixFrechetDerivativeAtZeroLaws) : Avg := by
  intro n lam
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsStrictlyPositive.isUnit_cfcSqrt (gramQ lam) (gram_strictPos hF lam)
  · exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  · exact CFC.sqrt_mul_sqrt_self _ (gram_nonneg hF lam)
  · intro k; exact gram_inv hF lam k
  · intro U hU hc; exact gram_comm hF lam U hU hc

end PositivityTheory.RgBcC

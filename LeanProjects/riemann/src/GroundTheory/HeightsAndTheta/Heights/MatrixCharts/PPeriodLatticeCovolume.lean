import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PeriodLatticeCovolume

theorem hermPair_comb {ι : Type*} [Fintype ι] {m : ℕ} (A : Matrix ι ι ℝ) (b : Fin m → ι → ℂ)
    (x y : Fin m → ℝ) :
    hermPair A (∑ a, (x a : ℂ) • b a) (∑ c, (y c : ℂ) • b c) =
      ∑ a, ∑ c, x a * y c * hermPair A (b a) (b c) := by
  unfold hermPair
  simp only [star_sum, star_smul, Complex.star_def, Complex.conj_ofReal, mulVec_sum,
    mulVec_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    Complex.re_sum, Complex.re_ofReal_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem sum_periodBasis {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a n : Fin g → ℤ) :
    ∑ i, ((Fin.append a n i : ℤ) : ℂ) • periodBasis τ i = intVecC a + τ *ᵥ intVecC n := by
  rw [Fin.sum_univ_add]
  simp only [periodBasis, Fin.append_left, Fin.append_right]
  congr 1
  · ext l
    simp [intVecC, Finset.sum_apply, Pi.single_apply]
  · have hs : ∀ x, ((n x : ℤ) : ℂ) • (τ *ᵥ Pi.single x (1 : ℂ)) =
        τ *ᵥ (((n x : ℤ) : ℂ) • Pi.single x (1 : ℂ)) := fun x => (mulVec_smul _ _ _).symm
    simp only [hs]
    rw [← mulVec_sum]
    congr 1
    ext l
    simp [intVecC, Finset.sum_apply, Pi.single_apply]

end PeriodLatticeCovolume

open PeriodLatticeCovolume in

theorem PeriodLatticeCovolume.proof : PeriodLatticeCovolume.Statement := by
  intro g τ k v hv hind
  choose a n han using hv
  let N : Matrix (Fin (g + g)) (Fin k) ℤ := fun i j => Fin.append (a j) (n j) i
  have hN : ∀ j, v j = ∑ i, (N i j : ℂ) • periodBasis τ i := fun j => by
    rw [han j]
    exact (sum_periodBasis τ (a j) (n j)).symm
  refine ⟨N, hN, ?_, ?_⟩
  · intro c hc
    rw [Fintype.linearIndependent_iff] at hind
    funext j
    refine hind c ?_ j
    have : ∀ j, c j • v j = ∑ i, ((c j : ℂ) * (N i j : ℂ)) • periodBasis τ i := fun j => by
      rw [hN j, ← Int.cast_smul_eq_zsmul ℂ, Finset.smul_sum]
      simp only [smul_smul]
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_smul]
    have hi := congrFun hc i
    simp only [mulVec, dotProduct, Pi.zero_apply] at hi
    have : ∑ j, (c j : ℂ) * (N i j : ℂ) = ((∑ j, N i j * c j : ℤ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [this, hi]
    simp
  · unfold covolume
    congr 2
    ext j l
    rw [Matrix.of_apply, hN j, hN l]
    have h1 : ∀ j, ∑ i, (N i j : ℂ) • periodBasis τ i
        = ∑ i, (((N i j : ℝ)) : ℂ) • periodBasis τ i := fun j => by
      simp
    rw [h1 j, h1 l, hermPair_comb]
    simp only [intGram, mul_apply, transpose_apply, map_apply, periodGram, Matrix.of_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
    ring

end

end GroundTheory.Heights₂.Heights

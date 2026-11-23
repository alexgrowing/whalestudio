import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem blockWeight_cast_eq_unitDeg {K : Type} [DecidableEq K] (ι : K → Type) (b : K) (i : ι b) :
    (fun k => ((blockWeight ι ⟨b, i⟩ k : ℕ) : ℤ)) = unitDeg b := by
  funext k
  simp only [blockWeight, unitDeg, Pi.single_apply]
  split_ifs <;> rfl

open Classical in

theorem IntersectionRecursion.proof : IntersectionRecursion.Statement.{u} := by
  intro F _ K _ _ ι _ q d hq hdim b i hX bs
  have : q.IsPrime := hq.isPrime
  set x : MRing ι F := X ⟨b, i⟩ with hxdef
  set J : Ideal (MRing ι F) := q ⊔ Ideal.span {x} with hJdef
  have hx : IsMultiHomog x (blockWeight ι ⟨b, i⟩) := isWeightedHomogeneous_X F _ _

  have hlt : ringKrullDim (MRing ι F ⧸ q) < ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [hdim]
    exact_mod_cast (by omega : d + 1 + Fintype.card K < d + 2 + Fintype.card K)
  have hcut := CutByForm.full F K ι d q hq.isPrime hq.multiHomog hlt x (blockWeight ι ⟨b, i⟩) hx hX bs
  rw [blockWeight_cast_eq_unitDeg] at hcut
  rw [hcut, cycEval]

  have hle : q ≤ J := le_sup_left
  have hr : Ideal.Quotient.mk q x ∈ nonZeroDivisors (MRing ι F ⧸ q) :=
    mem_nonZeroDivisors_of_ne_zero fun h => hX (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hsucc : ringKrullDim (MRing ι F ⧸ J) + 1 ≤ ringKrullDim (MRing ι F ⧸ q) :=
    ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle) hr (by
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_sup_right (Ideal.subset_span rfl))
  rw [hdim] at hsucc
  have hJlt : ringKrullDim (MRing ι F ⧸ J) < ((d + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
    have h := HilbDegBound.lt_of_add_one_le_natCast hsucc
    rwa [show d + 1 + Fintype.card K = d + Fintype.card K + 1 by omega] at h
  have hJh : IsMultiHomogIdeal J := isMultiHomogIdeal_sup_span_of_form hq.multiHomog hx

  refine finsum_congr fun W => ?_
  unfold divCycle
  by_cases hW : W ∈ J.minimalPrimes ∧ IsRelevant W
  · rw [dif_pos hW]
    have hWp : W.IsPrime := hW.1.1.1
    have hWh : IsMultiHomogIdeal W := MinimalPrimeMultiHomog.proof F K ι J W hJh hW.1
    have hWle : ringKrullDim (MRing ι F ⧸ W) ≤ ringKrullDim (MRing ι F ⧸ J) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor hW.1.1.2)
        (Ideal.Quotient.factor_surjective hW.1.1.2)
    by_cases hWd : ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)
    · rw [dif_pos ⟨⟨hWp, hWh, hW.2⟩, hW.1.1.2, hWd⟩]
    · rw [dif_neg fun h => hWd h.2.2]
      have hWlt : ringKrullDim (MRing ι F ⧸ W) < ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
        exact lt_of_le_of_ne
          (HilbDegBound.le_natCast_of_lt_natCast_succ (lt_of_le_of_lt hWle hJlt)) hWd
      rw [IntNumVanish.full F K ι d W hWp hWh (Or.inr hWlt) bs, mul_zero]
  · rw [dif_neg hW, zero_mul, dif_neg]
    rintro ⟨hWq, hJW, hWd⟩
    have : W.IsPrime := hWq.isPrime
    refine hW ⟨TopDimMinimal.full _ J W (d + Fintype.card K) hJW hJlt ?_, hWq.relevant⟩
    rw [hWd]
    exact lt_irrefl _

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

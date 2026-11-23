import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.CoeffScale

open Polynomial UpperTheory.V.Z.Sym.Wt

theorem UpperTheory.V.Z.Sym.Wt.finMH :
    UpperTheory.V.Z.Sym.Wt.FinMH := by
  intro K _ d n
  have hle : MH d n ≤ MvPolynomial.restrictDegree (K × Fin d) ℂ (∑ k, n k) := by
    intro P hP
    rw [MvPolynomial.mem_restrictDegree]
    rintro m hm ⟨k, i⟩
    have h := (memMH K d n P).1 hP m hm k
    calc m (k, i) ≤ ∑ j, m (k, j) :=
          Finset.single_le_sum (f := fun j => m (k, j)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ i)
      _ = n k := h
      _ ≤ ∑ k, n k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

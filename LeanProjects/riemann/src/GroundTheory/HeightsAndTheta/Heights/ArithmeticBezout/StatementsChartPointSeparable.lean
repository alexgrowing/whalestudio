import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.OfFreeParAlgIndep
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LineInhabitant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartParAlgebraic.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (K L : Type) [Field K] [Field L] [Algebra F K] [Algebra K L]
    [Algebra F L] [IsScalarTower F K L] (u : Fin e × Fin n → K) (t : Fin n → F) (η : Fin n → L),
    IntermediateField.adjoin F (Set.range u) = ⊤ → IntermediateField.adjoin K (Set.range η) = ⊤ →
    (∀ i : Fin e, ∑ m, algebraMap K L (u (i, m)) * η m = 0) → ∑ m, algebraMap F L (t m) * η m = 1 →
    ∀ j₀, η j₀ ≠ 0 →
      Algebra.IsAlgebraic
        (Algebra.adjoin (Algebra.adjoin F (Set.range fun m => η m * (η j₀)⁻¹))
          (Set.range fun p : Fin e × {j : Fin n // j ≠ j₀} => algebraMap K L (u (p.1, p.2.1)))) L

def ChartFreeParAlgIndep.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (K L : Type) [Field K] [Field L] [Algebra F K] [Algebra K L]
    [Algebra F L] [IsScalarTower F K L] (u : Fin e × Fin n → K) (t : Fin n → F) (η : Fin n → L),
    AlgebraicIndependent F u →
    IntermediateField.adjoin F (Set.range u) = ⊤ → IntermediateField.adjoin K (Set.range η) = ⊤ →
    (∀ i : Fin e, ∑ m, algebraMap K L (u (i, m)) * η m = 0) → ∑ m, algebraMap F L (t m) * η m = 1 →
    ∀ j₀, η j₀ ≠ 0 →
      Algebra.trdeg F (Algebra.adjoin F (Set.range fun m => η m * (η j₀)⁻¹)) ≤ (e : Cardinal) →
      AlgebraicIndependent (IntermediateField.adjoin F (Set.range fun m => η m * (η j₀)⁻¹))
          (fun p : Fin e × {j : Fin n // j ≠ j₀} => algebraMap K L (u (p.1, p.2.1))) ∧
        Algebra.IsAlgebraic K L

def ChartPointSeparable.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n e : ℕ) (K L : Type) [Field K] [Field L] [Algebra F K]
    [Algebra K L] [Algebra F L] [IsScalarTower F K L] (u : Fin e × Fin n → K) (t : Fin n → F)
    (η : Fin n → L),
    AlgebraicIndependent F u →
    IntermediateField.adjoin F (Set.range u) = ⊤ → IntermediateField.adjoin K (Set.range η) = ⊤ →
    (∀ i : Fin e, ∑ m, algebraMap K L (u (i, m)) * η m = 0) → ∑ m, algebraMap F L (t m) * η m = 1 →
    (∀ j₀, η j₀ ≠ 0 →
      Algebra.trdeg F (Algebra.adjoin F (Set.range fun m => η m * (η j₀)⁻¹)) ≤ (e : Cardinal)) →
      Algebra.IsSeparable K L

section Inhabitants

namespace ChartPointLine

abbrev KL : Type := FractionRing (MvPolynomial (Fin 1 × Fin 2) ℚ)

def uL : Fin 1 × Fin 2 → KL := fun q => algebraMap (MvPolynomial (Fin 1 × Fin 2) ℚ) KL (X q)

def tL : Fin 2 → ℚ := ![0, 1]

def ηL : Fin 2 → KL := ![-(uL (0, 1)) / uL (0, 0), 1]

theorem uL_ne_zero (q : Fin 1 × Fin 2) : uL q ≠ 0 := by
  intro h
  have hinj := IsFractionRing.injective (MvPolynomial (Fin 1 × Fin 2) ℚ) KL
  exact X_ne_zero (R := ℚ) q (hinj (by rw [map_zero]; exact h))

theorem adjoin_ηL : IntermediateField.adjoin KL (Set.range ηL) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  simpa using IntermediateField.algebraMap_mem (IntermediateField.adjoin KL (Set.range ηL)) x

theorem rel_ηL : ∀ i : Fin 1, ∑ m, algebraMap KL KL (uL (i, m)) * ηL m = 0 := by
  intro i
  fin_cases i
  simp only [Fin.sum_univ_two, Algebra.algebraMap_self, RingHom.id_apply, ηL]
  simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one]
  field_simp [uL_ne_zero (0, 0)]
  ring

theorem chart_ηL : ∑ m, algebraMap ℚ KL (tL m) * ηL m = 1 := by
  simp [Fin.sum_univ_two, tL, ηL]

theorem ηL_one_ne_zero : ηL 1 ≠ 0 := by simp [ηL]

theorem trdeg_ηL (j₀ : Fin 2) (hj₀ : ηL j₀ ≠ 0) :
    Algebra.trdeg ℚ (Algebra.adjoin ℚ (Set.range fun m => ηL m * (ηL j₀)⁻¹)) ≤ ((1 : ℕ) : Cardinal) :=
  Vertical.ChartPointTrdeg.full ℚ KL 2 1 ⊥ LineChowForm.D2 LineChowForm.isProjPrime_line
    LineChowForm.isChowForm_line ηL j₀ (fun f hf => by rw [Ideal.mem_bot.1 hf, map_zero]) hj₀

end ChartPointLine

open ChartPointLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights

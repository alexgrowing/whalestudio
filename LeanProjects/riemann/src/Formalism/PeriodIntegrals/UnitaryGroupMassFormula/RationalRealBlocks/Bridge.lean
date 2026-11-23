import Mathlib
import Formalism.PeriodIntegrals.BlockRatReal
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylLeDual
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SumIcoTsubTelescope
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowDivStable
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMap
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowStable

open MvPolynomial Matrix

noncomputable section

namespace PI.BlockRatReal.UnitaryGroupMassFormula

theorem s1 {S : Type} [CommRing S] (φ : ℤ →+* S) (k : ℕ) (ν : Fin k → ℕ) (hν : Antitone ν)
    (f : MvPolynomial (Fin k × Fin k) ℤ) (hf : f ∈ PI.BlockRatReal.weyl ℤ k k le_rfl ν) :
    MvPolynomial.map φ f ∈ PI.BlockRatReal.dualWeyl S k k ν := by
  have hle := Formalism.GradedWeylDivisibility.weylLeDual_of Formalism.GradedWeylDivisibility.highestWeightVectorMem Formalism.GradedWeylDivisibility.dualWeylModuleRowDividedPowerStable
  have h1 : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ k k ν := hle ℤ k k le_rfl ν hν hf
  exact Formalism.GradedWeylDivisibility.dualWeylModuleMap ℤ S φ k k ν f h1

theorem s2 {R : Type} [CommRing R] (k : ℕ) (ν : Fin k → ℕ) (g : Matrix (Fin k) (Fin k) R)
    (f : MvPolynomial (Fin k × Fin k) R) (hf : f ∈ PI.BlockRatReal.dualWeyl R k k ν) :
    Formalism.GradedWeylDivisibility.rowAct R g f ∈ PI.BlockRatReal.dualWeyl R k k ν := by
  have h1 : f ∈ Formalism.GradedWeylDivisibility.dualWeyl R k k ν := hf
  exact Formalism.GradedWeylDivisibility.dualWeylModuleRowActionStable R k k ν g f h1

theorem eval_map_rowAct {LL : Type} [Field LL] (φ : LL →+* ℂ) {k : ℕ} (g : Matrix (Fin k) (Fin k) LL)
    (F : MvPolynomial (Fin k × Fin k) LL) (z : Matrix (Fin k) (Fin k) ℂ) :
    eval (fun x => z x.1 x.2) (MvPolynomial.map φ (Formalism.GradedWeylDivisibility.rowAct LL g F)) =
      eval (fun x => (g.map φ * z) x.1 x.2) (MvPolynomial.map φ F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]

theorem map_map_int {LL : Type} [Field LL] (φ : LL →+* ℂ) {σ : Type} (f : MvPolynomial σ ℤ) :
    MvPolynomial.map φ (MvPolynomial.map (Int.castRingHom LL) f) = MvPolynomial.map (Int.castRingHom ℂ) f := by
  rw [MvPolynomial.map_map, RingHom.ext_int (φ.comp (Int.castRingHom LL)) (Int.castRingHom ℂ)]

end PI.BlockRatReal.UnitaryGroupMassFormula

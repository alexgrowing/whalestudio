import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Laurent

open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.QDer

variable (p : ℕ) [Fact p.Prime]

abbrev qL : Lau p := HahnSeries.single (1 : ℤ) (1 : ℤ_[p])

def thetaFun (f : Lau p) : Lau p := qL p * Formalism.L2.Th1.A.dL f

theorem thetaFun_qL : thetaFun p (qL p) = qL p := by
  have h := Formalism.L2.Th1.A.dL_uPow (R := ℤ_[p]) 1
  simp only [Formalism.L2.Th1.A.uPow] at h
  simp [thetaFun, h, HahnSeries.single_zero_one]

theorem dL_algebraMap (r : ℤ_[p]) : Formalism.L2.Th1.A.dL (algebraMap ℤ_[p] (Lau p) r) = 0 :=
  (Formalism.L2.Th1.A.dLDR ℤ_[p]).map_algebraMap r

def thetaO :=
  letI : Module ℤ_[p] (Lau p) := Algebra.toModule
  GlobalTheory.BK.complDer (k := ℤ_[p]) (pI p)
    { toFun := thetaFun p
      map_add' := fun a b => by simp only [thetaFun, map_add, mul_add]
      map_smul' := fun r f => by
        simp only [thetaFun, Algebra.smul_def, RingHom.id_apply]
        rw [Formalism.L2.Th1.A.dL_mul, dL_algebraMap p r]
        ring
      map_one_eq_zero' := by
        show thetaFun p 1 = 0
        simp [thetaFun, Formalism.L2.Th1.A.dL_one]
      leibniz' := fun a b => by
        show thetaFun p (a * b) = a • thetaFun p b + b • thetaFun p a
        simp only [thetaFun, smul_eq_mul, Formalism.L2.Th1.A.dL_mul]
        ring }

theorem thetaO_qO : thetaO p (qO p) = qO p := by
  rw [thetaO, qO, GlobalTheory.BK.complDer_algebraMap]
  exact congrArg _ (thetaFun_qL p)

theorem thetaO_algebraMap (r : ℤ_[p]) : thetaO p (algebraMap ℤ_[p] (O0 p) r) = 0 :=
  (thetaO p).map_algebraMap r

def thetaZ : Derivation ℤ (O0 p) (O0 p) where
  toFun := thetaO p
  map_add' := map_add _
  map_smul' := fun r x => by
    simp [Algebra.smul_def, Derivation.leibniz]
  map_one_eq_zero' := (thetaO p).map_one_eq_zero
  leibniz' := (thetaO p).leibniz

theorem exists_qDer : ∀ (p : ℕ) [Fact p.Prime], ∃ D : Derivation ℤ (O0 p) (O0 p), D (qO p) = qO p ∧
    ∀ r : ℤ_[p], D (algebraMap ℤ_[p] (O0 p) r) = 0 := fun p _ =>
  ⟨thetaZ p, thetaO_qO p, thetaO_algebraMap p⟩

end GlobalTheory.K5.QDer

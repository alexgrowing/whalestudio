import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

namespace GlobalTheory.FrobStick

theorem hasSubst_line {R : Type} [CommRing R] (t : Fin 3 → R) :
    MvPowerSeries.HasSubst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    rw [map_mul]; exact mul_eq_zero_of_right _ (PowerSeries.constantCoeff_X (R := R))

theorem subst_line_subst {R : Type} [CommRing R] (t : Fin 3 → R) (a : MvPowerSeries (Fin 3) R)
    (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries R) :
    (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (PowerSeries.subst a f : MvPowerSeries (Fin 3) R) : PowerSeries R) =
      PowerSeries.subst (MvPowerSeries.subst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) a : PowerSeries R) f := by
  have has : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => ha
  rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply has (hasSubst_line t)]
  rfl

theorem subst_C_mul_X {R : Type} [CommRing R] (c : R) (f : PowerSeries R) :
    PowerSeries.subst (PowerSeries.C c * PowerSeries.X : PowerSeries R) f = PowerSeries.rescale c f := by
  rw [PowerSeries.rescale_eq_subst, PowerSeries.smul_eq_C_mul]

end GlobalTheory.FrobStick

namespace GlobalTheory.FrobStick

theorem defect_line (R : Type) [CommRing R] (f : Fin 3 → PowerSeries R) (s : PowerSeries R)
    (t : Fin 3 → R) :
    (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (GlobalTheory.FrobStick.defect f s) : PowerSeries R) =
      Matrix.det (Matrix.of fun i j => PowerSeries.rescale (t i) (f j)) -
        2 * PowerSeries.rescale (t 0 + t 1 + t 2) s * PowerSeries.rescale (t 0 - t 1) s *
          PowerSeries.rescale (t 1 - t 2) s * PowerSeries.rescale (t 2 - t 0) s := by
  have hb := hasSubst_line t
  have hlin : ∀ (a : MvPowerSeries (Fin 3) R) (c : R), MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) a =
        (PowerSeries.C c * PowerSeries.X : PowerSeries R) → ∀ g : PowerSeries R,
      (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
        (PowerSeries.subst a g : MvPowerSeries (Fin 3) R) : PowerSeries R) = PowerSeries.rescale c g := by
    intro a c ha h g
    rw [subst_line_subst t a ha, h, subst_C_mul_X]
  have hX : ∀ i, MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) = (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R) :=
    fun i => MvPowerSeries.subst_X hb i
  unfold defect
  rw [← MvPowerSeries.coe_substAlgHom hb]
  simp only [map_sub, map_mul, AlgHom.map_det]

  have hmat : (MvPowerSeries.substAlgHom hb).mapMatrix
      (Matrix.of fun i j => (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) (f j) :
        MvPowerSeries (Fin 3) R)) = Matrix.of fun i j => PowerSeries.rescale (t i) (f j) := by
    refine Matrix.ext fun i j => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPowerSeries.coe_substAlgHom]
    exact hlin _ _ (MvPowerSeries.constantCoeff_X i) (hX i) _
  rw [hmat, map_ofNat]
  simp only [MvPowerSeries.coe_substAlgHom]
  have h3 : MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) =
      (PowerSeries.C (t 0 + t 1 + t 2) * PowerSeries.X : PowerSeries R) := by
    rw [MvPowerSeries.subst_add hb, MvPowerSeries.subst_add hb, hX, hX, hX, map_add, map_add, add_mul, add_mul]
  have hd : ∀ i j : Fin 3, MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (MvPowerSeries.X i - MvPowerSeries.X j : MvPowerSeries (Fin 3) R) =
      (PowerSeries.C (t i - t j) * PowerSeries.X : PowerSeries R) := by
    intro i j
    rw [MvPowerSeries.subst_sub hb, hX, hX, map_sub, sub_mul]
  have c3 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) = 0 := by
    simp
  have cd : ∀ i j : Fin 3, MvPowerSeries.constantCoeff
      (MvPowerSeries.X i - MvPowerSeries.X j : MvPowerSeries (Fin 3) R) = 0 := by
    intro i j; simp
  rw [hlin _ _ c3 h3, hlin _ _ (cd 0 1) (hd 0 1), hlin _ _ (cd 1 2) (hd 1 2), hlin _ _ (cd 2 0) (hd 2 0)]

end GlobalTheory.FrobStick

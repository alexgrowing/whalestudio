import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeCommonAdelicFixatorOfColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNeTopOfContinuousMulEquivSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyLatR
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousSplitCentre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBoundLtTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactLatticeGL
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.GLOneVol

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume GlobalTheory.OneRep.SplitTwist

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem idl_det_eq (k : ℕ) (g : GL (Fin k) (AF F ⊗[F] E)) :
    GlobalTheory.TateConv.idl F E (Matrix.GeneralLinearGroup.det g) = Matrix.GeneralLinearGroup.det (glTens F E k g) := by
  ext
  change GlobalTheory.TateConv.tens F E (g : Matrix (Fin k) (Fin k) (AF F ⊗[F] E)).det =
    ((GlobalTheory.TateConv.tens F E).toRingEquiv.toRingHom.mapMatrix (g : Matrix (Fin k) (Fin k) (AF F ⊗[F] E))).det
  exact RingHom.map_det (GlobalTheory.TateConv.tens F E).toRingEquiv.toRingHom _

variable [IsTotallyComplex E]

theorem absE_det_cR (k : ℕ) (t : ℝ) :
    ((absE F E (Matrix.GeneralLinearGroup.det (cR F E k t)) : ℝ≥0) : ℝ) =
      ideleNorm (E := E) (Matrix.GeneralLinearGroup.det (GlobalTheory.UnitaryBC.splitCentre E k t)) := by
  rw [GlobalTheory.TateConv.absE_eq, idl_det_eq, glTens_cR]
  rfl

end GlobalTheory.GLOneVol

theorem GlobalTheory.GLOneVol.log_absE_det_cR : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyComplex E] (k : ℕ), 1 ≤ k → ∃ a : ℝ, a ≠ 0 ∧ ∀ t : ℝ,
      Real.log ((absE F E (Matrix.GeneralLinearGroup.det (GlobalTheory.GLOneVol.cR F E k t)) : ℝ≥0) : ℝ) = a * t := by
  intro F E _ _ _ _ _ _ k hk
  let D : ℝ →+ ℝ := AddMonoidHom.mk'
    (fun t => Real.log (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (E := E)
      (Matrix.GeneralLinearGroup.det (GlobalTheory.UnitaryBC.splitCentre E k t)))) fun x y => by
      rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_add, map_mul, map_mul,
        Real.log_mul (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _)]
  have hD : Continuous D :=
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleNorm.comp (Matrix.GeneralLinearGroup.continuous_det.comp
      GlobalTheory.OneRep.SplitTwist.continuous_splitCentre)).log fun _ => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _
  have hDt : ∀ t, D t = t * D 1 := fun t => by simpa using map_real_smul D hD t 1
  have hD1 : 0 < D 1 := by
    change 0 < Real.log (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (E := E)
      (Matrix.GeneralLinearGroup.det (GlobalTheory.UnitaryBC.splitCentre E k 1)))
    rw [GlobalTheory.CuspRep.CuspidalL2GL.det_splitCentre_one, map_pow, Real.log_pow]
    exact mul_pos (by exact_mod_cast hk) (Real.log_pos (GlobalTheory.IdeleCovolume.one_lt_ideleNorm_eIdele E))
  refine ⟨D 1, hD1.ne', fun t => ?_⟩
  rw [GlobalTheory.GLOneVol.absE_det_cR, mul_comm]
  exact hDt t

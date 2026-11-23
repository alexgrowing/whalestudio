import Mathlib
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.BcrisPlusHomAlgebraMap
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.BcFrob
import Development.WeilBound.CoreStatements.PeriodRingComparison.AinfInverseMaps.AinfInvMapGOC
import Development.WeilBound.CoreStatements.PeriodRingComparison.RationalRingEquivalences.IsLogCore
import Development.WeilBound.CoreStatements.PeriodRingComparison.TeichmullerLogarithm.LogEps
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.BcrisLogTeichmullerEqT
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.CAFrobAinf

noncomputable section

open GroundTheory.PAdicHodge Formalism.BasicNotions.Loc

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem cPd_eq_cP : cPd l = cP l := rfl

theorem cD_zD (z : ℤ_[l]) :
    cD l (algebraMap ℚ_[l] (Reformulated.AutPerF.BdR l (OC l)) (z : ℚ_[l])) = Formalism.Per6.zD l z := by
  have h0 : algebraMap ℚ_[l] (Reformulated.AutPerF.AinfInv l (OC l)) (z : ℚ_[l]) =
      algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.AinfInv l (OC l))
        (algebraMap ℤ_[l] (Reformulated.AutPerF.Ainf l (OC l)) z) :=
    Reformulated.AutPerF.padicLift_algebraMap l (algebraMap ℤ_[l] (Reformulated.AutPerF.AinfInv l (OC l)))
      (Reformulated.AutPerF.AinfInv.isUnit_p l (R := OC l)) z
  have h1 : algebraMap ℚ_[l] (Reformulated.AutPerF.BdR l (OC l)) (z : ℚ_[l]) =
      algebraMap (Reformulated.AutPerF.BdRPlus l (OC l)) (Reformulated.AutPerF.BdR l (OC l))
        (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.BdRPlus l (OC l))
          (algebraMap ℤ_[l] (Reformulated.AutPerF.Ainf l (OC l)) z)) := by
    change algebraMap (Reformulated.AutPerF.BdRPlus l (OC l)) (Reformulated.AutPerF.BdR l (OC l))
      (algebraMap (Reformulated.AutPerF.AinfInv l (OC l)) (Reformulated.AutPerF.BdRPlus l (OC l))
        (algebraMap ℚ_[l] (Reformulated.AutPerF.AinfInv l (OC l)) (z : ℚ_[l]))) = _
    rw [h0]
    rfl
  rw [h1, cD_algebraMap, cPd_eq_cP, comparison_algebraMap_ainf]
  rfl

theorem isLogA_iff_cP (ε : PreTilt ↥(PadicComplexInt l) l) (y : Reformulated.AutPerF.BdRPlus l (OC l)) :
    IsLogA l ε y ↔ Formalism.Per6.IsLog l ε (cP l y) :=
  isLogA_iff_of_compat l (cP l) (comparison_algebraMap_ainf l) (θD_cP l) ε y

theorem compat_native :
    (∀ z : ℤ_[l], cBc l (algebraMap ℚ_[l] (Reformulated.AutPerF.Bcris l (OC l)) (z : ℚ_[l])) = Formalism.Per6.zB l z) ∧
    (∀ z : ℤ_[l], cD l (algebraMap ℚ_[l] (Reformulated.AutPerF.BdR l (OC l)) (z : ℚ_[l])) = Formalism.Per6.zD l z) ∧
    (∀ y : Reformulated.AutPerF.BdRPlus l (OC l), cD l (algebraMap _ (Reformulated.AutPerF.BdR l (OC l)) y) =
      algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (cP l y)) ∧
    (∀ y : Reformulated.AutPerF.BdRPlus l (OC l), Formalism.Per6.θD l (cP l y) =
      Reformulated.AutPerF.BdRPlus.thetaC l (PadicComplexInt l) y) ∧
    (∀ (g : GQ l) (b : Reformulated.AutPerF.Bcris l (OC l)), cBc l (g • b) = Formalism.Per6.σB g (cBc l b)) ∧
    (∀ (g : GQ l) (x : Reformulated.AutPerF.BdR l (OC l)), cD l (g • x) = Formalism.Per6.σD g (cD l x)) ∧
    (∀ b : Reformulated.AutPerF.Bcris l (OC l), cBc l (Reformulated.AutPerF.Bcris.frob l (OC l) b) = Formalism.Per6.φB l (cBc l b)) ∧
    (∀ (a : ℤ) (x : Reformulated.AutPerF.BdR l (OC l)), x ∈ Reformulated.AutPerF.BdR.fil l (OC l) a ↔ cD l x ∈ Formalism.Per6.FilD l a) ∧
    (∀ (ε : PreTilt ↥(PadicComplexInt l) l) (y : Reformulated.AutPerF.BdRPlus l (OC l)),
      IsLogA l ε y ↔ Formalism.Per6.IsLog l ε (cP l y)) ∧
    (∀ a : Reformulated.AutPerF.Ainf l (OC l), cBc l (algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))
      (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l)) a)) = Formalism.Per6.aB l a) :=
  ⟨cBc_zB l, cD_zD l, fun y => cD_algebraMap l y, θD_cP l, cBc_smul l, cD_gal l, cBc_frob_of l (cA_frob l), cD_fil l, isLogA_iff_cP l, cBc_aB l⟩

end Cmp6

import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section
namespace GlobalTheory.CosDual

variable {D : D7}

theorem symplO_smul_half (S T : HSp D) (e : AE D) (u y : WO S T) (hy : IsHalf (cA D e) y) :
    symplO S T (e • u) y = symplO S T u y := by
  have hc : ∀ c b, cA D (y c b) = e * cA D (y c b) := fun c b => by
    conv_lhs => rw [← hy c b]
    rw [map_mul, GlobalTheory.LatVac.cA_cA]
  unfold symplO
  congr 2
  unfold hO
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl
    (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [Matrix.smul_apply, smul_eq_mul]
  conv_rhs => rw [hc c b]
  ring

theorem half_actO (S T : HSp D) (c : AE D) (h : GA D T) (Y : WO S T) (hY : IsHalf c Y) :
    IsHalf c (actO S T 1 h Y) := by
  have hYe : c • Y = Y := by
    ext a b
    exact hY a b
  have hm : c • actO S T 1 h Y = actO S T 1 h Y := by
    unfold actO
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hYe]
  intro a b
  exact congrFun (congrFun hm a) b

theorem actO_add (S T : HSp D) (h : GA D T) (Y Y' : WO S T) :
    actO S T 1 h (Y + Y') = actO S T 1 h Y + actO S T 1 h Y' := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem actO_inv (S T : HSp D) (h : GA D T) (y : WO S T) :
    actO S T 1 h (actO S T 1 h⁻¹ y) = y := by
  have h1 : Formalism.L2.Theta.mt T h * Formalism.L2.Theta.mt T h⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    first
      | rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
      | simp
  unfold actO
  simp [← Matrix.mul_assoc, h1]

end GlobalTheory.CosDual

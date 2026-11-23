import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SupportCompat
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsRc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SuppIne
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
namespace UpperTheory.One.M
open GlobalTheory GlobalTheory.SerSys GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.SplitWeil
theorem supportCompat_alt_alt : GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v)) (fun π : Supp.GLRep _ => rc k v π.1 π.2) := by
  intro hZ hL D T I rc hrc k v π hi hs
  obtain ⟨L, y, hind, -, hsup, hf⟩ := GlobalTheory.SerSys.SuppTame.chain hZ (D.host.g k) π hi hs
  refine ⟨_, inInd_reps hind y hf, fun ρ hρ => ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hρ
    have hc := hsup.isCusp (Multiset.mem_coe.2 hx)
    exact ⟨hc.1, Ysupp.IrreducibleSupport.isIrrRep_of_isIrreducible (IrrRep.irr _),
      GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal ℚ_[D.host.g k] x.1 _ x.rep hc.2⟩
  show D.naut.inePol (rc k v π.1 π.2) (D.ntypes.tg k v) = _
  rw [_root_.GlobalTheory.SuppIne.ine_pol_rc_eq_prod_of_has_support hL D T I rc hrc k v π y hsup, List.map_map]
  rfl
end UpperTheory.One.M
end

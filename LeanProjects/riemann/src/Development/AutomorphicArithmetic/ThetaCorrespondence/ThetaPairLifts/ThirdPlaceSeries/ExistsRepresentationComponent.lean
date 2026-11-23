import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepresentationComponent
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SglobDzBigDef
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodFTAllOfLocal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsRc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameParamRecordLe
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.CoefDuty GlobalTheory.TypeRec
attribute [local instance] GlobalTheory.TypeRec.factG
namespace DiscreteGroups.sglob.DzType.Rt
set_option maxHeartbeats 2000000 in
theorem goodFTAll_pinned_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp), _root_.GlobalTheory.CoefDuty.OPinAlt a → (∀ (I : Ident a.nt.D) cp, IsComp I a.nt.rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g a.nt.D.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom a.nt.D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom a.nt.D.ntypes.e0 x = x) → GoodFTAll D := by
  intro hG hZ hDZ hL D cf nch tp a hp hloc
  have h0 : GoodFTAll a.nt.D := by
    refine _root_.DiscreteGroups.sglob.DzType.Rt.goodFTAll_of_local_alt hG hZ hL a.nt.D a.nt.A.wdT a.nt.A.row a.nt.rep
      (fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) a.nt.row a.depth hp.lab
      (fun k => @GlobalTheory.DepthZeroCusp.depthZeroCuspidal (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) ?_ hloc
    intro I rc hrc k v
    refine _root_.DiscreteGroups.sglob.DzType.Rt.tame_param_le_of_tame_coupled hDZ hL a.nt.D a.nt.A.wdT I rc hrc (fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) k v (a.nt.A.grp.kv k v) ?_
    rw [← hp.gen k]
    exact a.nt.A.grp.tg_tame k v
  have e : ∀ D', D' = withLoc a.nt.L → GoodFTAll D' := by
    rintro _ rfl
    exact h0
  exact e D a.nt.eq
set_option maxHeartbeats 1000000 in
theorem exists_representation_component_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp), _root_.GlobalTheory.CoefDuty.OPinAlt a → (∀ (I : Ident a.nt.D) cp, IsComp I a.nt.rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g a.nt.D.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom a.nt.D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom a.nt.D.ntypes.e0 x = x) → GoodFTAll D :=
  _root_.DiscreteGroups.sglob.DzType.Rt.goodFTAll_pinned_alt
end DiscreteGroups.sglob.DzType.Rt
end

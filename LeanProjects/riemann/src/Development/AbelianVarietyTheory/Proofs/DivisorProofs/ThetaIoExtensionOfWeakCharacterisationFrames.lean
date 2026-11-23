import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsModelHolomorphicIntegralExtremalWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeSmoothModelsOnThetaTargets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorsHolomorphicModelUniqueUpToPhase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeChoiceClausesOfWeakCharacterisationAtFaceAl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IoExtCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VStdOfOrthonormalSpan
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IoExtStd

theorem thetaIoExtension_of_weakCharacterisation_frames : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ i, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧ (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)) → IoExt R.toRealDat := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hC hE hF
  have hB := GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face D G Pl0 I0 T0 A3 Ks R F hC hE
  have hcore := hB.1
  have hsh := GlobalTheory.DefLift.holShape_fixed D G Pl0 T0 A3.A Ks R.toRealDat hcore.models.order
  exact GlobalTheory.AdTh.IoExtCore.ioExt_core D G Pl0 T0 A3.A Ks R.toRealDat F.lv2 hcore
    (fun i => GlobalTheory.StdFrame.vStd_of_orthonormal_span D i (hF i))
    (fun i => ⟨GlobalTheory.LowSmooth.lowSm_MW D G Pl0 T0 A3.A Ks R.toRealDat i _,
      GlobalTheory.HolLowOnce.extLine_of_holShape D _ _ _ (hsh i).1⟩)

end GlobalTheory.IoExtStd

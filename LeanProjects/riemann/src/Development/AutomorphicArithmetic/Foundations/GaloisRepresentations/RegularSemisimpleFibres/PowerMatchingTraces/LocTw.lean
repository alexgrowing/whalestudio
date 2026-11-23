import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocFlath
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.IsLocCompTwistFills

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.locTw :
    UpperTheory.Gal.InertialTypesAlt.G.LocTw := by
  intro K _ _ _ n _ π χ v τ hτ
  have h' : (π.twist χ).IsLocComp v (τ.twist (CuspSub.locDet n χ v) (CuspSub.isOpen_ker_locDet χ v)) :=
    PositivityTheory.RSHS.LocalComponentTwist.isLocComp_twist π χ hτ
  refine ⟨⟨_, h'⟩, fun τ₁ h₁ => ?_⟩
  obtain ⟨e⟩ := GlobalTheory.CuspRep.LocUniq.isLocComp_unique (π.twist χ) v _ τ₁ h' h₁
  refine ⟨e.toLinearEquiv, fun g x => ?_⟩
  exact LinearMap.congr_fun (e.isIntertwining' g) x

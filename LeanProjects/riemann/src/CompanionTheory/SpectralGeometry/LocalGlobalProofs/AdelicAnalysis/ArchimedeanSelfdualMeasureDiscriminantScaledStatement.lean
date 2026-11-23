import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanSelfdualMeasureDiscriminantScaled
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SelfdualMeasureTransportEquivStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_selfdual_measure_discriminant_scaled : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ laminf : Measure (Ainf F), IsStdInf laminf → SelfDual (Real.toNNReal (Real.sqrt |(discr F : ℝ)|) • laminf) (fun s t => psiInf F (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar F)) (s * t)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.selfDual_psiInf_std | exact GlobalTheory.CompanionTheory.SW.selfDual_psiInf_std | (intros; apply GlobalTheory.CompanionTheory.SW.selfDual_psiInf_std <;> assumption)

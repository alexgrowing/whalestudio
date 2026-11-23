import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adelic_lattice_iff_local_selfDual_completion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (V : HSpace E) (y : Fin V.rank → Af F ⊗[F] E), y ∈ Formalism.MainNotions.StandardLattice.latHat F E {x : Fin V.rank → E | ∑ i, x i • V.frame i ∈ V.L0} ↔ ∀ v : HeightOneSpectrum (𝓞 F), (fun i => Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (y i)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := by
  first | exact @GlobalTheory.LatticeLocalGlobal.mem_latHat_iff | exact GlobalTheory.LatticeLocalGlobal.mem_latHat_iff | (intros; apply GlobalTheory.LatticeLocalGlobal.mem_latHat_iff <;> assumption)

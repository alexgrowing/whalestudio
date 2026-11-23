import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CsdMonoOddLitN
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ResidualAutomorphyOfLinkedEnds
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HilbertEisensteinWeightOneHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.MinimalHyp6
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.LocalFieldEmbeddingMem
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.LocalEmbeddingAgree
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.LocalEmbeddingCompatibleExtension
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.AuxStatement23
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.LocalEmbeddingRestrictExtension
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.AlgSatPow
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsSide
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InfiniteQuadraticFieldsSplitInertia
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InertiaLeRangeOfUnramified
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.EventuallyHasSatakeParameters
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.HasFixedOfHasSat
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ComplexConjAlgebraMap
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.GaloisRepPatchingInfiniteFamily
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.QuadraticBaseChangeRegularPolarized
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.EqOfMultisetSymmetricReflections
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.ExistsPrimeIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.BaseChangeNorms.SeedII
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.BaseChangeNorms.MixSeed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.BaseChangeNorms.ClosedOneU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IndGlue
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadLiftRealToComplexOfBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SymmetricCubeUnits.IsOpenKerKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SymmetricCubeUnits.ExistsSymmetricPairingAdjointZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SymmetricCubeUnits.SeedIII
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ClozelConjC
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsHilbertModularFormCongrOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.PropEG2

open NumberField Formalism.GaloisCohomology UpperTheory.Top

namespace UpperTheory.V.Z.Bc

open UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.HV UpperTheory.V.Lit

instance : Coe DescQ ImagQuadraticDescentGL2 := ⟨imagQuadDescent_of_descentQ⟩

structure HypothesesB : Prop where
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  descU : Z.Desc.DescWeak
  cyc : CycC
  desc2 : ImagQuadraticDescentGL2
  lift2 : QuadBC2

theorem cyclicLiftRankTwo_of_cyclic_base_change (h : CycC) : CyclicBaseChangeLiftRankTwo := by
  intro F E _ _ hF _ _ hE _ _ hp π hr
  rcases (h F E hp hF 2 one_le_two).1 _ _ (Or.inl ⟨hF, π, rfl, rfl⟩)
    (fun τ => ⟨_, GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (GlobalTheory.CuspRep.CG.mk π) τ, hr τ⟩) with h1 | ⟨sat', inf', hc, hw, hi⟩
  · exact Or.inl h1
  · rcases hc with ⟨_, P, rfl, rfl⟩ | ⟨hR, -⟩
    · exact Or.inr ⟨P, hi, hw⟩
    · obtain ⟨v⟩ : Nonempty (InfinitePlace E) := inferInstance
      exact absurd (hR.isReal v) (InfinitePlace.not_isReal_iff_isComplex.2 (hE.isComplex v))

end UpperTheory.V.Z.Bc

import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCdvrMkLeContinuum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionOfDimOneNormal
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.LocalCompletion

open IsLocalRing

theorem exists_cDvr_embedding : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O], IsIntegrallyClosed O → IsNoetherianRing O → ringKrullDim O = 1 → CharZero O → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (g : O →+* W), CDvr W ∧ Function.Injective g ∧ IsLocalHom g := by
  intro O _ _ _ hic hn hd h0
  haveI := hic
  haveI := hn
  haveI : IsDiscreteValuationRing O := GlobalTheory.CdvrExt.isDVR_of_ringKrullDim_eq_one hd
  have hinj := GlobalTheory.algebraMap_adicCompletion_injective_of_dvr O
  haveI : CharZero (AdicCompletion (maximalIdeal O) O) := charZero_of_injective_algebraMap hinj
  refine ⟨AdicCompletion (maximalIdeal O) O, inferInstance, inferInstance, inferInstance,
    algebraMap O (AdicCompletion (maximalIdeal O) O), ?_, hinj, inferInstance⟩
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.LocalCompletion

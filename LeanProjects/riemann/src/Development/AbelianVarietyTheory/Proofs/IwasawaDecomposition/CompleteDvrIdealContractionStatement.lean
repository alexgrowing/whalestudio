import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompleteDvrIdealContraction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_dvr_ideal_contraction : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O], IsIntegrallyClosed O → IsNoetherianRing O → ringKrullDim O = 1 → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (g : O →+* W), Function.Injective g → IsLocalHom g → ∀ (I : Ideal O) (a : O), g a ∈ I.map g → a ∈ I := by
  first | exact @GlobalTheory.MemberReflect.mem_of_map_mem_map | exact GlobalTheory.MemberReflect.mem_of_map_mem_map | (intros; apply GlobalTheory.MemberReflect.mem_of_map_mem_map <;> assumption)

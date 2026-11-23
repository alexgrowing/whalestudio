import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStalkIdealOfCodimOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_stalk_ideal_of_codim_one : ∀ (V : Scheme.{0}) (I : V.IdealSheafData), (∀ v : V, IsDomain (V.presheaf.stalk v) ∧ IsIntegrallyClosed (V.presheaf.stalk v) ∧ IsNoetherianRing (V.presheaf.stalk v)) → (∀ v : V, (FinalTheorems.stalkId I v).IsPrincipal) → ∀ s : Γ(V, ⊤), (∀ v : V, ringKrullDim (V.presheaf.stalk v) ≤ 1 → (V.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v) → ∀ v : V, (V.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v := by
  first | exact @GlobalTheory.PrincipalHartogs.mem_stalkId_of_forall_ringKrullDim_le_one | exact GlobalTheory.PrincipalHartogs.mem_stalkId_of_forall_ringKrullDim_le_one | (intros; apply GlobalTheory.PrincipalHartogs.mem_stalkId_of_forall_ringKrullDim_le_one <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

namespace GlobalTheory.DeRham

theorem hdR_free_of_dvr (H : GlobalTheory.Published.AbelianDeRham) (F : Type) [Field F] [NumberField F]
    (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Obj F 𝔠 (Sp R)) : ∃ n : ℕ, Nonempty (HdR X.A ≃ₗ[R] (Fin n → R)) := by
  letI := X.grp
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim H.1 X.ab X.dim
  haveI := hfin
  haveI := hproj
  haveI : Module.Free R (primDR X.A) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Free R (HdR X.A) := inferInstanceAs (Module.Free R (Module.Dual R (primDR X.A)))
  haveI : Module.Finite R (HdR X.A) := inferInstanceAs (Module.Finite R (Module.Dual R (primDR X.A)))
  let b := Module.Free.chooseBasis R (HdR X.A)
  exact ⟨Fintype.card (Module.Free.ChooseBasisIndex R (HdR X.A)),
    ⟨b.equivFun.trans (LinearEquiv.funCongrLeft R R (Fintype.equivFin _).symm)⟩⟩

end GlobalTheory.DeRham

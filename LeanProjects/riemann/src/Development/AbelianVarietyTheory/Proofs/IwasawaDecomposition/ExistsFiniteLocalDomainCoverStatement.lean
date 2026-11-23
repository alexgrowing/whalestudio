import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteLocalDomainCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_local_domain_cover : ∀ (R₀ A R' : Type) [CommRing R₀] [IsLocalRing R₀] [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing R'] [IsLocalRing R'] (φ : R₀ →+* A) (ρ : R₀ →+* R'), IsCN A → IsLocalHom φ → Function.Injective ρ → ρ.Finite → ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (ι : A →+* A₁) (σ : R' →+* A₁), IsCN A₁ ∧ Function.Injective ι ∧ ι.Finite ∧ IsLocalHom ι ∧ IsLocalHom σ ∧ σ.comp ρ = ι.comp φ := by
  first | exact @GlobalTheory.LocExt.exists_isCN_common_of_finite | exact GlobalTheory.LocExt.exists_isCN_common_of_finite | (intros; apply GlobalTheory.LocExt.exists_isCN_common_of_finite <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpecMorphismEqOfLocalInjective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
open AlgebraicGeometry CategoryTheory Limits IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_morphism_eq_of_local_injective : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] (φ : A →+* R),
    Function.Injective φ → IsLocalHom φ → ∀ (S : Scheme.{0}) (f g : Sp A ⟶ S), spMap φ ≫ f = spMap φ ≫ g → f = g := by
  first | exact @GlobalTheory.ExtLocal.eq_of_spMap_comp_eq | exact GlobalTheory.ExtLocal.eq_of_spMap_comp_eq | (intros; apply GlobalTheory.ExtLocal.eq_of_spMap_comp_eq <;> assumption)

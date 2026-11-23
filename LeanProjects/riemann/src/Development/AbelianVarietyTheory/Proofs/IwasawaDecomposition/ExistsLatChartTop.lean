import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsLocalTangentFrames

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
open GlobalTheory.LieMet (tanOf isTan_tv tan_ext isTan_map)
open GlobalTheory.LocM.StepBasis GlobalTheory.GradedPieces GlobalTheory.Points

namespace GlobalTheory.LocM.TopChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem tanEv_map {X : Scheme.{0}} {t : SAB H X} {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X} {V : X.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ V) {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) (φ : S →+* T) {x' : Sp T ⟶ X}
    (hx : spMap φ ≫ x = x') (h' : ⊤ ≤ x' ⁻¹ᵁ V) (s : Γ(GlobalTheory.LieVB.omega t.G, V)) :
    tanEv t (isTan_map φ hx hv) h' s = φ (tanEv t hv h s) := by
  subst hx
  exact GlobalTheory.LocM.tanEv_baseChange E H X t S x V h v hv T φ _ h' s

end GlobalTheory.LocM.TopChart

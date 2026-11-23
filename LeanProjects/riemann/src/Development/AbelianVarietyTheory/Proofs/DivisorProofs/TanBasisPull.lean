import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailMore
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisMovesAlongSemiAbelianTripleMap
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BasisPull

theorem tanBasis_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (T : SAB H X) (t : SAB H X') (g : X' ⟶ X) (φ : SABMap t T g) (U : X.affineOpens) (U' : X'.affineOpens) (hU : U'.1 ≤ g ⁻¹ᵁ U.1) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ T.G.left)) (v' : Fin n → (Sp (DualNumber Γ(X', U'.1)) ⟶ t.G.left)), (∀ i, IsTanAtG T (chart U) (v i)) → (∀ w, IsTanAtG T (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG T (chart U) v cf w) → (∀ i, IsTanAtG t (chart U') (v' i)) → (∀ i, v' i ≫ φ.φ = spMap (dualMap (g.appLE U.1 U'.1 hU).hom) ≫ v i) → ∀ w, IsTanAtG t (chart U') w → ∃! cf : Fin n → Γ(X', U'.1), IsCombAtG t (chart U') v' cf w := by
  intro E _ _ _ H X X' T t g φ U U' hU n v v' hv hvb hv' hvv' w hw
  have hx : chart U' ≫ g = spMap (g.appLE U.1 U'.1 hU).hom ≫ chart U :=
    (IsAffineOpen.SpecMap_appLE_fromSpec g U.2 U'.2 hU).symm
  obtain ⟨v'', hv''φ, hv''t, hv''b⟩ :=
    GlobalTheory.SabTan.tanBasis_sabMap E H X X' T t g φ _ _ (g.appLE U.1 U'.1 hU).hom (chart U) (chart U')
      hx n v hv hvb
  have heq : v'' = v' := by
    funext i
    apply φ.cart.1.hom_ext
    · rw [hv''φ, hvv']
    · rw [(hv''t i).1, (hv' i).1]
  rw [← heq]
  exact hv''b w hw

end GlobalTheory.BasisPull

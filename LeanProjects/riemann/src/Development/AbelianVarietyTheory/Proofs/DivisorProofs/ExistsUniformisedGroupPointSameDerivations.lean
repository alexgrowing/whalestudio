import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantVectorFieldSemiAbelianTripleAffinStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTangentBasisOfRaynaudBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointFromFormalRaynaudPointSameDerivaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfInvariantDerivativesVanishSemiAbelianStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalPointG

theorem exists_point_sameDerivations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → Function.Injective φ → ∀ (hx : x ≫ Y.H.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∃ (x' : Sp Ω ⟶ t.G.left) (hx' : x' ≫ t.G.hom = spMap φ) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) ∧ (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) ∧ (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) ∧ GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ _ _
  letI := H.starRing
  intro Y n vH dd hdd v' hv' Ω _ _ _ φ x δ hΩ hφ hx hδ hxd
  haveI := hΩ
  obtain ⟨x', hx'p, -⟩ :=
    GlobalTheory.FormalPoint.existsUnique_isPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx))
  choose dd' hdd' using fun a => GlobalTheory.T.exists_invariant_vectorField_semiAbelian_triple_affine E H R t (v' a)
  have hpt : GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx))
      (Over.homMk x'.left (Over.w x')) := hx'p
  have hder := GlobalTheory.T.uniformised_point_from_formal_raynaud_point_same_derivations E H R t P Y n (fun a => vH a) dd hdd v' hv' dd' hdd' Ω φ x δ hΩ hx hδ hxd x'.left
    (Over.w x') hpt
  obtain ⟨b, hb⟩ := GlobalTheory.T.uniformisedTangentBasis_of_raynaudBasis E H R t P Y n vH v' hv'
  refine ⟨x'.left, Over.w x', dd', hdd', hder, ?_, hpt⟩
  intro O f hO h0
  refine GlobalTheory.T.eq_zero_of_invariantDerivatives_vanish_semiAbelian R t.G t.semi n b dd' (fun a => (hb a).symm ▸ hdd' a) Ω φ hφ x'.left (Over.w x') O f hO
    fun l => ?_
  have key : ∀ l : List (Fin n), valR x'.left O (l.foldr (fun a g => dd' a O g) f) =
      l.foldr (fun a w => δ a w) (valR x'.left O f) := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.foldr_cons]; rw [hder a O _ hO, ih]
  rw [key, h0]
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons]; rw [ih, map_zero]

end GlobalTheory.FormalPointG

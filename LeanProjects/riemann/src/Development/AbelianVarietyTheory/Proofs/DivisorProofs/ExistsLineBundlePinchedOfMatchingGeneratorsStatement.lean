import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePinchedOfMatchingGenerators
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_pinched_of_matching_generators : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), i' ≫ p = p' ≫ i → GlobalTheory.Pinch.UnitsPatch p i i' p' → ∀ (L' : LB X') (N : LB Z), L'.IsLB → N.IsLB → ∀ (w : LB.Iso (L'.pull i') (N.pull p')) (W : X → X.Opens) (a : ∀ x k, Γ(X', p ⁻¹ᵁ (W x) ⊓ L'.U k)ˣ) (b : ∀ x l, Γ(Z, i ⁻¹ᵁ (W x) ⊓ N.U l)ˣ), (∀ x, x ∈ W x) → (∀ x, GlobalTheory.Pinch.LocGen L' (p ⁻¹ᵁ (W x)) (a x)) → (∀ x, GlobalTheory.Pinch.LocGen N (i ⁻¹ᵁ (W x)) (b x)) → (∀ x, GlobalTheory.Pinch.Matches i' p' w (a x) (b x)) → ∃ L : LB X, L.IsLB ∧ LBIso (L.pull p) L' := by
  first | exact @GlobalTheory.Pinch.exists_lb_of_matching_gens | exact GlobalTheory.Pinch.exists_lb_of_matching_gens | (intros; apply GlobalTheory.Pinch.exists_lb_of_matching_gens <;> assumption)

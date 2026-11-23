import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormLineBundleDescent
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_line_bundle_descent : ∀ {X Y : Scheme.{0}} (q : X ⟶ Y), IsFinite q → ∀ (N : ∀ V : Y.Opens, Γ(X, q ⁻¹ᵁ V) →* Γ(Y, V)), (∀ (V W : Y.Opens) (h : W ≤ V) (a : Γ(X, q ⁻¹ᵁ V)), (Y.presheaf.map (homOfLE h).op).hom (N V a) = N W ((X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ V from fun _ hx => h hx)).op).hom a)) → (∀ (V : Y.Opens) (a : Γ(X, q ⁻¹ᵁ V)) (y : Y), y ∈ V → (y ∈ Y.basicOpen (N V a) ↔ ∀ x : X, q x = y → x ∈ X.basicOpen a)) → ∀ L : LB X, L.IsLB → (∀ y : Y, ∃ W : X.Opens, (∀ x : X, q x = y → x ∈ W) ∧ ∃ t : (L.pull W.ι).Gen, t.IsGen) → ∃ L' : LB Y, L'.IsLB ∧ ∀ (n : ℕ) (s : (lbPow L n).Sec), ∃ σ : (lbPow L' n).Sec, ∀ y : Y, y ∈ nonzeroLocus σ ↔ ∀ x : X, q x = y → x ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.CompanionTheory.NormLB.exists_normLB | exact GlobalTheory.CompanionTheory.NormLB.exists_normLB | (intros; apply GlobalTheory.CompanionTheory.NormLB.exists_normLB <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleGaloisDescentAbelianVarietyFinit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_galoisDescent_abelianVariety_finite : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K'), i.Finite → ∀ (Γ : Type) [Finite Γ] (s : Γ → (K' ≃+* K')), (∀ g x, s g (i x) = i x) → (∀ y : K', (∀ g, s g y = y) → y ∈ i.range) → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp K')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap i) φ → ∀ L' : LB A'.left, L'.IsLB → (∀ g, ∃ ψ : A'.left ⟶ A'.left, ψ ≫ φ = φ ∧ ψ ≫ A'.hom = A'.hom ≫ spMap (s g).toRingHom ∧ LBIso L' (L'.pull ψ)) → ∃ L : LB A.left, L.IsLB ∧ LBIso L' (L.pull φ) := by
  first | exact @GlobalTheory.Mum.GenDesc.exists_lb_descent_of_finite_aut | exact GlobalTheory.Mum.GenDesc.exists_lb_descent_of_finite_aut | (intros; apply GlobalTheory.Mum.GenDesc.exists_lb_descent_of_finite_aut <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicAbelianLogarithm
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix Filter Topology MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open scoped ContDiff
open scoped CategoryTheory.Obj MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannForm_im_eventually_const_of_continuous_lattice : ∀ (X : Scheme.{0}) (P : PPAS X) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (d : ∀ b, P.RiemannData (y b)) (ε : (Fin m → ℂ) × (Fin P.g → ℂ) → (Sp ℂ ⟶ P.A.left)) (T : (Fin m → ℂ) → ((Fin P.g → ℂ) ≃L[ℂ] (Fin P.g → ℂ))) (l l' : (Fin m → ℂ) → (Fin P.g → ℂ)), IsOpen B → b₀ ∈ B → IsHolTo (B ×ˢ Set.univ) ε → (∀ b ∈ B, ∀ z, ε (b, z) = ((d b).u.ex (T b z)).left ≫ (d b).φ) → ContinuousOn l B → ContinuousOn l' B → (∀ b ∈ B, T b (l b) ∈ (d b).u.Λ ∧ T b (l' b) ∈ (d b).u.Λ) → ∀ᶠ b in nhds b₀, (HermFrame.form (d b).H (T b (l b)) (T b (l' b))).im = (HermFrame.form (d b₀).H (T b₀ (l b₀)) (T b₀ (l' b₀))).im := by
  first | exact @GlobalTheory.RiemannConst.eventually_im_form_eq | exact GlobalTheory.RiemannConst.eventually_im_form_eq | (intros; apply GlobalTheory.RiemannConst.eventually_im_form_eq <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raynaudTorusWeight_zero_invariantField_coeffs : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) →
    ∀ (V : Q.P.A.left.Opens) (δ : Fld Y.H.left), IsField (Y.q.left ⁻¹ᵁ V) δ → (∀ O, O ≤ Y.q.left ⁻¹ᵁ V → ∀ r, δ O (constFn Y.H.hom O r) = 0) →
    (∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (δ _ f)) →
    ∀ c : Fin n → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V), (∀ O, O ≤ Y.q.left ⁻¹ᵁ V → ∀ f, δ O f = ∑ a, rsT (c a) O * dd a O f) →
    ∀ a, IsWt Y 0 _ (c a) := by
  first | exact @GlobalTheory.Heat.CoeffWt.isWt_coeff | exact GlobalTheory.Heat.CoeffWt.isWt_coeff | (intros; apply GlobalTheory.Heat.CoeffWt.isWt_coeff <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionGenericBound
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_intersection_generic_bound : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem), IsFullIntersectionSystem II → Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∀ (S₀ S₁ : Finset ℕ) (sw : Bool), (∀ p ∈ S₀, p.Prime) → (∀ p ∈ S₁, p.Prime) → Disjoint S₁ S₀ → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (Ω : Type) (_ : Field Ω) (_ : Algebra ℚ Ω) (W : CMType H → Type) (_ : ∀ τ, AddCommGroup (W τ)) (_ : ∀ τ, Module Ω (W τ)) (Dc : GroundTheory.Heights₂.Heights.LowerBoundFree.ComponentData II (CMType H) K J Ω W) (Hd : GroundTheory.Heights₂.Heights.LowerBoundFree.HodgeData Dc) (Or : CptOrigin Y S₀ Dc Hd), genPt Or.𝔐.ξ₀ = genPt ξ₀ ∧ Dc.S = S₁ ∧ Dc.j = (if sw then D.q else D.p) ∧ Or.bg = (if sw then Sum.inr else Sum.inl) ∧ Or.𝔐.OmVB ∧ ∀ p ∈ S₀ ∪ S₁, HT.HTFree Or.𝔐 p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_componentData_origin | exact GlobalTheory.CompanionTheory.Ar.exists_componentData_origin | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_componentData_origin <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneous_polys_tangent_basis : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (x₀ : Sp A ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)), IsTanBasis t x₀ e → ∀ q k : ℕ, ∃ (d : ℕ+) (n : ℕ) (B : Fin n → MvPolynomial (Fin k → Fin g) A), (∀ i, (B i).IsHomogeneous d) ∧ (∀ s, ∃ (i : Fin n) (c : ℕ), c ≠ 0 ∧ B i = MvPolynomial.C (c : A) * (MvPolynomial.X s : MvPolynomial (Fin k → Fin g) A) ^ (d : ℕ)) ∧ ∀ (p : ℕ) [Fact p.Prime] (x : A →+* ℂ_[p]), (∀ a, ‖x a‖ ≤ 1) → ∀ (m : ℕ) (hk : k ≤ m) (u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin m → Fin g → ℂ_[p]), LinearIndependent ℂ_[p] a → (∀ l, IsCombAtG t (spMap x ≫ x₀) (fun i => spMap (dualMap x) ≫ e i) (a l) (u l)) → ((d : ℕ) : ℝ) * ∑ l : Fin k, Real.log (GlobalTheory.ShFam.Pad.grNorm t (spMap x ≫ x₀) (lat t p (spMap x ≫ x₀) (decide (p = q))) u (Fin.castLE hk l)) = Real.log (⨆ i, ‖MvPolynomial.eval₂ x (minor a hk) (B i)‖) := by
  first | exact @GlobalTheory.LineNorm.WedgeMax.wedge_norm_max | exact GlobalTheory.LineNorm.WedgeMax.wedge_norm_max | (intros; apply GlobalTheory.LineNorm.WedgeMax.wedge_norm_max <;> assumption)

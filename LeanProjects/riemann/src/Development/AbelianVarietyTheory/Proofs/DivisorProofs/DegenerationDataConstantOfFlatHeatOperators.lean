import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConstantHeatOperatorSymbolInMaximalIdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorsSymbolZeroTorsionPointsHorizontalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitPartPeriodsConstantAlongTangentStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSFlatPer

theorem isConstAlong_of_heat_flat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ c : ℚ, c ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m d) gam ρ (fun i => (c : k) * MvPowerSeries.constantCoeff (q i)) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hlin hab Y n' v' dd hdd D q hq h hb hdef hΘ ρ hρ
  obtain ⟨B', inst, π₁, π₂, h₁, h₂, h₃⟩ := GlobalTheory.T.abelian_part_constant_heat_operator_symbol_in_maximal_ideal E H k m d t P gam hmon hlin hab Y n' v' dd hdd D q hq h hb hdef hΘ ρ hρ
  choose c' hc' using GlobalTheory.T.heatOperators_symbol_zero_torsion_points_horizontal E H k m d t P gam hmon hlin hab Y n' v' dd hdd D q hq h hb hdef hΘ ρ hρ B' π₁ π₂ h₁ h₂ h₃
  obtain ⟨c, hc, w, hw, hrel⟩ := GlobalTheory.T.unitPart_periods_constant_along_tangent E H k m d t P gam hmon hlin hab Y n' v' dd hdd D q hq h hb hdef hΘ ρ hρ B' π₁ π₂ c' h₁ h₂ h₃ hc'
  exact ⟨c, hc, B', inst, π₁, π₂, w, c', h₁, h₂, h₃, hw, hc', hrel⟩

end GlobalTheory.KSFlatPer

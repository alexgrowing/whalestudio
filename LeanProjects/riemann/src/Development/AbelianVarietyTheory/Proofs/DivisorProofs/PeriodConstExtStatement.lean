import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodConstExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefD_pull1_eq_perClD_of_pull1_eq_perCl : ∀ {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) {B₀ D : Type} [CommRing B₀] [CommRing D] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp B₀} {σ₀ : B₀ →+* Hol F₀.V} (r₀ : GlobalTheory.AnPer.Real K₀ s₀ σ₀) {J : Ideal D} (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io) (j : B₀ →+* D) (φ₀ : X₀ ⟶ X₀) (n : IsMor (dp0 B₀) s₀ dl s' j φ₀), φ₀ = 𝟙 X₀ → (∀ b, et (σ₀ b) = io (j b)) → ∀ (c : FirstDeRham s₀) (per : Λ →+ Hol F₀.V), r₀.coef.pull1 c = K₀.perCl per → (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (et.toAddMonoidHom.comp per) := by
  first | exact @GlobalTheory.AnPer.period_const_ext | exact GlobalTheory.AnPer.period_const_ext | (intros; apply GlobalTheory.AnPer.period_const_ext <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodOverRingRestrictFamilyClassStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem period_const_ext : ∀ {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) {B₀ D : Type} [CommRing B₀] [CommRing D] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp B₀} {σ₀ : B₀ →+* Hol F₀.V} (r₀ : GlobalTheory.AnPer.Real K₀ s₀ σ₀) {J : Ideal D} (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io) (j : B₀ →+* D) (φ₀ : X₀ ⟶ X₀) (n : IsMor (dp0 B₀) s₀ dl s' j φ₀), φ₀ = 𝟙 X₀ → (∀ b, et (σ₀ b) = io (j b)) → ∀ (c : FirstDeRham s₀) (per : Λ →+ Hol F₀.V), r₀.coef.pull1 c = K₀.perCl per → (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (et.toAddMonoidHom.comp per) := by
  intro I₀ _ g Λ _ F₀ K₀ R _ et M B₀ D _ _ X₀ s₀ σ₀ r₀ J dl s' π io H j φ₀ n hφ hj c per hc
  refine GlobalTheory.T.period_over_ring_restrict_family_class K₀ K₀ et M et id (fun h ↦ h) (fun _ ↦ RingHom.id _) (fun S ↦ S.T.ρ)
    (fun S f ↦ (S.T.ρ_cst f).trans (S.compat f)) (fun S h ↦ ?_) (fun S S' f ↦ Charts.Hom.close f.1)
    r₀ r₀ dl H j φ₀ n hj (fun k ↦ ?_) c per hc
  · exact (sub_self (S.T.ρ h)).symm ▸ S.T.J.zero_mem
  · subst hφ
    have e : spMap (RingHom.id (Hol (K₀.W k))) = 𝟙 _ := Spec.map_id _
    exact (congrArg (· ≫ r₀.x k) e).trans ((Category.id_comp _).trans (Category.comp_id _).symm)

end GlobalTheory.AnPer

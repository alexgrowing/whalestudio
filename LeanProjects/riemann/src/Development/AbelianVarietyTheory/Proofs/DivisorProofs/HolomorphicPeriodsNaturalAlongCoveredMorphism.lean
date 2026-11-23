import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallChartPairAlongLinearMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodPullbackEqOfChartMapClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPointExtOfIsSeparatedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAnalyticChartsRealizationOfAffineStatement

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem isPeriod_pull1_eq_comap : ∀ {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁} {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V} {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂} {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V} (u₁ : Unif F₁ s₁ σ₁) (u₂ : Unif F₂ s₂ σ₂), X₁.IsSeparated → X₂.IsSeparated → ∀ (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂), (∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) → ∀ (β : B₂ →+* B₁) (φ : X₁ ⟶ X₂) (m : IsMor (dp0 B₂) s₂ (dp0 B₁) s₁ β φ), (∀ x, σ₁ (β x) = Hol.comap b hb hbV (σ₂ x)) → (∀ p : Tot I₁ g₁, p.1 ∈ F₁.V → u₁.E p ≫ φ = u₂.E (b p.1, M p.2)) → ∀ (c : FirstDeRham s₂) (per₂ : Λ₂ →+ Hol F₂.V) (per₁ : Λ₁ →+ Hol F₁.V), IsPeriod u₂ c per₂ → IsPeriod u₁ (m.pull1 c) per₁ → ∀ l, per₁ l = Hol.comap b hb hbV (per₂ (A l)) := by
  intro I₁ _ g₁ Λ₁ _ F₁ B₁ _ X₁ s₁ σ₁ I₂ _ g₂ Λ₂ _ F₂ B₂ _ X₂ s₂ σ₂ u₁ u₂ h₁ h₂ b hb hbV M A hτ β φ m hσ hE
    c per₂ per₁ hp₂ hp₁ l
  obtain ⟨K₁, K₂, κ, hR, hs₁, hs₂, hW, hle⟩ := GlobalTheory.T.exists_small_chart_pair_along_linear_map u₁ u₂ b hb hbV M A hτ
  obtain ⟨r₁, hr₁, -⟩ := GlobalTheory.T.exists_analyticChartsRealization_of_affine u₁ h₁ K₁ hs₁
  obtain ⟨r₂, hr₂, -⟩ := GlobalTheory.T.exists_analyticChartsRealization_of_affine u₂ h₂ K₂ hs₂
  have hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k) := fun k p hp ↦
    ((hb _ (K₁.base k p hp)).comp analyticAt_fst).prod
      (((LinearMap.toContinuousLinearMap M).analyticAt p.2).comp analyticAt_snd)
  have hx : ∀ k, spMap (Hol.comap _ (hΦ k) (hW k)).toRingHom ≫ r₂.x (κ k) = r₁.x k ≫ φ := by
    intro k
    refine GlobalTheory.T.holomorphicPoint_ext_of_isSeparated (K₁.W k) h₂ _ _ fun p hp ↦ ?_
    have e : (Hol.ev p hp).toRingHom.comp (Hol.comap _ (hΦ k) (hW k)).toRingHom =
        (Hol.ev ((b p.1, M p.2) : Tot I₂ g₂) (hW k p hp)).toRingHom := by
      refine RingHom.ext fun f ↦ ?_
      change Hol.ev p hp (Hol.comap _ (hΦ k) (hW k) f) = Hol.ev _ (hW k p hp) f
      rw [Hol.ev_apply, Hol.ev_apply, Hol.fn_comap _ _ _ f hp]
    rw [← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, e, hr₂ (κ k) _ (hW k p hp), hr₁ k p hp,
      hE p (K₁.base k p hp)]
  let per : Λ₁ →+ Hol F₁.V :=
    ((Hol.comap b hb hbV).toRingHom.toAddMonoidHom.comp per₂).comp A
  have key := GlobalTheory.T.period_pullback_eq_of_chartMap_class b hb hbV M A hτ K₁ K₂ κ hΦ hW hle r₁ r₂ β φ m hσ hx c per₂ per (fun _ ↦ rfl)
    (hp₂ K₂ r₂ hr₂)
  have := GlobalTheory.T.periodClass_injective_of_rich_charts K₁ hR per₁ per ((hp₁ K₁ r₁ hr₁).symm.trans key)
  rw [this]
  rfl

end GlobalTheory.AnPer

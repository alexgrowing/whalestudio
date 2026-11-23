import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeformationComplexStatement

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFamily

theorem span_range_eq_top_of_liftSemi {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M M' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] (f : M →ₛₗ[algebraMap R R'] M')
    (h : Function.Surjective (liftSemi f)) : Submodule.span R' (Set.range f) = ⊤ := by
  refine eq_top_iff.2 fun c _ ↦ ?_
  obtain ⟨z, rfl⟩ := h c
  induction z with
  | zero => rw [map_zero]; exact zero_mem _
  | add x y hx hy => rw [map_add]; exact add_mem (hx trivial) (hy trivial)
  | tmul x c => rw [liftSemi_tmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem liftSemi_comp_eq {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M M' M'' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] [AddCommGroup M''] [Module R' M'']
    (f : M →ₛₗ[algebraMap R R'] M') (l : M' →ₗ[R'] M'') (k : M →ₛₗ[algebraMap R R'] M'')
    (e : ∀ c, l (f c) = k c) : ⇑(liftSemi k) = l ∘ liftSemi f := by
  funext z
  induction z with
  | zero => simp
  | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
  | tmul x c => simp only [Function.comp_apply, liftSemi_tmul, map_smul, e]

theorem isBC_augmented : GlobalTheory.Published.AbelianDeRham.BaseChange → GlobalTheory.Published.AbelianDeRham.Rigid → ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (k : GrpMor (dp0 ℂ) (𝟙 _) A₀ κ (spMap π) A₀ (algebraMap ℂ D) (𝟙 _) (Over.Hom.left (𝟙 A₀))), k.IsBC ∧ Submodule.span D (Set.range k.pull) = ⊤ := by
  intro hB hR A₀ _ g hA hg D _ _ π κ hκ hπ k
  obtain ⟨A', _, q, i, hA', hg', hq, hi, e⟩ := GlobalTheory.T.abelian_scheme_deformation_complex A₀ g hA hg D π hπ
  have h1 : Function.Bijective (liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor hq).pull) :=
    (hB ℂ A₀ g hA hg D A' q hq).1
  have h2 := hR D A' g hA' hg' _ κ hκ ℂ π (fun a ↦ ⟨_, hπ a⟩) rfl A₀ i hi
  have h3 : Function.Bijective (liftSemi k.pull) := by
    rw [liftSemi_comp_eq (GlobalTheory.Published.AbelianDeRham.bcMor hq).pull (liftMor κ hi).pull k.pull
      (GrpMor.pull_pull _ _ k (fun _ ↦ rfl) e)]
    exact h2.comp h1
  exact ⟨h3, span_range_eq_top_of_liftSemi _ h3.2⟩

end GlobalTheory.PeriodFamily

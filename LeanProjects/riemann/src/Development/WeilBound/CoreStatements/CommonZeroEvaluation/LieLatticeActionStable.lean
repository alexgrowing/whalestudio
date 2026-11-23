import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace ModelDimension

theorem lie_lattice_action_stable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (tX : SAB H X) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel tX.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li), M.IsActOf tX.act.act ρ → ∀ (q : Cpt ξ) (a : 𝓞 E) (e : Li), e ∈ M.lat q → ρ a e ∈ M.lat q := by
  intro E _ _ _ H X tX Ω _ ξ Li _ _ M ρ hM q a e he
  unfold LieModel.lat at he ⊢
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv1, hv2⟩ := hx
    apply Submodule.subset_span
    refine ⟨v ≫ tX.act.act a, ?_, ?_⟩
    · haveI := tX.act.hom a
      unfold IsTanAt at hv1 ⊢
      rw [Over.comp_left, ← Category.assoc, hv1, ← Over.comp_left, MonObj.one_comp]
    · rw [hM a x, Over.comp_left, hv2, Over.comp_left]
      exact Category.assoc _ _ _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [Subring.smul_def, map_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ r hx

end ModelDimension

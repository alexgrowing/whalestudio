import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem cm_type_label_twist_permutation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (g : HostAut H), ∃ π : CMType H ≃ CMType H, (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) ∧ ∀ s, labelEmb c (Sum.map π π s) = (labelEmb c s).comp g.s.toRingHom := by
  intro E _ _ _ H l c g
  let F : HostAut H → CMType H → CMType H := fun g τ =>
    ⟨τ.1.comp g.σ.toRingHom, by
      show τ.1 (g.σ (H.rt : E)) = _
      rw [g.fix]
      exact τ.2⟩
  refine ⟨⟨F g, F g.symm, fun τ => ?_, fun τ => ?_⟩, fun _ => rfl, ?_⟩
  · refine Subtype.ext (RingHom.ext fun x => ?_)
    show τ.1 (g.σ (g.σ.symm x)) = τ.1 x
    rw [RingEquiv.apply_symm_apply]
  · refine Subtype.ext (RingHom.ext fun x => ?_)
    show τ.1 (g.σ.symm (g.σ x)) = τ.1 x
    rw [RingEquiv.symm_apply_apply]
  · rintro (τ | τ)
    · exact RingHom.ext fun x => Subtype.ext rfl
    · refine RingHom.ext fun x => Subtype.ext ?_
      show τ.1 ((g.s (H.bar x) : 𝓞 E) : E) = τ.1 ((H.bar (g.s x) : 𝓞 E) : E)
      rw [g.s_bar]

end PositivityTheory.UnitarySelfGeneration

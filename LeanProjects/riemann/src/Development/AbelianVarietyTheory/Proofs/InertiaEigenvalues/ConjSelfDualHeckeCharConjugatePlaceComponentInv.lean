import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjGenTransportExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDetStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitaryStatement
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL
namespace GlobalTheory.ConjLocCsd

theorem plMap_conj_eq {R : Ranks} (Hs : Host R) (w w' : HeightOneSpectrum (𝓞 Hs.E)) (h : IsConjPl Hs w w') :
    CT.plMap (Hs.conj : Hs.E ≃+* Hs.E) w = w' := by
  ext y
  set j : Hs.E ≃+* Hs.E := (Hs.conj : Hs.E ≃+* Hs.E)
  set x := (RingOfIntegers.mapRingEquiv j).symm y with hx
  have hy : RingOfIntegers.mapRingEquiv j x = y := by rw [hx, RingEquiv.apply_symm_apply]
  have hyx : (y : Hs.E) = Hs.conj (x : Hs.E) := by rw [← hy]; rfl
  rw [← hy, CT.mem_plMap, hy]
  exact h x y hyx

theorem main : ∀ {R : Ranks} (Hs : Host R) (μ : HChar Hs.E), IsCSD Hs μ → ∀ (w w' : HeightOneSpectrum (𝓞 Hs.E)), IsConjPl Hs w w' → ∃ i : w.adicCompletion Hs.E ≃+* w'.adicCompletion Hs.E, Continuous i ∧ (∀ x, i (algebraMap Hs.E _ x) = algebraMap Hs.E _ (Hs.conj x)) ∧ ∀ x, μ.loc w' (Units.map i.toRingHom.toMonoidHom x) = (μ.loc w x)⁻¹ := by
  intro R Hs μ hμ w w' hc
  have hcsd := hμ.1 w w' hc
  obtain rfl := plMap_conj_eq Hs w w' hc
  set j : Hs.E ≃+* Hs.E := (Hs.conj : Hs.E ≃+* Hs.E) with hj
  set i := CT.compEquiv j w with hi
  have hcont : Continuous i := CT.continuous_compEquiv j w
  have halg : ∀ x, i (algebraMap Hs.E _ x) = algebraMap Hs.E _ (Hs.conj x) := fun x => CT.compEquiv_algebraMap j w x
  refine ⟨i, hcont, halg, ?_⟩
  obtain ⟨ξ, -, huniq, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary Hs.E μ⁻¹ w
  set ψ₁ : (w.adicCompletion Hs.E)ˣ →* ℂˣ := (μ.loc (CT.plMap j w)).comp (Units.map i.toRingHom.toMonoidHom) with hψ₁
  have h1 : IsComp μ⁻¹ w ψ₁ := by
    refine ⟨?_, fun x => ?_⟩
    · have hc' : Continuous (Units.map i.toRingHom.toMonoidHom) := Units.continuous_map hcont
      exact (ParLaws.isSmoothChar_loc μ (CT.plMap j w)).preimage hc'
    · have hu : Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap Hs.E (w.adicCompletion Hs.E)).toMonoidHom x)
          = Units.map (algebraMap Hs.E ((CT.plMap j w).adicCompletion Hs.E)).toMonoidHom (Units.map (Hs.conj : Hs.E ≃+* Hs.E).toRingHom.toMonoidHom x) := by
        apply Units.ext
        exact halg (x : Hs.E)
      rw [hψ₁, MonoidHom.comp_apply, hu]
      have := hcsd x
      exact this
  have h2 : IsComp μ⁻¹ w ((μ⁻¹).loc w) := ⟨ParLaws.isSmoothChar_loc _ w, fun x => rfl⟩
  have he : ψ₁ = (μ⁻¹).loc w := (huniq _ h1).trans (huniq _ h2).symm
  intro x
  have := congrArg (fun f => f x) he
  simpa [hψ₁, HChar.loc_inv] using this

end GlobalTheory.ConjLocCsd

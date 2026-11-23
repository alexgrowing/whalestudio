import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ExponentSeparationLemma.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharacters
import GroundTheory.AutomorphicForms.Satake

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical

namespace GlobalTheory.CompanionTheory.HeckeSub

theorem isSatakeParameter_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (α : Fin n → ℂˣ) (X V : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) X), IsSmooth ρ → ∀ (ι : ρ.IntertwiningMap (principalSeries k n (paramChar k α))), Function.Injective ι → ∀ (π : Representation ℂ (GL (Fin n) k) V), IsSubquotient π ρ → ∀ [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : MeasureTheory.Measure (GL (Fin n) k)) [μ.IsHaarMeasure], IsSatakeParameter π μ α := by
  intro k _ _ _ _ n α X V _ _ _ _ ρ hρ ι hι π hπ _ _ μ _ h v hv
  obtain ⟨S, f, hf⟩ := hπ
  have hS : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth (ρ := ρ) ⟨S, .id _, Function.surjective_id⟩ hρ
  obtain ⟨u, rfl⟩ := hf v
  have hfix : ∀ g ∈ GroundTheory.Automorphic.GLnLocal.integralGL k n, π g (f u) = f u := fun g hg =>
    GroundTheory.Automorphic.mem_fixedVectors.1 hv g hg
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hS
    (GroundTheory.Automorphic.GLnLocal.isCompact_integralGL k n) f.toLinearMap u fun g hg => by
      show f (S.toRepresentation g u) = f u
      rw [f.isIntertwining]
      exact hfix g hg
  have hfw' : f w = f u := hfw
  have hw' : w ∈ GroundTheory.Automorphic.fixedVectors S.toRepresentation
      (GroundTheory.Automorphic.GLnLocal.integralGL k n) := by
    simpa [fixed, eig, GroundTheory.Automorphic.fixedVectors] using hw
  let T : S.toRepresentation.IntertwiningMap (principalSeries k n (paramChar k α)) :=
    ⟨ι.toLinearMap ∘ₗ S.toSubmodule.subtype, fun g => by
      refine LinearMap.ext fun x => ?_
      exact ι.isIntertwining _ _ g x⟩
  have hT : Function.Injective T := fun a b e => Subtype.ext (hι e)
  have hTw : T w ∈ GroundTheory.Automorphic.fixedVectors (principalSeries k n (paramChar k α))
      (GroundTheory.Automorphic.GLnLocal.integralGL k n) :=
    GroundTheory.Automorphic.mem_fixedVectors.2 fun g hg => by
      rw [← T.isIntertwining, GroundTheory.Automorphic.mem_fixedVectors.1 hw' g hg]
  have hmem := (h : GroundTheory.Automorphic.HeckeAlgebra μ).mem
  set c := GroundTheory.Automorphic.Spherical.evalAt α (satakeTransform μ h) with hc
  have hPS := isSatakeParameter_principalSeries (F := k) (μ := μ) α h (T w) hTw
  have hact : GroundTheory.Automorphic.heckeAct μ S.toRepresentation (h : GroundTheory.Automorphic.HeckeAlgebra μ) w = c • w := by
    apply hT
    rw [GroundTheory.Automorphic.map_heckeAct T hmem (hS w), hPS, map_smul]
  rw [← hfw', ← GroundTheory.Automorphic.map_heckeAct f hmem (hS w), hact, map_smul]

end GlobalTheory.CompanionTheory.HeckeSub

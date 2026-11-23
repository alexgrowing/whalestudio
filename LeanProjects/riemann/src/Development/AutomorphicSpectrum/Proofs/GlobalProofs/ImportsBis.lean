import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjMemSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneStrongApproxProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneStrongApproxGeneratorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneStrongApproxHoldsStatement

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem strongApproxSU : GlobalTheory.Published.StrongApproxSU := by
  intro F E _ _ _ _ _ σ hCM M J hM hJ S₁ S₂ ε hε hnc g hg
  obtain ⟨N, hN⟩ := GlobalTheory.CompanionTheory.StrongApproxSub.propSub F E σ M J ε
  have hcl : IsClosed (N : Set (HA (AF F) σ J)) := hN ▸ isClosed_closure
  have hS : SUSupp σ J ε ⊆ N := by
    intro h hh
    have : h ∈ closure (SASet σ J ε) := subset_closure ⟨1, one_mem _, h, hh, (one_mul h).symm⟩
    rw [← hN] at this
    exact this
  have hplane : ∀ u₀ u₁ : Fin M → E, PlaneND σ J u₀ u₁ → ¬ IsCompact (PlaneSupp σ J ε u₀ u₁) →
      ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (δ : AF F), IsPlacesIdem T₁ T₂ δ →
        PlaneSupp σ J δ u₀ u₁ ⊆ N := by
    intro u₀ u₁ hnd hc T₁ T₂ δ hδ x hx
    have h := GlobalTheory.T.plane_strong_approx_holds F E σ hCM M J hM hJ S₁ S₂ ε hε u₀ u₁ hnd hc T₁ T₂ δ hδ hx
    rw [← hN] at h
    exact h
  have hgen := GlobalTheory.T.plane_strong_approx_generator F E σ hCM M J hM hJ S₁ S₂ ε hε hnc N hcl hS hplane
  have hmem : g ∈ N := GlobalTheory.T.plane_strong_approx_product F E σ M J N hcl hgen g hg
  have : g ∈ (N : Set (HA (AF F) σ J)) := hmem
  rwa [hN] at this

end GlobalTheory.CompanionTheory.Hypotheses₂

end

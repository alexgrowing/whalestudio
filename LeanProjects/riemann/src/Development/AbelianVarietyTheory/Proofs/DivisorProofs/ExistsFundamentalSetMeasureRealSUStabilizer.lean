import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureUnitaryLatticeFamily
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp

theorem exists_measurableSet_reps_covolume : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Γ : Subgroup (GL (Fin r) E)) (ν : Measure (realSU Ψ G)) [ν.IsMulLeftInvariant], (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → (∀ γ ∈ Γ, IsUStab G Λ γ) → ∃ S : Set (realSU Ψ G), MeasurableSet S ∧ ν S = covolume (inReal Ψ G Γ) (realSU Ψ G) ν ∧ ∀ s : realSU Ψ G, ∃ δ ∈ Γ, ∃ hδ : embGL Ψ r δ ∈ realSU Ψ G, (⟨embGL Ψ r δ, hδ⟩ : realSU Ψ G) * s ∈ S := by
  intro E _ _ _ r Ψ G Λ Γ ν _ hΨ hfg hsp hΓ
  haveI := GlobalTheory.SUCount.discrete_inReal hΨ G Γ Λ hfg hsp (fun γ hγ x hx => ((hΓ γ hγ).2 x).1 hx)
  haveI := GlobalTheory.countable_of_discrete_subgroup (inReal Ψ G Γ)
  obtain ⟨D, hD, hu, hF⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (inReal Ψ G Γ)
  refine ⟨D, hD, ((hF ν).covolume_eq_volume).symm, fun s => ?_⟩
  obtain ⟨g, hg, -⟩ := hu s
  obtain ⟨δ, hδ, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
  have hmem : embGL Ψ r δ ∈ realSU Ψ G := e ▸ g.1.2
  refine ⟨δ, hδ, hmem, ?_⟩
  have hg' : ((g : realSU Ψ G)) = ⟨embGL Ψ r δ, hmem⟩ := Subtype.ext e.symm
  rw [← hg']
  exact hg

end GlobalTheory.CovTop.VolUp

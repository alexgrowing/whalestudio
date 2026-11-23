import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChangeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.BCGalAll

theorem main : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm2 D → ∀ (i : D.nd.Loc) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), IsBCV D.nd D.naut i P Pa → ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧ (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ := by
  intro D h0 h2 i P Pa hB
  obtain ⟨ρ, hc, hs, hw, hl⟩ := GlobalTheory.T.exists_galois_rep_base_change D h0 h2 i P Pa hB
  refine ⟨ρ, hc, hs, fun w _ => hw w, fun w hw' => ⟨(hl w hw').1, hw w, fun τ hτ => ?_⟩⟩
  apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
  rw [(hl w hw').2 τ hτ, D.naut.locAut_hodgeTateWeightsLevelZero_def i τ]

end GlobalTheory.BCGalAll

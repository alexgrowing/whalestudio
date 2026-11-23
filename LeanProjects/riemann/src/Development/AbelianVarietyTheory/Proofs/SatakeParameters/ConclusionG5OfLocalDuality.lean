import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import ReciprocityTheory.Hypotheses.GalCoh
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPeriodOfLocalGlobalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.H1H2LocalDualityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalCompatibilityStatement

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

namespace GlobalTheory.LevelPlaces

theorem local_conditions_at_level : LocalFiniteness → LocalTateDuality → LocalEulerChar →
    ∀ D : D7, SumRepresentations.admitted D → RbEx D → SumRepresentations.ConclusionG5 D := by
  intro h1 h2 h3 D hA hRb
  have hLGC : LGC D := GlobalTheory.T.local_global_compatibility D hA.1.1
  have hEig : EigPd D := GlobalTheory.T.eigen_period_of_local_global D hA.1.1 hLGC hRb
  have hH : HOneTwo D := GlobalTheory.T.hOneTwo_of_localFiniteness_tateDuality_eulerChar h1 h2 h3 D
  refine SumRepresentations.galois_clause_of_sufficient D hA.1.1 fun i hg r hr w hw => ⟨hLGC i r hr w hw, fun hS => ⟨hRb i hg, fun rb hrb => ?_⟩⟩
  have hS' := (D.nd.S_def i w).1 hS
  have hnr : ¬ (((rb (D.nd.gam0 i w) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).IsRoot
      (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) := by
    have hk : ∀ k, w ∈ placesOver D.host.E (D.host.g k) → D.nd.l i ≠ D.host.g k :=
      fun k hk h => hS'.2 (h ▸ hk)
    rcases hS'.1 with h0 | h0 | h0
    · exact (hA.2.1 i hg rb hrb).2 0 (hk 0 h0) w h0
    · exact (hA.2.1 i hg rb hrb).2 1 (hk 1 h0) w h0
    · exact hEig i hg w hS h0 rb hrb
  exact ⟨hnr, hH i rb w hS hrb hnr⟩

end GlobalTheory.LevelPlaces

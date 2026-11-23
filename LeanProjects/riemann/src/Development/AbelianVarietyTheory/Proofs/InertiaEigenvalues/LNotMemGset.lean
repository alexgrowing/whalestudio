import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RestPt
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionAtGoodPointsStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.AtQDTypes

theorem g_ne_q_d (D : D7) (k : Fin 2) : D.host.g k ≠ D.host.q ∧ D.host.g k ≠ D.host.d := by
  have hc := D.ntypes.g_cond k
  have hq8 := D.host.hyp.2.2.1
  have hd16 := D.host.hyp.2.2.2.1
  constructor
  · intro h
    have h1 : D.host.g k % D.host.q = 1 := by
      rw [← Nat.mod_mod_of_dvd _ (show D.host.q ∣ D.host.QS * D.host.q * D.host.d from
        ⟨D.host.QS * D.host.d, by ring⟩), hc]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h, Nat.mod_self] at h1
    omega
  · intro h
    have h1 : D.host.g k % D.host.d = 1 := by
      rw [← Nat.mod_mod_of_dvd _ (show D.host.d ∣ D.host.QS * D.host.q * D.host.d from
        ⟨D.host.QS * D.host.q, by ring⟩), hc]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h, Nat.mod_self] at h1
    omega

theorem l_not_mem_gset {D : D7} (i : D.nd.Loc) (h : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) :
    D.nd.l i ∉ TwistedPlaces.gset D := by
  unfold TwistedPlaces.gset
  intro hm
  rw [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm <;> rcases h with h | h
  · exact (g_ne_q_d D 0).1 (hm ▸ h)
  · exact (g_ne_q_d D 0).2 (hm ▸ h)
  · exact (g_ne_q_d D 1).1 (hm ▸ h)
  · exact (g_ne_q_d D 1).2 (hm ▸ h)

end GlobalTheory.AtQDTypes

theorem GlobalTheory.restPt_atQD : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → SumRepresentations.Conclusion41 D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, RestPt i (r i) (ρ i) π :=
  fun hF D r ρ hP h41 hO i hi π hπ =>
    GlobalTheory.T.restriction_at_good_points hF D r ρ hP h41 hO i (GlobalTheory.AtQDTypes.l_not_mem_gset i hi.1.1) π hπ

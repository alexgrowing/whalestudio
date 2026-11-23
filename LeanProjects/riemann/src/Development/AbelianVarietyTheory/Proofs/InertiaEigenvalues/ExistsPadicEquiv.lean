import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContractNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralAndGoodOfIsSpherical
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdent

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.SplitTypeCompl

theorem exists_padic_equiv : ∀ (D : D7) (s : SplitPlace D.host.E), s.v ∈ gPl D →
    ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* s.w.adicCompletion D.host.E), Continuous i := by
  intro D s hs
  obtain ⟨w, hw, k, hk⟩ := hs
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hwk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by simpa [placesOver] using hk
  have hv : ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
    rw [← hw, Ideal.mem_comap, map_natCast]; exact hwk
  have hsw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ s.w.asIdeal := by
    have := hv
    rw [← s.w_under, Ideal.mem_comap, map_natCast] at this
    exact this
  obtain ⟨h1, h2, -⟩ := GlobalTheory.Mem.Chr.splitsC_place (D.host.g_prime k) (D.nd.g_split k) _ hsw
  haveI : CharZero (s.w.adicCompletion D.host.E) :=
    charZero_of_injective_ringHom (algebraMap D.host.E _).injective
  obtain ⟨φ, h, -⟩ := GlobalTheory.QpChar.exists_ringEquiv_padic (s.w.adicCompletion D.host.E) (D.host.g k)
    ((GlobalTheory.LocLanglands.resCard_eq_normV _).trans h1) (GlobalTheory.TypeIdent.irreducible_natCast_compl _ hsw h2)
  exact ⟨D.host.g k, inferInstance, φ, h⟩

end GlobalTheory.SplitTypeCompl

end

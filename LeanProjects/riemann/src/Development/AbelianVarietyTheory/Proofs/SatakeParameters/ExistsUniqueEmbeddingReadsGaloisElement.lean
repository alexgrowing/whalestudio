import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterOfLocalEmbedding
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem existsUnique_reads : ∀ {R : Ranks} (H : Host R) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (c : H.E →+* ↥K.1) (κ : H.E →+* ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), ∃! g : R.GG, Reads H c κ τ g := by
  intro R H l _ K LL c κ τ
  haveI : IsGalois ℚ H.E := H.hostE_isGalois
  obtain ⟨σ, hσ⟩ := GlobalTheory.HTW.exists_aut_comp_eq_of_normal κ ((τ : ↥K.1 →+* ↥LL.1).comp c)
  obtain ⟨g, hg⟩ := (H.gal).symm.surjective σ
  have hg' : H.sigmaOf g = σ := hg
  refine ⟨g, fun x => ?_, fun g' hg2 => ?_⟩
  · rw [hg']
    exact hσ x
  · have e : H.sigmaOf g' = H.sigmaOf g := by
      refine AlgEquiv.ext fun x => ?_
      apply κ.injective
      rw [← hg2 x, hg']
      exact hσ x
    exact (H.gal).symm.injective e

end GlobalTheory.HTW.Rec

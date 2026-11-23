import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostFieldPadicEmbeddingMemMaxUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicAlgClFiniteDenseEqAdjoinStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory

theorem bridge_field_le_unramified : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    {N : NData R H what₂} (nbr : Br.NBr N) (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E))
    (hw : w ∈ placesOver H.E (N.l i)),
    N.l i ∉ H.small → N.l i ≠ H.q → N.l i ≠ H.d → (nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (N.l i) := by
  intro R H what₂ N nbr i w hw h2 hq hd
  have hK := GlobalTheory.T.padicAlgCl_finite_dense_eq_adjoin' (N.l i) H.E ((nbr i w hw).j.comp (algebraMap H.E N.Om)) (nbr i w hw).Kw.1
    (nbr i w hw).j_E (nbr i w hw).Kw.2 (nbr i w hw).j_dense
  rw [hK, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, rfl⟩
  exact GlobalTheory.T.hostField_padicEmbedding_mem_maxUnramified H (N.l i) h2 hq hd _ x

end GlobalTheory

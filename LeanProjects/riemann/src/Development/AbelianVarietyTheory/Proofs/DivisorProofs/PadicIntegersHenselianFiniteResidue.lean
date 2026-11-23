import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import GroundTheory.GlobalFields.LocalAtPlace

open IsDedekindDomain IsLocalRing

namespace GlobalTheory.IntAdicHensel

theorem henselianLocalRing_and_finite_residueField :
    ∀ (v : HeightOneSpectrum ℤ), HenselianLocalRing (v.adicCompletionIntegers ℚ) ∧
      Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := by
  intro v
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers ℚ)
  haveI : IsPrecomplete (maximalIdeal (v.adicCompletionIntegers ℚ)) (v.adicCompletionIntegers ℚ) :=
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.completion_integers_precomplete v hϖ
  haveI : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers ℚ)) (v.adicCompletionIntegers ℚ) := {}
  haveI := IsAdicComplete.henselianRing (v.adicCompletionIntegers ℚ)
    (maximalIdeal (v.adicCompletionIntegers ℚ))
  refine ⟨GlobalTheory.henselianLocalRing_of_henselianRing _, ?_⟩
  haveI : Finite (ℤ ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  exact Finite.of_equiv _ (GroundTheory.Global.residueFieldEquiv (K := ℚ) v).toEquiv

end GlobalTheory.IntAdicHensel

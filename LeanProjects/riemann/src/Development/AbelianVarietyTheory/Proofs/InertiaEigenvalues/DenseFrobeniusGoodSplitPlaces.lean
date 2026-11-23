import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeEigenvalueSystemSetFiniteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationPointEigenSystemMemStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContainsAfterLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralModelRepCoeffRingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationCoefFieldFiniteRangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteCoefficientSetFrobeniusCharpolysStatement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.FrobDense

theorem placesS_finite (D : D7) (l : ℕ) : (placesS D l).Finite := by
  have h0 := Formalism.L2.TwC.placesOver_finite' D.host.E (D.host.g 0) (D.host.g_prime 0).ne_zero
  have h1 := Formalism.L2.TwC.placesOver_finite' D.host.E (D.host.g 1) (D.host.g_prime 1).ne_zero
  have h2 := Formalism.L2.TwC.placesOver_finite' D.host.E (if l = D.host.pde then D.host.pde' else D.host.pde)
    (by split_ifs <;> first | exact D.host.pde'_prime.ne_zero | exact D.host.pde_prime.ne_zero)
  refine ((h0.union h1).union h2).subset ?_
  rintro v ⟨hv | hv | hv, -⟩
  · exact Or.inl (Or.inl hv)
  · exact Or.inl (Or.inr hv)
  · exact Or.inr hv

theorem frob_dense_goodSplit : ∀ (D : D7) (l : ℕ) (Q : Finset (PlE D.host)), l.Prime → GlobalTheory.RowTie.ChebSplit D.nd →
    Dense {σ : G D.host.E D.nd.Om | ∃ v : PlE D.host,
      (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q) ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ} := by
  intro D l Q hl hC
  have hfin : (placesOver D.host.E l ∪ placesS D l ∪ (Q : Set (PlE D.host))).Finite :=
    ((Formalism.L2.TwC.placesOver_finite' D.host.E l hl.ne_zero).union (placesS_finite D l)).union Q.finite_toSet
  refine (hC hfin.toFinset).mono ?_
  rintro σ ⟨w, hwS, hsp, B, hB, hF⟩
  have hw : w ∉ placesOver D.host.E l ∪ placesS D l ∪ (Q : Set (PlE D.host)) := by
    simpa using hwS
  simp only [Set.mem_union, Finset.mem_coe, not_or] at hw
  exact ⟨w, ⟨hsp, hw.1.1, hw.1.2, hw.2⟩, B, hB, hF⟩

end GlobalTheory.FrobDense

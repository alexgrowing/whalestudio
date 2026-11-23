import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFamilyIffRationalHecke

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false

namespace GlobalTheory.HeckeIndexPrime

theorem isHeckePrime_of_hkIdx : ∀ (D : D7) (T0 : CoreJ D), LawsJ T0 → ∀ (i : D.ntw.Tw) (k : ℕ) (P : PlE D.host),
    Formalism.MainNotions.IntegralHeckeForms.HkIdx (X := D.ntw) i k P →
    GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime T0.Q.H T0.Q.l P.asIdeal (charAt P) ∧ charAt P ≠ D.ntw.l i := by
  intro D T0 hL i k P hk
  obtain ⟨_, _, hsp, hS⟩ := hk
  refine ⟨⟨P.isMaximal, GlobalTheory.HeckeSup.split_of_ne ((GlobalTheory.HeckeTieCompare.isSplitPl_iff P).1 hsp), charAt_prime P,
    charAt_mem P, GlobalTheory.HeckeSup.not_dvd_level hL (charAt_mem P) (GlobalTheory.HeckeTieCompare.level_notMem ⟨i, hS⟩)⟩, ?_⟩
  intro he
  apply hS
  have hm : P ∈ Formalism.BasicNotions.placesOver D.host.E (D.ntw.l i) := by
    show ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
    rw [← he]
    exact charAt_mem P
  exact D.ntw.twistExcludedPlaces_contains_residueChar i hm

end GlobalTheory.HeckeIndexPrime

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.Mem.HeckeLevel

open GlobalTheory.Mem.Chr

theorem exists_level_nat : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L), ∃ M : ℕ, 0 < M ∧ ∀ a : Neutral.B1.Ideles L, a ∈ GlobalTheory.Mem.Chr.unitIdl L → (∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 L), Valued.v ((a : AdeleRing (𝓞 L) L).2 P - 1) ≤ Valued.v ((M : L) : P.adicCompletion L)) → χ.1 a = 1 := by
  intro L _ _ χ
  classical
  obtain ⟨hfin, hlev⟩ := GlobalTheory.Mem.UnrAe.unr_ae_and_level L χ
  choose n hn using hlev
  refine ⟨∏ P ∈ hfin.toFinset, (Ideal.absNorm P.asIdeal) ^ (n P), ?_, ?_⟩
  · refine Finset.prod_pos fun P _ => pow_pos (Nat.pos_of_ne_zero fun h => P.ne_bot ?_) _
    exact Ideal.absNorm_eq_zero_iff.1 h
  · intro a ha h1 hv
    refine GlobalTheory.Mem.LocTriv.eq_one_of_local L χ.1 χ.2.1 a ha h1 fun P x hx => ?_
    have hxu : IsUnitAt P x := by
      unfold IsUnitAt
      rw [hx]
      exact ha P
    by_cases hP : P ∈ hfin.toFinset
    · refine hn P x hxu ?_
      rw [hx]
      refine (hv P).trans ?_
      have e : (((∏ Q ∈ hfin.toFinset, (Ideal.absNorm Q.asIdeal) ^ (n Q) : ℕ) : L) : P.adicCompletion L) =
          (((∏ Q ∈ hfin.toFinset, (Ideal.absNorm Q.asIdeal) ^ (n Q) : ℕ) : 𝓞 L) : L) := by
        push_cast
        rfl
      rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_le_pow_iff_dvd]
      have hd : (Ideal.absNorm P.asIdeal) ^ (n P) ∣ ∏ Q ∈ hfin.toFinset, (Ideal.absNorm Q.asIdeal) ^ (n Q) :=
        Finset.dvd_prod_of_mem _ hP
      have hd' := Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast (α := 𝓞 L) hd)
      refine Ideal.dvd_iff_le.2 (le_trans hd' ?_)
      rw [Nat.cast_pow, ← Ideal.span_singleton_pow]
      refine Ideal.pow_right_mono ?_ _
      rw [Ideal.span_singleton_le_iff_mem]
      exact Ideal.absNorm_mem P.asIdeal
    · have hu : χ.UnrAt P := by
        by_contra h
        exact hP (hfin.mem_toFinset.2 h)
      exact hu x hxu

end GlobalTheory.Mem.HeckeLevel

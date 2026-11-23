import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPlNeOfIsSplit

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.ModulusNorm

theorem absNorm_eq_of_two_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {w w' : HeightOneSpectrum (𝓞 E)} (hne : w ≠ w')
    (h : w'.under (𝓞 F) = w.under (𝓞 F)) :
    Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 F)).asIdeal := by
  set p := (w.under (𝓞 F)).asIdeal with hp
  have l1 : w.asIdeal.LiesOver p := ⟨rfl⟩
  have l2 : w'.asIdeal.LiesOver p := ⟨by rw [hp, ← h]; rfl⟩
  have f1 := Ideal.absNorm_pow_inertiaDeg p w.asIdeal
  have f2 := Ideal.absNorm_pow_inertiaDeg p w'.asIdeal
  have c1 := w.asIdeal.inertiaDeg_pos (𝓞 F)
  have c2 := w'.asIdeal.inertiaDeg_pos (𝓞 F)
  have m1 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≤ w.asIdeal := Ideal.map_le_iff_le_comap.2 (le_of_eq l1.over)
  have m2 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≤ w'.asIdeal := Ideal.map_le_iff_le_comap.2 (le_of_eq l2.over)
  have cop : w.asIdeal ⊔ w'.asIdeal = ⊤ :=
    Ideal.IsMaximal.coprime_of_ne w.isMaximal w'.isMaximal fun e => hne (HeightOneSpectrum.ext e)
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≤ w.asIdeal * w'.asIdeal := by
    rw [Ideal.mul_eq_inf_of_coprime cop]; exact le_inf m1 m2
  have hd := map_dvd Ideal.absNorm (Ideal.dvd_iff_le.2 hle)
  rw [map_mul, Ideal.absNorm_algebraMap, ← f1, ← f2, ← pow_add,
    ← Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E, h2] at hd
  have hq : 1 < Ideal.absNorm p := by
    rcases Nat.lt_or_ge 1 (Ideal.absNorm p) with h' | h'
    · exact h'
    · exfalso
      interval_cases hh : Ideal.absNorm p
      · exact (w.under (𝓞 F)).ne_bot (Ideal.absNorm_eq_zero_iff.1 hh)
      · exact (w.under (𝓞 F)).isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 hh)
  have := (Nat.pow_dvd_pow_iff_le_right hq).1 hd
  have e1 : w.asIdeal.inertiaDeg (𝓞 F) = 1 := by omega
  rw [← f1, e1, pow_one]

variable {D : D7}

theorem conjPl_ne_of_isIdemAt {w : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e w) : Formalism.DivisionValues.conjPl w ≠ w := by
  rw [GlobalTheory.FunObj.conjPl_eq_cP]
  exact GlobalTheory.FunObj.conjPrime_ne_of_isIdempotentAt he

theorem absNorm_of_isIdemAt {w : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : Formalism.L2.NTheta.IsIdemAt e w) :
    Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal :=
  absNorm_eq_of_two_over D.sp.cm.deg2 (conjPl_ne_of_isIdemAt he).symm (GlobalTheory.ChainTw.ParInv.under_conjPl w)

variable {T : Type} {L : LevCh D T}

theorem absNorm_condE (P : Places L) : Ideal.absNorm (GlobalTheory.FunObj.SqNum.condE P) = GlobalTheory.FunObj.SqNum.levQ P := by
  unfold GlobalTheory.FunObj.SqNum.condE GlobalTheory.FunObj.SqNum.levQ
  rw [map_prod]
  refine Finset.prod_congr rfl fun v hv => ?_
  obtain ⟨e, he⟩ := P.w_split v hv
  rw [map_pow, absNorm_of_isIdemAt he, P.under_w hv]

end GlobalTheory.ModulusNorm

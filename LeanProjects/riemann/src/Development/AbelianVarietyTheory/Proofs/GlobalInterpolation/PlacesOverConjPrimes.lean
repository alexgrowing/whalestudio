import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemUnitOff
import Formalism.LocalRingCardinality.Lemmas

noncomputable section

namespace GlobalTheory.LvT.Inh

open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix GlobalTheory.LvT GlobalTheory.LvT.Inh
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)
open Formalism.L2.Col (conjPrime₂ PosStar hStd UF Sp)

theorem exists_below {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (j : K →+* L)
    (W : HeightOneSpectrum (𝓞 L)) : ∃ Q : HeightOneSpectrum (𝓞 K),
      ∀ r : 𝓞 K, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom j r ∈ W.asIdeal := by
  letI : Algebra K L := j.toAlgebra
  exact ⟨W.under (𝓞 K), fun r => Iff.rfl⟩

theorem mem_valO_of_below {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (j : K →+* L)
    (W : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K))
    (h : ∀ r : 𝓞 K, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom j r ∈ W.asIdeal) (x : K) :
    j x ∈ valO W ↔ x ∈ valO Q := by
  letI : Algebra K L := j.toAlgebra
  haveI : W.asIdeal.LiesOver Q.asIdeal := ⟨Ideal.ext fun r => h r⟩
  rw [mem_valO, mem_valO, show j x = algebraMap K L x from rfl,
    ← HeightOneSpectrum.valuation_liesOver L Q W x]
  exact pow_le_one_iff (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver W.asIdeal Q.ne_bot)

theorem mem_Ow_iff_valO (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) : x ∈ Ow D w ↔ x ∈ valO (D.plEq w) :=
  D.val_nonneg_iff w x

theorem resChar_mem_plEq (D : D7) (w : D.what₂.places.Pl) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  rw [← (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL), D.val_resChar', ← WithZero.exp_zero,
    WithZero.exp_lt_exp]
  have := D.what₂.places.ramIdx_pos w
  omega

theorem resChar_eq_of_mem_plEq (D : D7) (w : D.what₂.places.Pl) {T : ℕ} (hT : T.Prime)
    (h : (T : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal) : D.what₂.places.resChar w = T := by
  by_contra hne
  have hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) (T : 𝓞 D.what₂.LL) :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.what₂.places.resChar_prime w) hT).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  refine (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (resChar_mem_plEq D w)) (Ideal.mul_mem_left _ _ h)

end GlobalTheory.LvT.Inh

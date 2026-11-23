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

noncomputable section

open GlobalTheory.Mem.Col2.SplitChar

namespace GlobalTheory.UnrKill

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 K) ∈ P.asIdeal := by
  haveI := P.isPrime
  haveI : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  refine ⟨ringChar (𝓞 K ⧸ P.asIdeal), CharP.char_is_prime (𝓞 K ⧸ P.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec]

theorem vl_nat_eq_one {D : D7} {q m : ℕ} (hm : Nat.Coprime m q) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : GlobalTheory.Mem.Chr.OverP D.host q v) : vl D v (m : AE D) = 1 := by
  refine le_antisymm (vl_le (natCast_mem _ _) v) (not_lt.1 fun hlt => ?_)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hm
  have hab' := congrArg (Int.cast : ℤ → AE D) hab
  push_cast at hab'
  have h2 : vl D v ((a : AE D) * m) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left' (vl_le (intCast_mem _ _) v)).trans_lt hlt
  have h3 : vl D v ((b : AE D) * q) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left' (vl_le (intCast_mem _ _) v)).trans_lt (val_nat_lt hv)
  have h4 := Valuation.map_add_lt _ h2 h3
  rw [hab', map_one] at h4
  exact lt_irrefl _ h4

theorem vl_eq_zero_of_zeroAt {D : D7} {q : ℕ} {x : AE D} (h : ZeroAt D q x) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : GlobalTheory.Mem.Chr.OverP D.host q v) : vl D v x = 0 := by
  have hk : ∀ k : ℕ, vl D v x ≤ vl D v (q : AE D) ^ k := fun k => by
    obtain ⟨m, -, hm, s, hs, e⟩ := h k
    have h1 := vl_nat_eq_one hm hv
    rw [← one_mul (vl D v x), ← h1, ← map_mul, e, map_mul, map_pow]
    exact mul_le_of_le_one_right' (vl_le hs v)
  by_contra h0
  obtain ⟨k, hk'⟩ := exists_pow_lt₀ (val_nat_lt hv) (Units.mk0 _ h0)
  exact lt_irrefl _ ((hk k).trans_lt hk')

theorem unr_kill : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E), (∀ P : HeightOneSpectrum (𝓞 D.host.E), (∃ q : ℕ, q.Prime ∧ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) → χ.UnrAt P) → ∀ u : (AE D)ˣ, IntU D u → (∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q ((u : AE D) - 1)) → χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D u) = 1 := by
  intro D χ hχ u hu hz
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E χ.1 χ.2.1 (finIdl D u) (finIdl_unit hu)
    (fun w => by rw [finIdl_fst]; rfl) ?_
  intro P x hx
  obtain ⟨q, hq, hqP⟩ := exists_prime_mem P
  by_cases hI : InertQ D q
  · have hunr := hχ P ⟨q, hq, hI, hqP⟩
    refine hunr x ?_
    show Valued.v (x : P.adicCompletion D.host.E) = 1
    rw [hx]
    exact finIdl_unit hu P
  · have h0 := vl_eq_zero_of_zeroAt (hz q hq hI) (v := P) hqP
    rw [← vl_sub_one, map_eq_zero, sub_eq_zero, ← hx] at h0
    have hx1 : x = 1 := Units.ext h0
    rw [hx1, map_one]
    exact map_one _

end GlobalTheory.UnrKill

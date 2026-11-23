import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
import Formalism.LocalToGlobal.GroupLattices.JointServices.VwResChar
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase

open NumberField IsDedekindDomain Formalism.BasicNotions

namespace GlobalTheory.BigOn.Exp.SerBase

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem natPrime_notMem {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : q.Prime)
    (hne : q ≠ Formalism.EigenvalueLevelCeiling.plc v) : (q : 𝓞 K) ∉ v.asIdeal := by
  intro hmem
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at hmem
  have hdvd : Formalism.EigenvalueLevelCeiling.plc v ∣ q := (ringChar.spec (𝓞 K ⧸ v.asIdeal) q).1 hmem
  exact hne ((Nat.prime_dvd_prime_iff_eq (Formalism.L2.DIV.plc_prime' v) hq).1 hdvd).symm

theorem ownAt_prime_ne (D : D7) (w : D.what₂.places.Pl) :
    (ownAt D (D.plEq w)).Prime ∧ ownAt D (D.plEq w) ≠ Formalism.EigenvalueLevelCeiling.plc (D.plEq w) := by
  unfold ownAt
  split_ifs with h
  · exact ⟨D.host.pde'_prime, fun e => D.host.pde_ne (h.symm.trans e.symm)⟩
  · exact ⟨D.host.pde_prime, fun e => h e.symm⟩

theorem ownUnit : OwnUnit := by
  intro D c w
  obtain ⟨hq, hne⟩ := ownAt_prime_ne D w
  set q := ownAt D (D.plEq w) with hqdef
  have hnot := natPrime_notMem (D.plEq w) hq hne
  have hv : (D.plEq w).valuation D.what₂.LL (q : D.what₂.LL) = 1 := by
    have := ((D.plEq w).valuation_eq_one_iff_notMem (K := D.what₂.LL)).2 hnot
    simpa using this
  have hq0 : (q : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have hnn : (0 : WithTop ℤ) ≤ D.what₂.places.val w (q : D.what₂.LL)⁻¹ :=
    (D.val_nonneg_iff w _).2 (by rw [map_inv₀, hv, inv_one])
  obtain ⟨y, hy⟩ := (c.embW_w w _).1 hnn
  rw [map_inv₀, map_natCast] at hy
  have hqF : ((q : ℕ) : FractionRing (c.Oe w)) ≠ 0 := by
    have := (map_ne_zero (c.embW w)).2 hq0
    rwa [map_natCast] at this
  have h1 : algebraMap (c.Oe w) (FractionRing (c.Oe w)) (y * (q : c.Oe w)) = 1 := by
    rw [map_mul, hy, map_natCast]
    exact inv_mul_cancel₀ hqF
  have h2 : y * (q : c.Oe w) = 1 := by
    apply IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w))
    rw [h1, map_one]
  exact (Units.mkOfMulEqOne (q : c.Oe w) y (by rw [mul_comm]; exact h2)).isUnit

end GlobalTheory.BigOn.Exp.SerBase

import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime

theorem exists_intAt_pow_mul {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    ∃ m : ℕ, IntAt P ((qOf P : E) ^ m * a) := by
  have e : (qOf P : E) = algebraMap (𝓞 E) E (qOf P : 𝓞 E) := by rw [map_natCast]
  have h1 : P.valuation E (qOf P : E) < 1 := by
    rw [e, HeightOneSpectrum.valuation_of_algebraMap]
    exact (P.intValuation_lt_one_iff_mem _).2 (Ideal.absNorm_mem _)
  have key : ∃ m : ℕ, P.valuation E ((qOf P : E) ^ m * a) ≤ 1 := by
    rcases eq_or_ne (P.valuation E a) 0 with ha | ha
    · exact ⟨0, by simp [ha]⟩
    have hq : P.valuation E (qOf P : E) ≠ 0 := by
      simpa using GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
    refine ⟨(WithZero.log (P.valuation E a)).toNat, ?_⟩
    rw [map_mul, map_pow]
    rw [← WithZero.exp_log hq, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [← WithZero.exp_log hq, ← WithZero.exp_log ha, ← WithZero.exp_nsmul, ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.log_exp]
    set u := WithZero.log (P.valuation E (qOf P : E))
    set w := WithZero.log (P.valuation E a)
    have h2 : w ≤ (w.toNat : ℤ) := Int.self_le_toNat w
    have h3 : (0 : ℤ) ≤ (w.toNat : ℤ) := Int.natCast_nonneg _
    rw [nsmul_eq_mul]
    nlinarith
  obtain ⟨m, h⟩ := key
  obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer _ h
  exact ⟨m, n, d, d.2, by rw [mul_comm]; exact hnd⟩

theorem exists_intAt_family {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι]
    (f : ι → E) : ∃ m : ℕ, ∀ m', m ≤ m' → ∀ i, IntAt P ((qOf P : E) ^ m' * f i) := by
  choose g hg using fun i => exists_intAt_pow_mul P (f i)
  exact ⟨Finset.univ.sup g, fun m' hm i =>
    GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mono ((Finset.le_sup (Finset.mem_univ i)).trans hm) (hg i)⟩

theorem bounded_denominators : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ), (∀ v : Fin a → E, ∃ m : ℕ, ∀ m', m ≤ m' → IntV P (((qOf P : E) ^ m') • v)) ∧ ∀ y : (Fin a → E) →ₗ[E] (Fin b → E), ∃ m : ℕ, ∀ m', m ≤ m' → IntHom P (((qOf P : E) ^ m') • y) := by
  intro E _ _ P a b
  refine ⟨fun v => ?_, fun y => ?_⟩
  · obtain ⟨m, hm⟩ := exists_intAt_family P v
    exact ⟨m, fun m' h l => hm m' h l⟩
  · obtain ⟨m, hm⟩ := exists_intAt_family P (fun p : Fin a × Fin b => y (Pi.single p.1 1) p.2)
    exact ⟨m, fun m' h => (intHom_iff _).2 fun s l => hm m' h (s, l)⟩

end GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.ExpTie

theorem exists_mul_eq_prW_pow {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (J : ℕ) {a : 𝓞 K}
    (ha : a ∈ w.asIdeal ^ (J * Formalism.L2.Col.eW w)) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ b : 𝓞 K, t * a = ((Formalism.L2.Col.prW w : ℕ) : 𝓞 K) ^ J * b := by
  have hm := (Formalism.L2.Col.algebraMap_mem_maximalIdeal_pow_iff w a (J * Formalism.L2.Col.eW w)).2 ha
  rw [mul_comm, pow_mul, ← Formalism.L2.Col.span_prW_ow, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm
  obtain ⟨y, hy⟩ := hm
  obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective w.asIdeal.primeCompl y
  refine ⟨t, t.2, b, ?_⟩
  apply IsLocalization.injective (Formalism.L2.Col.Ow w) w.asIdeal.primeCompl_le_nonZeroDivisors
  rw [map_mul, map_mul, hy, map_pow, map_natCast, mul_comm, mul_assoc, IsLocalization.mk'_spec]

theorem LIncl.jexpU_bounds {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    {B : Formalism.L2.DIV.BlockDat K G Pl0} {ℓ : Formalism.L2.DIV.Lvl K G} {Z : Submodule K B.S.Forms} {w : HeightOneSpectrum (𝓞 K)} {J : ℕ}
    (h : LIncl B ℓ Z w J) : 0 ≤ B.JexpU ℓ Z w ∧ B.JexpU ℓ Z w ≤ J := by
  have he : 0 < Formalism.L2.Col.eW w := Formalism.L2.Col.eW_pos w
  have hp : Formalism.EigenvalueLevelCeiling.plc w = Formalism.L2.Col.prW w :=
    Formalism.L2.Col.eq_prW_of_mem w (Formalism.EigenvalueLevelCeiling.plc_prime w) (Formalism.EigenvalueLevelCeiling.plc_mem w)
  have key : B.JexpW ℓ Z w ≤ J * Formalism.L2.Col.eW w := by
    unfold Formalism.L2.DIV.BlockDat.JexpW Formalism.L2.DIV.expW
    apply Nat.sInf_le
    intro a ha z hz
    obtain ⟨t, ht, b, htb⟩ := exists_mul_eq_prW_pow w J ha
    obtain ⟨s, hs, hsz⟩ := h z hz
    refine ⟨s * t, w.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
    have e : (s * t) • (a • z) = b • (s • ((((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^ J) • z)) := by
      rw [hp, smul_smul, smul_smul, smul_smul, mul_assoc, htb]
      congr 1
      ring
    rw [e]
    exact Submodule.smul_mem _ b hsz
  refine ⟨?_, ?_⟩
  · unfold Formalism.L2.DIV.BlockDat.JexpU
    positivity
  · unfold Formalism.L2.DIV.BlockDat.JexpU
    rw [div_le_iff₀ (by exact_mod_cast he)]
    exact_mod_cast key

theorem jexpU_le_of_lIncl : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type)
    (B : Formalism.L2.DIV.BlockDat K G Pl0) (ℓ : Formalism.L2.DIV.Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (J : ℕ),
    LIncl B ℓ Z w J → 0 ≤ B.JexpU ℓ Z w ∧ B.JexpU ℓ Z w ≤ J :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => LIncl.jexpU_bounds h

end GlobalTheory.ExpTie

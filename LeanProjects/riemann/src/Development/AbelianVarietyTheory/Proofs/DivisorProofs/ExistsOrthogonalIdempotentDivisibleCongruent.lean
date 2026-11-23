import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruentOneDetSubOneMemIdealMulConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongLevRelIndexLe
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall.IdemChoice

open GlobalTheory.FunObj.StdDatum

theorem exists_idem_of_limit : (∀ (D : D7) (x : 𝓞 D.host.E), ∃ e ∈ OhE D, e * e = e ∧ ∀ N : ℕ, 0 < N → ∃ n : ℕ, 0 < n ∧ ∃ w ∈ OhE D, e = inc D (x : D.host.E) ^ n + (N : AE D) * w) → ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (δ u : 𝓞 D.host.E), inc D ((δ * u : 𝓞 D.host.E) : D.host.E) - 1 ∈ hatId D (D.host.conj • 𝔪) → ∃ f ∈ OhE D, ∃ w ∈ OhE D, f * f = f ∧ f * sgA D f = 0 ∧ f = inc D (δ : D.host.E) * w ∧ 1 - f ∈ hatId D (D.host.conj • 𝔪) := by
  intro hB1 D 𝔪 hsup δ u hδu
  set 𝔫 : Ideal (𝓞 D.host.E) := D.host.conj • 𝔪 with h𝔫
  have gen : ∀ {b : 𝓞 D.host.E}, b ∈ 𝔫 → ∀ {y : AE D}, y ∈ OhE D → inc D (b : D.host.E) * y ∈ hatId D 𝔫 :=
    fun {b} hb {y} hy => AddSubgroup.subset_closure ⟨b, hb, y, hy, rfl⟩
  have gen1 : ∀ {b : 𝓞 D.host.E}, b ∈ 𝔫 → inc D (b : D.host.E) ∈ hatId D 𝔫 := fun hb => by
    simpa using gen hb (one_mem (OhE D))
  by_cases hδ : δ = 0
  · subst hδ
    refine ⟨0, zero_mem _, 0, zero_mem _, by simp, by simp, by simp, ?_⟩
    have : inc D ((0 * u : 𝓞 D.host.E) : D.host.E) - 1 = -1 := by simp
    rw [this] at hδu
    simpa using neg_mem hδu
  have h1m : (1 : 𝓞 D.host.E) ∈ 𝔪 ⊔ 𝔫 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 h1m
  have h𝔫0 : 𝔫 ≠ ⊥ := by
    intro e
    have h𝔪 : 𝔪 = ⊥ := by
      by_contra h
      exact GlobalTheory.BotPairSmall.conj_smul_ne_bot D h e
    rw [e, h𝔪, sup_bot_eq] at hsup
    exact bot_ne_top hsup
  set x : 𝓞 D.host.E := s * δ * u with hx
  set X : AE D := inc D (x : D.host.E) with hX
  have hXO : X ∈ OhE D := GlobalTheory.CongIdx.inc_int_mem x

  have h1X : 1 - X ∈ hatId D 𝔫 := by
    have e : 1 - X = inc D (t : D.host.E) + inc D (s : D.host.E) * (-(inc D ((δ * u : 𝓞 D.host.E) : D.host.E) - 1)) := by
      have e1 : inc D (s : D.host.E) + inc D (t : D.host.E) = 1 := by
        rw [← map_add, show (s : D.host.E) + t = ((s + t : 𝓞 D.host.E) : D.host.E) from rfl, hst]; simp
      rw [hX, hx]
      push_cast
      simp only [map_mul]
      linear_combination -e1
    rw [e]
    exact add_mem (gen1 ht) (GlobalTheory.CongIdx.mul_mem_hatId (GlobalTheory.CongIdx.inc_int_mem s) (neg_mem hδu))

  have hxm : x ∈ 𝔪 := by rw [hx, mul_assoc]; exact Ideal.mul_mem_right _ _ hs
  have hsX : sgA D X ∈ hatId D 𝔫 := by
    rw [hX, GlobalTheory.NormSum.PtsMem.sgA_inc]
    exact gen1 (Ideal.smul_mem_pointwise_smul _ _ _ hxm)
  have hsXO : sgA D X ∈ OhE D := VacMove.sgA_mem D hXO

  have hN₁ : 0 < Ideal.absNorm (Ideal.span {δ}) := by
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hδ
  have hN₂ : 0 < Ideal.absNorm 𝔫 := by
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔫0
  set N := Ideal.absNorm (Ideal.span {δ}) * Ideal.absNorm 𝔫 with hN
  have hNδ : (N : 𝓞 D.host.E) ∈ Ideal.span {δ} := by
    rw [hN, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hN𝔫 : (N : 𝓞 D.host.E) ∈ 𝔫 := by
    rw [hN, Nat.cast_mul]; exact Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hNδ
  have hNinc : (N : AE D) = inc D ((N : 𝓞 D.host.E) : D.host.E) := by simp
  obtain ⟨e, heO, hee, hlim⟩ := hB1 D x
  obtain ⟨n, hn, w, hwO, hew⟩ := hlim N (Nat.mul_pos hN₁ hN₂)
  set ē := sgA D e with hē
  have hēO : ē ∈ OhE D := VacMove.sgA_mem D heO
  have hēē : ē * ē = ē := by rw [hē, ← map_mul, hee]
  refine ⟨e * (1 - ē), mul_mem heO (sub_mem (one_mem _) hēO), ?_⟩

  have hXd : X = inc D (δ : D.host.E) * inc D ((s * u : 𝓞 D.host.E) : D.host.E) := by
    rw [hX, hx, ← map_mul]; congr 1; push_cast; ring
  have hNd : (N : AE D) = inc D (δ : D.host.E) * inc D (c : D.host.E) := by
    rw [hNinc, ← hc, ← map_mul]; congr 1; push_cast; ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hed : e = inc D (δ : D.host.E) *
      (inc D ((s * u : 𝓞 D.host.E) : D.host.E) * X ^ m + inc D (c : D.host.E) * w) := by
    rw [hew, pow_succ, hNd, ← hX]
    linear_combination X ^ m * hXd
  refine ⟨(inc D ((s * u : 𝓞 D.host.E) : D.host.E) * X ^ m + inc D (c : D.host.E) * w) * (1 - ē),
    mul_mem (add_mem (mul_mem (GlobalTheory.CongIdx.inc_int_mem _) (pow_mem hXO m))
      (mul_mem (GlobalTheory.CongIdx.inc_int_mem _) hwO)) (sub_mem (one_mem _) hēO), ?_, ?_, ?_, ?_⟩
  · linear_combination (1 - ē) ^ 2 * hee + e * hēē
  · have hs2 : sgA D (e * (1 - ē)) = ē * (1 - e) := by
      rw [map_mul, map_sub, map_one, hē, GlobalTheory.NormSum.VacMove.sgA_sgA]
    rw [hs2]
    linear_combination (-(1 - ē) * ē) * hee
  · conv_lhs => rw [hed]
    ring
  ·
    have e1 : 1 - e * (1 - ē) = (1 - X ^ (m + 1)) - (N : AE D) * w + e * ē := by rw [hew, ← hX]; ring
    rw [e1]
    refine add_mem (sub_mem ?_ ?_) ?_
    · rw [← mul_neg_geom_sum]
      rw [mul_comm]
      exact GlobalTheory.CongIdx.mul_mem_hatId (sum_mem fun i _ => pow_mem hXO i) h1X
    · rw [hNinc]; exact gen hN𝔫 hwO
    · refine GlobalTheory.CongIdx.mul_mem_hatId heO ?_
      rw [hē, hew, ← hX, map_add, map_pow, map_mul, pow_succ, map_natCast]
      refine add_mem ?_ ?_
      · exact GlobalTheory.CongIdx.mul_mem_hatId (pow_mem hsXO m) hsX
      · rw [hNinc]; exact gen hN𝔫 (VacMove.sgA_mem D hwO)

end GlobalTheory.BotPairSmall.IdemChoice

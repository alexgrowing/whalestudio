import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.AdelicApprox

variable (D : D7)

theorem levelC_natCast (n : ℕ) : Formalism.UG.P.levelafC D.host.E (n : 𝓞 ℚ) = (n : AE D) := by
  rw [← Formalism.UG.P.adelstab_incl_C, map_natCast, map_natCast]

theorem exists_denom (x : AE D) : ∃ n : ℕ, 0 < n ∧ (n : AE D) * x ∈ OhE D := by
  obtain ⟨d, hd, hx⟩ := Formalism.UG.P.levelaf_denom x
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨Ideal.absNorm (Ideal.span {d}), Nat.pos_of_ne_zero ?_, ?_⟩
  · simpa [Ideal.absNorm_eq_zero_iff] using hd
  · rw [← levelC_natCast, ← hc, Formalism.UG.P.levelafC_mul, mul_assoc]
    exact mul_mem (Formalism.UG.P.levelafC_mem c) hx

theorem exists_approx (n : ℕ) (hn : 0 < n) (s : AE D) (hs : s ∈ OhE D) :
    ∃ r : D.host.E, ∃ w ∈ OhE D, s = inc D r + (n : AE D) * w := by
  rw [← levelC_natCast]
  obtain ⟨b, t, ht, h⟩ := Formalism.UG.P.csGlob_approx Formalism.UG.P.csGlob_intAdApprox (n : 𝓞 ℚ)
    (Nat.cast_ne_zero.2 hn.ne') s hs
  exact ⟨_, t, ht, h⟩

theorem one_mem_inverse_halfDifferent : (1 : D.host.E) ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
  have hne : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) ≠ ⊥ := differentIdeal_ne_bot
  have hspec : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) =
      D.host.𝔟 * (D.host.conj • D.host.𝔟) := D.host.𝔟_spec.1
  rw [hspec] at hne
  have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; rintro h; exact hne (by rw [h]; simp)
  rw [FractionalIdeal.mem_coe]
  unfold Host.AA0
  rw [FractionalIdeal.mem_inv_iff hB]
  intro y hy
  rw [one_mul]
  exact FractionalIdeal.coeIdeal_le_one hy

theorem mul_mem_IhE (cc : Ideal (𝓞 D.host.K)) (s : AE D) (hs : s ∈ OhE D) (t : AE D)
    (ht : t ∈ IhE D cc) : s * t ∈ IhE D cc := by
  unfold IhE at ht
  induction ht using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, a, ha, u, hu, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, s * u, mul_mem hs hu, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem absNorm_mul_mem_IhE (cc : Ideal (𝓞 D.host.K)) (s : AE D) (hs : s ∈ OhE D) :
    (Ideal.absNorm cc : AE D) * s ∈ IhE D cc := by
  refine AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, 1, one_mem_inverse_halfDifferent D, s, hs, ?_⟩
  simp

theorem approx_mod_ideal : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), cc ≠ ⊥ →
    (∀ (y : AE D) (m : ℕ), 0 < m → ∃ e : D.host.E, ∃ t ∈ IhE D cc,
      inc D e - y = (m : AE D) * t) ∧
    (∀ y : AE D, ∃ n : ℕ, 0 < n ∧ (n : AE D) * y ∈ OhE D) ∧
    (∀ s ∈ OhE D, ∀ t ∈ IhE D cc, s * t ∈ IhE D cc) := by
  intro D cc hcc
  refine ⟨fun y m hm => ?_, exists_denom D, mul_mem_IhE D cc⟩
  obtain ⟨k, hk, hy⟩ := exists_denom D y
  have hn : 0 < Ideal.absNorm cc :=
    Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨r, w, hw, h⟩ := exists_approx D (k * m * Ideal.absNorm cc)
    (Nat.mul_pos (Nat.mul_pos hk hm) hn) _ hy
  refine ⟨(k : D.host.E)⁻¹ * r, _, absNorm_mul_mem_IhE D cc (-w) (neg_mem hw), ?_⟩
  have hu : inc D (k : D.host.E)⁻¹ * (k : AE D) = 1 := by
    rw [← map_natCast (inc D), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hk.ne'), map_one]
  rw [map_mul]
  push_cast at h
  linear_combination (-inc D (k : D.host.E)⁻¹) * h +
    (y - (m : AE D) * (Ideal.absNorm cc : AE D) * w) * hu

end GlobalTheory.AdelicApprox

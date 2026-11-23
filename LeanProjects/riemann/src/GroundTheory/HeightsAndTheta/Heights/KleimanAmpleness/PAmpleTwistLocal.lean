import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsAmple
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsAmpleAffine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace AmpleTwistLocal

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem mem_chartRing_of_mem_zero {I : Chart x} {q : Ω} (hq : q ∈ twistMod S x 0 I) :
    q ∈ chartRing S x I := by
  refine Submodule.span_induction (p := fun q _ => q ∈ chartRing S x I) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨f, s, e, e', hs, hf, hse, he, rfl⟩
    have hee : e' = e := by omega
    subst hee
    exact ⟨f, s, e', hs, hf, hse, rfl⟩
  · exact Subalgebra.zero_mem _
  · intro a b _ _ ha hb; exact Subalgebra.add_mem _ ha hb
  · intro a q _ hq
    rw [chartRing_smul_def]
    exact Subalgebra.mul_mem _ a.2 hq

theorem mul_mem_pow (H : SubSystem S x Ω) (I : Chart x) {c : ℕ} {z : Ω}
    (hz : z ∈ (H.pow c).sub I) (d : ℕ) {w : Ω} (hw : w ∈ (H.pow d).sub I) :
    z * w ∈ (H.pow (c + d)).sub I := by
  induction d generalizing w with
  | zero =>
    change w ∈ twistMod S x 0 I at hw
    have h := Submodule.smul_mem ((H.pow c).sub I)
      (⟨w, mem_chartRing_of_mem_zero hw⟩ : chartRing S x I) hz
    rw [chartRing_smul_def] at h
    rwa [Nat.add_zero, mul_comm]
  | succ d ih =>
    change w ∈ Submodule.span _ _ at hw
    refine Submodule.span_induction
      (p := fun w _ => z * w ∈ ((H.pow (c + d)).twist H).sub I) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨q, hq, y, hy, rfl⟩
      refine Submodule.subset_span ⟨q, hq, z * y, ih hy, ?_⟩
      simp only [smul_eq_mul]; ring
    · rw [mul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
    · intro a w _ hw
      rw [chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]
      exact Submodule.smul_mem _ a hw

theorem pow_mem_pow (H : SubSystem S x Ω) (I : Chart x) {m : ℕ} {h : Ω}
    (hh : h ∈ (H.pow m).sub I) (n : ℕ) : h ^ n ∈ (H.pow (m * n)).sub I := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact one_mem_twistMod_zero I
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact mul_mem_pow H I ih m hh

theorem mul_mem_twist_pow (Q H : SubSystem S x Ω) (I : Chart x) {c d : ℕ} {z w : Ω}
    (hz : z ∈ (Q.twist (H.pow c)).sub I) (hw : w ∈ (H.pow d).sub I) :
    z * w ∈ (Q.twist (H.pow (c + d))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction
    (p := fun z _ => z * w ∈ (Q.twist (H.pow (c + d))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.subset_span ⟨q * w, mul_mem_pow H I hq d hw, y, hy, ?_⟩
    simp only [smul_eq_mul]; ring
  · rw [zero_mul]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [add_mul]; exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    rw [chartRing_smul_def, mul_assoc, ← chartRing_smul_def]
    exact Submodule.smul_mem _ a hz

theorem proof (hA : AmpleAffineGen.Statement.{u, w}) : AmpleTwistLocal.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x H A Q b j
  classical
  by_cases h0 : A.h j = 0
  · refine ⟨0, fun n _ I y _ => ⟨1, ?_⟩⟩
    rw [h0, pow_one, mul_zero]
    exact Submodule.zero_mem _
  obtain ⟨p, s, hs, hgen⟩ := hA S Ω N x H A Q b j h0
  have hhI : ∀ I : Chart x, A.h j ∈ (H.pow A.m).sub I := fun I =>
    (Submodule.mem_iInf _).mp (A.mem_secs j) I
  choose k hk using hs
  refine ⟨Finset.univ.sup fun q : Fin p × Chart x => k q.1 q.2, fun n hn I y hy => ?_⟩
  have hglob : ∀ t, s t * A.h j ^ n ∈ (Q.twist (H.pow (b + A.m * n))).secs := by
    intro t
    refine (Submodule.mem_iInf _).mpr fun I' => ?_
    have hle : k t I' ≤ n := le_trans
      (Finset.le_sup (f := fun q : Fin p × Chart x => k q.1 q.2) (Finset.mem_univ (t, I'))) hn
    have h1 := mul_mem_twist_pow Q.toSubSystem H.toSubSystem I' (hk t I')
      (pow_mem_pow H.toSubSystem I' (hhI I') (n - k t I'))
    have e1 : s t * A.h j ^ k t I' * A.h j ^ (n - k t I') = s t * A.h j ^ n := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
    have e2 : b + A.m * k t I' + A.m * (n - k t I') = b + A.m * n := by
      rw [add_assoc, ← mul_add, Nat.add_sub_cancel' hle]
    rw [e1, e2] at h1
    exact h1
  have hpn : A.h j ^ n ≠ 0 := pow_ne_zero n h0
  obtain ⟨e, g, hg, hz⟩ := hgen I (y / A.h j ^ n) n (by rwa [div_mul_cancel₀ y hpn])
  refine ⟨e, ?_⟩
  have hy' : y = A.h j ^ n * ∑ t, g t * s t := by
    rw [← hz]; field_simp
  rw [hy', Finset.mul_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun t _ => ?_
  have e3 : A.h j ^ n * (g t * s t) * A.h j ^ e = (s t * A.h j ^ n) * (g t * A.h j ^ e) := by ring
  rw [e3]
  exact Submodule.mul_mem_mul (Submodule.subset_span (hglob t)) (hg t)

end AmpleTwistLocal

end

end GroundTheory.Heights₂.Heights.Kleiman

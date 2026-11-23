import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.LocIndex

theorem index_coprime_of_multiples {G : Type*} [AddCommGroup G] [AddGroup.FG G] (H : AddSubgroup G) (p : ℕ)
    (hp : p.Prime) (h : ∀ z : G, ∃ s : ℕ, Nat.Coprime s p ∧ s • z ∈ H) : Nat.Coprime H.index p := by
  have hq : ∀ x : G ⧸ H, ∃ s : ℕ, Nat.Coprime s p ∧ s • x = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨s, hs, hz⟩ := h z
    refine ⟨s, hs, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact hz
  have htor : AddMonoid.IsTorsion (G ⧸ H) := by
    intro x
    obtain ⟨s, hs, hx⟩ := hq x
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨s, Nat.pos_of_ne_zero ?_, hx⟩
    rintro rfl
    exact hp.one_lt.ne' (by simpa using hs)
  haveI : Finite (G ⧸ H) := AddCommGroup.finite_of_fg_torsion _ htor
  haveI := Fact.mk hp
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := G ⧸ H) p hd
  obtain ⟨s, hs, hs0⟩ := hq x
  have : p ∣ s := hx ▸ addOrderOf_dvd_of_nsmul_eq_zero hs0
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hs.symm this

theorem mul_mem_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a : 𝓞 D.host.K) {w : ℂ}
    (hw : w ∈ lamOf D cc δ) : w * D.host.φ₀ ((a : D.host.K) : D.host.E) ∈ lamOf D cc δ := by
  unfold lamOf at hw
  induction hw using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨c * a, cc.mul_mem_right a hc, ?_⟩
    rw [mul_assoc, ← map_mul]
    congr 2
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem exists_multiple_mem (D : D7) (hD : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (p : ℕ) (hb : LocBasis D p (YYl D L L') b)
    (z : VC D N N') (hz : z ∈ La D (tor0 D cc δ) L L') :
    ∃ s : ℕ, Nat.Coprime s p ∧ s • z ∈ LaB D (tor0 D cc δ) b := by
  unfold La at hz
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    obtain ⟨s, hs, c, hc⟩ := hb.2.2 A hA
    refine ⟨s, hs, ?_⟩
    have key : s • w • embV D (tor0 D cc δ) A =
        ∑ i, (w * D.host.φ₀ ((c i : D.host.K) : D.host.E)) • embV D (tor0 D cc δ) (b i) := by
      funext τ i j
      have h1 := congrArg (fun M => embT D τ (M i j)) hc
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, Matrix.sum_apply, map_sum] at h1
      simp only [hD.1 τ] at h1
      simp only [Pi.smul_apply, Finset.sum_apply, embV, tor0, smul_eq_mul, nsmul_eq_mul]
      rw [mul_left_comm, h1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [key]
    exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨_, mul_mem_lamOf D cc δ (c i) hw, i, rfl⟩
  | zero => exact ⟨1, Nat.coprime_one_left p, by rw [smul_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨t, ht, hy⟩ := hy
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx t
    · rw [mul_smul]; exact nsmul_mem hy s
  | neg x _ hx =>
    obtain ⟨s, hs, hx⟩ := hx
    exact ⟨s, hs, by rw [smul_neg]; exact neg_mem hx⟩

theorem index_coprime : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (p : ℕ), p.Prime → (La D (tor0 D cc δ) L L').FG → LocBasis D p (YYl D L L') b → Nat.Coprime (((LaB D (tor0 D cc δ) b).addSubgroupOf (La D (tor0 D cc δ) L L')).index) p := by
  intro D hD cc δ N N' r L L' b p hp hfg hb
  haveI : AddGroup.FG (La D (tor0 D cc δ) L L') := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
  refine index_coprime_of_multiples _ p hp fun z => ?_
  obtain ⟨s, hs, hz⟩ := exists_multiple_mem D hD cc δ L L' b p hb z.1 z.2
  exact ⟨s, hs, AddSubgroup.mem_addSubgroupOf.2 hz⟩

end GlobalTheory.NormSum.LocIndex

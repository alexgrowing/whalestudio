import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

open UpperTheory.Gal.Int.Geo

namespace UpperTheory.ActionSupremumCommute

variable {A O M : Type} [CommRing A] [Ring O] [Algebra A O] [AddCommGroup M] [Module O M]

private lemma nat_act (N : ℕ) (y : M) : algebraMap A O (N : A) • y = N • y := by
  rw [map_natCast, Nat.cast_smul_eq_nsmul]

private lemma act_comm (c d : A) (y : M) :
    algebraMap A O c • algebraMap A O d • y = algebraMap A O d • algebraMap A O c • y := by
  rw [smul_smul, smul_smul, ← map_mul, ← map_mul, mul_comm c d]

private lemma exists_sup {a b : A} {N : ℕ} (hb : b ∈ Ideal.span {a} ⊔ Ideal.span {(N : A)}) :
    ∃ r s : A, b = r * a + s * (N : A) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hb
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hu
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hv
  exact ⟨r, s, rfl⟩

private lemma act_sup {a b : A} {N : ℕ} (hb : b ∈ Ideal.span {a} ⊔ Ideal.span {(N : A)}) (w : M) :
    ∃ y z : M, algebraMap A O b • w = algebraMap A O a • y + N • z := by
  obtain ⟨r, s, rfl⟩ := exists_sup hb
  refine ⟨algebraMap A O r • w, algebraMap A O s • w, ?_⟩
  rw [map_add, add_smul, map_mul, map_mul, mul_smul, mul_smul, act_comm r a, act_comm s (N : A), nat_act]

private lemma act_sup_of {a b : A} {N : ℕ} (hb : b ∈ Ideal.span {a} ⊔ Ideal.span {(N : A)})
    {y z : M} (hy : algebraMap A O a • y = N • z) :
    ∃ z' : M, algebraMap A O b • y = N • z' := by
  obtain ⟨r, s, rfl⟩ := exists_sup hb
  refine ⟨algebraMap A O r • z + algebraMap A O s • y, ?_⟩
  rw [map_add, add_smul, map_mul, map_mul, mul_smul, mul_smul, hy, nat_act, smul_add,
    smul_comm N (algebraMap A O r) z, smul_comm N (algebraMap A O s) y]

private lemma fwd {a : A} {N : ℕ} {𝔞 : Ideal A}
    (h : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)})
    (inj : ∀ u v : M, N • u = N • v → u = v) (W : Submodule O M)
    (hW : ∀ c ∈ 𝔞, ∀ z : M, algebraMap A O c • z ∈ W) {y z : M}
    (hy : algebraMap A O a • y = N • z) : y ∈ W := by
  have key : ∀ t ∈ (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞,
      ∃ u ∈ W, algebraMap A O t • y = N • u := by
    intro t ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro b hb c hc
      obtain ⟨z', hz'⟩ := act_sup_of hb hy
      refine ⟨algebraMap A O c • z', hW c hc z', ?_⟩
      rw [mul_comm b c, map_mul, mul_smul, hz']
      exact smul_comm _ _ _
    · rintro t t' ⟨u, hu, hu'⟩ ⟨v, hv, hv'⟩
      exact ⟨u + v, W.add_mem hu hv, by rw [map_add, add_smul, hu', hv', smul_add]⟩
  obtain ⟨u, hu, hu'⟩ := key (N : A) (by rw [h]; exact Ideal.mem_span_singleton_self _)
  rw [nat_act] at hu'
  rwa [inj y u hu']

private lemma bwd {a : A} {N : ℕ} {𝔞 : Ideal A}
    (h : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)}) {y : M}
    (hy : y ∈ Submodule.span O {z : M | ∃ c ∈ 𝔞 ^ 1, ∃ z' : M, z = algebraMap A O c • z'}) :
    ∃ z : M, algebraMap A O a • y = N • z := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, z', rfl⟩ := hx
    rw [pow_one] at hc
    have hac : a * c ∈ Ideal.span {(N : A)} :=
      h ▸ Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) hc
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hac
    refine ⟨algebraMap A O t • z', ?_⟩
    rw [← mul_smul, ← map_mul, ← ht, map_mul, mul_smul, act_comm t (N : A), nat_act]
  | zero => exact ⟨0, by simp⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hx'
    exact ⟨u + v, by rw [smul_add, hu, hv, smul_add]⟩
  | smul o x _ hx =>
    obtain ⟨u, hu⟩ := hx
    refine ⟨o • u, ?_⟩
    rw [← mul_smul, Algebra.commutes, mul_smul, hu]
    exact smul_comm _ _ _

private lemma part2 {a : A} {N : ℕ} {𝔞 : Ideal A}
    (h : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)})
    (inj : ∀ u v : M, N • u = N • v → u = v) {x : M}
    (hx : ∀ c ∈ 𝔞, ∃ z : M, algebraMap A O c • x = N • z) :
    ∃ y z : M, x = algebraMap A O a • y + N • z := by
  have key : ∀ t ∈ (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞,
      ∃ y z : M, algebraMap A O t • x = N • (algebraMap A O a • y + N • z) := by
    intro t ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro b hb c hc
      obtain ⟨z0, hz0⟩ := hx c hc
      obtain ⟨y, z, hyz⟩ := act_sup (O := O) hb z0
      refine ⟨y, z, ?_⟩
      rw [map_mul, mul_smul, hz0, ← hyz]
      exact smul_comm _ _ _
    · rintro t t' ⟨y, z, h1⟩ ⟨y', z', h2⟩
      refine ⟨y + y', z + z', ?_⟩
      rw [map_add, add_smul, h1, h2]
      simp only [smul_add]
      abel
  obtain ⟨y, z, hyz⟩ := key (N : A) (by rw [h]; exact Ideal.mem_span_singleton_self _)
  rw [nat_act] at hyz
  exact ⟨y, z, inj _ _ hyz⟩

end UpperTheory.ActionSupremumCommute

theorem UpperTheory.lattice_generation :
    LatGen := by
  intro q _ D a N 𝔞 hN hG
  haveI := D.freeLa
  have inj : ∀ u v : D.La, N • u = N • v → u = v := by
    intro u v huv
    have h0 : (N : ℤ) • (u - v) = 0 := by
      rw [smul_sub, natCast_zsmul, natCast_zsmul, huv, sub_self]
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact absurd (Int.natCast_eq_zero.mp h1) hN.ne'
    · exact sub_eq_zero.mp h1
  refine ⟨fun y => ⟨fun ⟨z, hz⟩ => UpperTheory.ActionSupremumCommute.fwd hG inj _ ?_ hz,
    fun hy => UpperTheory.ActionSupremumCommute.bwd hG hy⟩, fun x hx => UpperTheory.ActionSupremumCommute.part2 hG inj hx⟩
  intro c hc z
  exact Submodule.subset_span ⟨c, by rwa [pow_one], z, rfl⟩

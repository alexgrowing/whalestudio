import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

section AmpleProof

variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}

theorem pow_mul_pow_le (Q : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) (a b : ℕ) :
    ((Q.pow a).sub I).restrictScalars S * ((Q.pow b).sub I).restrictScalars S ≤
      ((Q.pow (a + b)).sub I).restrictScalars S := by
  induction b with
  | zero =>
    rw [Submodule.mul_le]
    intro p hp q hq
    rw [Submodule.restrictScalars_mem, pow_zero_sub] at hq
    rw [Submodule.restrictScalars_mem] at hp ⊢
    rw [Nat.add_zero, mul_comm]
    have := Submodule.smul_mem _ (⟨q, hq⟩ : Kleiman.chartRing S x I) hp
    rwa [Kleiman.chartRing_smul_def] at this
  | succ b ih =>
    have h1 : ((Q.pow (b + 1)).sub I).restrictScalars S =
        ((Q.pow b).sub I).restrictScalars S * (Q.sub I).restrictScalars S :=
      (mul_eq_twist (Q.pow b) Q I).symm
    have h2 : ((Q.pow (a + (b + 1))).sub I).restrictScalars S =
        ((Q.pow (a + b)).sub I).restrictScalars S * (Q.sub I).restrictScalars S :=
      (mul_eq_twist (Q.pow (a + b)) Q I).symm
    rw [h1, h2, ← mul_assoc]
    exact mul_le_mul' ih le_rfl

theorem mul_mem_pow (Q : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) {a b : ℕ} {p q : Ω}
    (hp : p ∈ (Q.pow a).sub I) (hq : q ∈ (Q.pow b).sub I) : p * q ∈ (Q.pow (a + b)).sub I :=
  pow_mul_pow_le Q I a b (Submodule.mul_mem_mul (M := ((Q.pow a).sub I).restrictScalars S)
    (N := ((Q.pow b).sub I).restrictScalars S) hp hq)

theorem pow_mem_pow (Q : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) {m : ℕ} {h : Ω}
    (hh : h ∈ (Q.pow m).sub I) (n : ℕ) : h ^ n ∈ (Q.pow (m * n)).sub I := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.mul_zero, pow_zero_sub]
    exact one_mem _
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact mul_mem_pow Q I ih hh

def ampleSub (Q : Kleiman.SubSystem S x Ω) (m : ℕ) (h : Ω) (hh : ∀ I, h ∈ (Q.pow m).sub I) :
    Subalgebra S Ω where
  carrier := Kleiman.ampleRing Q m h
  mul_mem' := by
    intro a b ha hb
    refine Set.mem_iInter.mpr fun I => ?_
    obtain ⟨n, hn⟩ := Set.mem_iInter.mp ha I
    obtain ⟨n', hn'⟩ := Set.mem_iInter.mp hb I
    refine ⟨n + n', ?_⟩
    have e : a * b * h ^ (n + n') = a * h ^ n * (b * h ^ n') := by ring
    rw [e, Nat.mul_add]
    exact mul_mem_pow Q I hn hn'
  add_mem' := by
    intro a b ha hb
    refine Set.mem_iInter.mpr fun I => ?_
    obtain ⟨n, hn⟩ := Set.mem_iInter.mp ha I
    obtain ⟨n', hn'⟩ := Set.mem_iInter.mp hb I
    refine ⟨n + n', ?_⟩
    have e : (a + b) * h ^ (n + n') = a * h ^ n * h ^ n' + b * h ^ n' * h ^ n := by ring
    rw [e, Nat.mul_add]
    refine add_mem (mul_mem_pow Q I hn (pow_mem_pow Q I (hh I) n')) ?_
    rw [Nat.add_comm (m * n)]
    exact mul_mem_pow Q I hn' (pow_mem_pow Q I (hh I) n)
  algebraMap_mem' s := by
    refine Set.mem_iInter.mpr fun I => ⟨0, ?_⟩
    rw [pow_zero, mul_one, Nat.mul_zero, pow_zero_sub]
    exact Subalgebra.algebraMap_mem _ s

end AmpleProof

theorem Ample.proof : Ample.Statement := by
  intro S _ N Ω _ _ x H A
  have hxI : ∀ I : Kleiman.Chart x, ∃ i ∈ I.1, x i ≠ 0 := fun I =>
    let ⟨i, hi⟩ := I.2.1
    ⟨i, hi, (Kleiman.mem_support x).mp (I.2.2 hi)⟩
  have hsub : ∀ k I, A.h k ∈ (H.pow A.m).sub I := by
    intro k I
    have := A.mem_secs k
    rw [Kleiman.SubSystem.secs, Submodule.mem_iInf] at this
    exact this I
  refine ⟨{ m := A.m, m_pos := A.m_pos, M := A.r, h := A.h, gen := ⟨?_, ?_⟩, finite := ?_ }⟩
  · intro k
    simp only [IndefiniteRowSideFullHecke.Kleiman.secs, Submodule.mem_iInf]
    intro i hi
    rw [lpow.equiv _ A.m_pos hi, chartModule_of_ne_zero _ hi, Submodule.restrictScalars_mem]
    exact hsub k _
  · intro i hi
    rw [lpow.equiv _ A.m_pos hi, chartModule_of_ne_zero _ hi, chartRing.equiv S x hi, span_image2_eq,
      A.generates]
  · intro j hj
    obtain ⟨t, ht⟩ := A.finite j hj
    have hle : IndefiniteRowSideFullHecke.Kleiman.regOn S x (toIndefiniteRowSideFullHecke H.toSubSystem) A.m A.h j ≤
        ampleSub H.toSubSystem A.m (A.h j) (hsub j) := by
      rw [IndefiniteRowSideFullHecke.Kleiman.regOn, Algebra.adjoin_le_iff]
      intro f hf
      show f ∈ Kleiman.ampleRing H.toSubSystem A.m (A.h j)
      refine Set.mem_iInter.mpr fun I => ?_
      obtain ⟨i, hiI, hi⟩ := hxI I
      obtain ⟨n, hn⟩ := hf i hi
      refine ⟨n, ?_⟩
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp only [pow_zero, mul_one, Submodule.mem_one] at hn
        obtain ⟨s, rfl⟩ := hn
        rw [pow_zero, mul_one, Nat.mul_zero, pow_zero_sub]
        exact Subalgebra.algebraMap_mem _ s
      · have key : IndefiniteRowSideFullHecke.Kleiman.lpow S (toIndefiniteRowSideFullHecke H.toSubSystem) A.m i ^ n =
            IndefiniteRowSideFullHecke.Kleiman.lpow S (toIndefiniteRowSideFullHecke H.toSubSystem) (A.m * n) i := by
          simp only [IndefiniteRowSideFullHecke.Kleiman.lpow, pow_mul]
        rw [key, lpow.equiv _ (Nat.mul_pos A.m_pos hn0) hi, chartModule_of_ne_zero _ hi,
          Submodule.restrictScalars_mem] at hn
        exact (H.pow (A.m * n)).mono _ I (Finset.singleton_subset_iff.mpr hiI) _ hn
    exact ⟨t, fun f hf => ht (hle hf)⟩

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

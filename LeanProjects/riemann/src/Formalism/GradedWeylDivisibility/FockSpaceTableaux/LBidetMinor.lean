import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

def initW (n s : ℕ) : Fin n → ℕ := fun t => if t.val < s then 1 else 0

theorem sum_single_castLE {n s : ℕ} (hs : s ≤ n) :
    (∑ q : Fin s, (Pi.single (Fin.castLE hs q) 1 : Fin n → ℕ)) = initW n s := by
  funext t
  rw [Finset.sum_apply]
  simp only [initW]
  by_cases h : t.val < s
  · rw [if_pos h, Finset.sum_eq_single ⟨t.val, h⟩]
    · have e : Fin.castLE hs ⟨t.val, h⟩ = t := Fin.ext rfl
      rw [e, Pi.single_eq_same]
    · intro q _ hq
      rw [Pi.single_apply, if_neg]
      intro htq
      apply hq
      subst htq
      exact Fin.ext rfl
    · intro hq
      exact absurd (Finset.mem_univ _) hq
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [Pi.single_apply, if_neg]
    intro htq
    apply h
    subst htq
    exact q.isLt

theorem initMinor_isWeightedHomogeneous {R : Type*} [CommRing R] {r n s : ℕ}
    (I : Fin s → Fin r) (hs : s ≤ n) :
    IsWeightedHomogeneous (colW r n) (initMinor R I hs) (initW n s) := by
  rw [← mem_weightedHomogeneousSubmodule]
  unfold initMinor
  rw [Matrix.det_apply]
  refine _root_.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule, ← sum_single_castLE hs]
  apply IsWeightedHomogeneous.prod
  intro q _
  exact isWeightedHomogeneous_X (R := R) (colW r n) (I (σ q), Fin.castLE hs q)

theorem algHom_det_of {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (φ : A →ₐ[R] B) {s : ℕ} (M : Fin s → Fin s → A) :
    φ (Matrix.of M).det = (Matrix.of fun p q => φ (M p q)).det := by
  rw [AlgHom.map_det]
  rfl

theorem colAddGen_X {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n) (v : Fin r × Fin n) :
    colAddGen R l j (X v) =
      if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) := by
  simp only [colAddGen, aeval_X]

theorem initMinor_invariant {R : Type*} [CommRing R] {r n s : ℕ}
    (I : Fin s → Fin r) (hs : s ≤ n) (l j : Fin n) (hlj : l < j) :
    colAddGen R l j (initMinor R I hs) = rename some (initMinor R I hs) := by
  unfold initMinor
  rw [algHom_det_of, algHom_det_of]
  simp only [colAddGen_X, rename_X]
  by_cases hj : j.val < s
  · have hl : l.val < s := Nat.lt_trans (show l.val < j.val from hlj) hj
    have hjl : (⟨j.val, hj⟩ : Fin s) ≠ ⟨l.val, hl⟩ := by
      intro h
      exact hlj.ne' (Fin.ext (Fin.mk.inj_iff.mp h))
    rw [← Matrix.det_updateCol_add_smul_self
      (Matrix.of fun p q : Fin s =>
        (X (some (I p, Fin.castLE hs q)) : MvPolynomial (Option (Fin r × Fin n)) R)) hjl (X none)]
    congr 1
    ext p q
    simp only [Matrix.updateCol_apply, Matrix.of_apply]
    by_cases hq : q = ⟨j.val, hj⟩
    · subst hq
      have e1 : Fin.castLE hs ⟨j.val, hj⟩ = j := Fin.ext rfl
      have e2 : Fin.castLE hs ⟨l.val, hl⟩ = l := Fin.ext rfl
      rw [e1, e2]
      simp
    · have hne : Fin.castLE hs q ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        exact hq (Fin.ext hv)
      rw [if_neg hne, if_neg hq]
  · congr 1
    ext p q
    simp only [Matrix.of_apply]
    have hne : Fin.castLE hs q ≠ j := by
      intro h
      apply hj
      rw [← h]
      exact q.isLt
    rw [if_neg hne]

theorem initMinor_mem {R : Type*} [CommRing R] {r n s : ℕ}
    (I : Fin s → Fin r) (hs : s ≤ n) :
    initMinor R I hs ∈ dualWeyl R r n (initW n s) := by
  unfold dualWeyl
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact initMinor_isWeightedHomogeneous I hs
  · simp only [Submodule.mem_iInf]
    intro l j hlj
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact initMinor_invariant I hs l j hlj

end Formalism.GradedWeylDivisibility

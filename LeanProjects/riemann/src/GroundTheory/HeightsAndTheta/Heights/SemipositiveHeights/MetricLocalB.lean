import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterExtLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedG
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace MetricLocalB

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem induct (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) :
    ∀ (n : ℕ) (P : Ideal (MRing ι)) (L L' : Fin n → HermLine ι),
      IsArithVar P n → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) →
      (∀ j, (L j).a = (L' j).a) → (∀ j, ∀ z ∈ mcPts P, (L j).h z = (L' j).h z) →
      I P n L = I P n L'
  | 0, P, L, L', _, _, _, _, _ => by rw [Subsingleton.elim L L']
  | n + 1, P, L, L', hP, hL, hL', ha, hh => by

    have key : ∀ (C C' : HermLine ι) (b : K → ℕ), (∀ k, C.a k = b k) → (∀ k, C'.a k = b k) →
        IsSmoothHerm C → IsSmoothHerm C' → (∀ z ∈ mcPts P, C.h z = C'.h z) →
        I P (n + 1) (Fin.snoc (Fin.init L) C) = I P (n + 1) (Fin.snoc (Fin.init L') C') := by
      intro C C' b hC hC' hCs hC's hCC'
      have hPp : P.IsPrime := hP.2.1.1
      choose i hi using hP.2.1.2.2
      have hs := isMultiHomog_secOf i b
      have hsP := secOf_not_mem hPp hi b
      rw [hI.2.2 P n (Fin.init L) C (secOf i b) b hP (fun j => hL j.castSucc) hCs hC hs hsP,
        hI.2.2 P n (Fin.init L') C' (secOf i b) b hP (fun j => hL' j.castSucc) hC's hC' hs hsP]
      unfold recR
      congr 1
      · refine finsum_mem_congr rfl fun W hW => ?_
        congr 1
        split_ifs with hWh
        · have hWa : IsArithVar W n :=
            (divSuppArith K ι P n C (secOf i b) W hP ⟨b, hC, hs, hsP⟩ hW).1 hWh
          have hPW : P ≤ W := le_trans le_sup_left hW.1.1.2
          exact induct I hI n W (Fin.init L) (Fin.init L') hWa (fun j => hL j.castSucc)
            (fun j => hL' j.castSucc) (fun j => ha j.castSucc)
            (fun j z hz => hh j.castSucc z ⟨hz.1, fun f hf => hz.2 f (hPW hf)⟩)
        · have e : (fun j => (Fin.init L j).a) = fun j => (Fin.init L' j).a :=
            funext fun j => ha j.castSucc
          rw [e]
      · unfold arInt
        exact (ptsLocal K ι P n 0 _ _ _ _
          (fun j z hz => congrArg Real.log (hh j.castSucc z hz))
          (fun z hz => by unfold logNorm; rw [hCC' z hz])).2

    set A := L (Fin.last n) with hA
    set A' := L' (Fin.last n) with hA'
    let b : K → ℕ := fun k => (A.a k).natAbs
    let B : HermLine ι := HermLine.sqMetric b
    have hB : IsSmoothHerm B := isSmoothHerm_sqMetric b
    let c : K → ℕ := fun k => (A.a k + (A.a k).natAbs).toNat
    have hBa : ∀ k, B.a k = b k := fun k => rfl
    have hc : ∀ k, (A.tensor B).a k = c k := by
      intro k
      show A.a k + ((A.a k).natAbs : ℤ) = ((A.a k + (A.a k).natAbs).toNat : ℤ)
      rw [Int.toNat_of_nonneg (by omega)]
    have hc' : ∀ k, (A'.tensor B).a k = c k := by
      intro k
      rw [← hc k]
      show A'.a k + B.a k = A.a k + B.a k
      rw [hA, hA', ha (Fin.last n)]
    have hAs : IsSmoothHerm A := hL _
    have hA's : IsSmoothHerm A' := hL' _
    have e1 := hI.2.1 P n (Fin.init L) A B hP (fun j => hL j.castSucc) hAs hB
    have e1' := hI.2.1 P n (Fin.init L') A' B hP (fun j => hL' j.castSucc) hA's hB
    have k1 := key (A.tensor B) (A'.tensor B) c hc hc' (isSmoothHerm_tensor hAs hB)
      (isSmoothHerm_tensor hA's hB) (fun z hz => by
        show A.h z * B.h z = A'.h z * B.h z
        rw [hA, hA', hh (Fin.last n) z hz])
    have k2 := key B B b hBa hBa hB hB (fun _ _ => rfl)
    calc I P (n + 1) L = I P (n + 1) (Fin.snoc (Fin.init L) A) := by rw [hA, Fin.snoc_init_self]
      _ = I P (n + 1) (Fin.snoc (Fin.init L) (A.tensor B)) - I P (n + 1) (Fin.snoc (Fin.init L) B) := by
          rw [e1]; ring
      _ = I P (n + 1) (Fin.snoc (Fin.init L') (A'.tensor B)) - I P (n + 1) (Fin.snoc (Fin.init L') B) := by
          rw [k1, k2]
      _ = I P (n + 1) (Fin.snoc (Fin.init L') A') := by rw [e1']; ring
      _ = I P (n + 1) L' := by rw [hA', Fin.snoc_init_self]

end MetricLocalB

theorem MetricLocalB.full : MetricLocalStatement := by
  intro K _ ι _ I hI P n L L' hP hL hL' ha hh
  exact MetricLocalB.induct I hI n P L L' hP hL hL' ha hh

end GroundTheory.Heights₂.Heights

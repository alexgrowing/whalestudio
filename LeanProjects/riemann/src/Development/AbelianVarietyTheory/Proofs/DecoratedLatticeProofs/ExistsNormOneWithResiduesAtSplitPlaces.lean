import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory.LevNorm

theorem exists_normOne_residues {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)]
    {r : ∀ Q, S →+* k Q} (Z : PlaceSys A S P k r) (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S)
    (T : Finset P) (hT : ∀ Q ∈ T, ∀ Q' ∈ T, σ (Z.e Q) ≠ Z.e Q') (c : ∀ Q, (k Q)ˣ) :
    ∃ z : S, (z : A) * σ z = 1 ∧ (∀ Q ∈ T, r Q z = c Q) ∧
      ∀ b : A, (∀ Q ∈ T, Z.p Q b ∈ Z.O Q ∧ Z.p Q (σ b) ∈ Z.O Q) → (1 - (z : A)) * b ∈ S := by
  classical

  have comp : ∀ (f : P → A) Q0, Z.p Q0 (∑ Q ∈ T, Z.e Q * f Q) = if Q0 ∈ T then Z.p Q0 (f Q0) else 0 := by
    intro f Q0
    rw [map_sum]
    by_cases h : Q0 ∈ T
    · rw [if_pos h, Finset.sum_eq_single_of_mem Q0 h
        (fun Q _ hQ => by rw [map_mul, Z.e_ne Q Q0 (Ne.symm hQ), zero_mul]), map_mul, Z.e_self, one_mul]
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun Q hQ => by
        rw [map_mul, Z.e_ne Q Q0 (by rintro rfl; exact h hQ), zero_mul]
  have smem : ∀ f : P → A, (∀ Q, f Q ∈ S) → (∑ Q ∈ T, Z.e Q * f Q) ∈ S := fun f hf =>
    Subring.sum_mem _ fun Q _ => Subring.mul_mem _ (Z.e_mem Q) (hf Q)

  choose s hs using fun Q => Z.r_surj Q (c Q : k Q)
  have hval : ∀ Q, (Z.O Q).valuation (Z.p Q (s Q)) = 1 := fun Q => by
    have hm : Z.p Q (s Q) ∈ Z.O Q := (Z.int _).1 (s Q).2 Q
    refine le_antisymm (((Z.O Q).valuation_le_one_iff _).2 hm) (not_lt.1 fun hc => ?_)
    have := (Z.r_ker Q (s Q)).2 hc
    rw [hs Q] at this
    exact (c Q).ne_zero this
  have hne : ∀ Q, Z.p Q (s Q) ≠ 0 := fun Q e => by
    have := hval Q; rw [e, map_zero] at this; exact zero_ne_one this
  have hinv : ∀ Q, (Z.p Q (s Q))⁻¹ ∈ Z.O Q := fun Q => by
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hval Q, inv_one]
  choose t ht using fun Q => Z.pO_surj Q ⟨_, hinv Q⟩
  have hpt : ∀ Q, Z.p Q (t Q) = (Z.p Q (s Q))⁻¹ := fun Q => by
    rw [← Z.pO_coe, ht Q]

  obtain ⟨E, hEd⟩ : ∃ E, E = ∑ Q ∈ T, Z.e Q * 1 := ⟨_, rfl⟩
  obtain ⟨a, had⟩ : ∃ a, a = ∑ Q ∈ T, Z.e Q * (s Q : A) := ⟨_, rfl⟩
  obtain ⟨bb, hbd⟩ : ∃ bb, bb = ∑ Q ∈ T, Z.e Q * (t Q : A) := ⟨_, rfl⟩
  have pE : ∀ Q0, Z.p Q0 E = if Q0 ∈ T then 1 else 0 := fun Q0 => by
    rw [hEd, comp, map_one]
  have pa : ∀ Q0, Z.p Q0 a = if Q0 ∈ T then Z.p Q0 (s Q0) else 0 := fun Q0 => by rw [had, comp]
  have pb : ∀ Q0, Z.p Q0 bb = if Q0 ∈ T then Z.p Q0 (t Q0) else 0 := fun Q0 => by rw [hbd, comp]
  have pF : ∀ Q0 ∈ T, Z.p Q0 (σ E) = 0 := fun Q0 hQ0 => by
    rw [hEd, map_sum, map_sum]
    refine Finset.sum_eq_zero fun Q hQ => ?_
    obtain ⟨Q3, h3⟩ := Z.exists_bar hσ Q
    rw [map_mul, map_one, mul_one, h3, Z.e_ne Q3 Q0 (fun h => hT Q hQ Q0 hQ0 (by rw [h3, h]))]
  have Emem : E ∈ S := hEd ▸ smem _ fun _ => one_mem _
  have amem : a ∈ S := had ▸ smem _ fun Q => (s Q).2
  have bmem : bb ∈ S := hbd ▸ smem _ fun Q => (t Q).2
  have hE : E * E = E := Z.ext' fun Q0 => by rw [map_mul, pE]; split_ifs <;> simp
  have hEF : E * σ E = 0 := Z.ext' fun Q0 => by
    rw [map_mul, map_zero]
    by_cases h : Q0 ∈ T
    · rw [pF Q0 h, mul_zero]
    · rw [pE, if_neg h, zero_mul]
  have ha : E * a = a := Z.ext' fun Q0 => by rw [map_mul, pE, pa]; split_ifs <;> simp
  have hb : E * bb = bb := Z.ext' fun Q0 => by rw [map_mul, pE, pb]; split_ifs <;> simp
  have hab : a * bb = E := Z.ext' fun Q0 => by
    rw [map_mul, pE, pa, pb]
    split_ifs
    · rw [hpt, mul_inv_cancel₀ (hne Q0)]
    · simp
  set F := σ E with hFd
  set x := σ a with hxd
  set y := σ bb with hyd
  have hF : F * F = F := by rw [hFd, ← map_mul, hE]
  have hFx : F * x = x := by rw [hFd, hxd, ← map_mul, ha]
  have hFy : F * y = y := by rw [hFd, hyd, ← map_mul, hb]
  have hxy : x * y = F := by rw [hFd, hxd, hyd, ← map_mul, hab]
  have hEx : E * x = 0 := by rw [← hFx, ← mul_assoc, hEF, zero_mul]
  have hEy : E * y = 0 := by rw [← hFy, ← mul_assoc, hEF, zero_mul]
  have hFa : F * a = 0 := by rw [← ha, ← mul_assoc, mul_comm F E, hEF, zero_mul]
  have hFb : F * bb = 0 := by rw [← hb, ← mul_assoc, mul_comm F E, hEF, zero_mul]
  have hax : a * x = 0 := by
    calc a * x = (E * a) * (F * x) := by rw [ha, hFx]
      _ = (E * F) * (a * x) := by ring
      _ = 0 := by rw [hEF, zero_mul]
  have hby : bb * y = 0 := by
    calc bb * y = (E * bb) * (F * y) := by rw [hb, hFy]
      _ = (E * F) * (bb * y) := by ring
      _ = 0 := by rw [hEF, zero_mul]
  have zmem : 1 - E - F + a + y ∈ S :=
    add_mem (add_mem (sub_mem (sub_mem (one_mem _) Emem) (hS _ Emem)) amem) (hS _ bmem)
  refine ⟨⟨1 - E - F + a + y, zmem⟩, ?_, ?_, ?_⟩
  · show (1 - E - F + a + y) * σ (1 - E - F + a + y) = 1
    have hσF : σ F = E := hσ E
    have hσy : σ y = bb := hσ bb
    rw [map_add, map_add, map_sub, map_sub, map_one, hσF, hσy]
    linear_combination hE + hF + 2 * hEF - hEx - hb - hFx - hFb - ha - hFy - hFa - hEy + hax + hab + hxy + hby
  · intro Q hQ
    rw [← hs Q]
    refine Z.r_congr Q ?_
    show Z.p Q (1 - E - F + a + y) = Z.p Q (s Q)
    have hy0 : Z.p Q y = 0 := by rw [← hFy, map_mul, pF Q hQ, zero_mul]
    rw [map_add, map_add, map_sub, map_sub, map_one, pE, if_pos hQ, pF Q hQ, pa, if_pos hQ, hy0]
    ring
  · intro w hw
    show (1 - (1 - E - F + a + y)) * w ∈ S
    have key : (1 - (1 - E - F + a + y)) * w = (E - a) * w + σ ((E - bb) * σ w) := by
      rw [map_mul, map_sub, hσ w]; ring
    rw [key]
    refine add_mem ((Z.int _).2 fun Q0 => ?_) (hS _ ((Z.int _).2 fun Q0 => ?_))
    · rw [map_mul, map_sub, pE, pa]
      by_cases h : Q0 ∈ T
      · rw [if_pos h, if_pos h]
        exact Subring.mul_mem _ (sub_mem (one_mem _) ((Z.int _).1 (s Q0).2 Q0)) (hw Q0 h).1
      · rw [if_neg h, if_neg h, sub_zero, zero_mul]; exact zero_mem _
    · rw [map_mul, map_sub, pE, pb]
      by_cases h : Q0 ∈ T
      · rw [if_pos h, if_pos h]
        exact Subring.mul_mem _ (sub_mem (one_mem _) ((Z.int _).1 (t Q0).2 Q0)) (hw Q0 h).2
      · rw [if_neg h, if_neg h, sub_zero, zero_mul]; exact zero_mem _

end GlobalTheory.LevNorm

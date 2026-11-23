import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HalfWeight

open Finset

lemma ee_add (x y : ℂ) : ee (x + y) = ee x * ee y := by
  unfold ee
  rw [← Complex.exp_add]
  ring_nf

lemma ee_intCast (k : ℤ) : ee (k : ℂ) = 1 := by
  unfold ee
  rw [← Complex.exp_int_mul_two_pi_mul_I k]
  ring_nf

noncomputable def e1 (d : ℕ) (m : ℤ) : ℂ := ee ((m : ℂ) / d)

lemma root_of_unity_character_add (d : ℕ) (m k : ℤ) : e1 d (m + k) = e1 d m * e1 d k := by
  unfold e1
  rw [← ee_add]
  push_cast
  ring_nf

lemma root_of_unity_character_periodic (d : ℕ) (hd : 0 < d) (m k : ℤ) : e1 d (m + d * k) = e1 d m := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [root_of_unity_character_add]
  have : e1 d (d * k) = 1 := by
    unfold e1
    have : (((d : ℤ) * k : ℤ) : ℂ) / d = (k : ℂ) := by
      push_cast
      field_simp
    rw [this, ee_intCast]
  rw [this, mul_one]

lemma per_emod (f : ℤ → ℂ) (d : ℕ) (hf : ∀ x, f (x + d) = f x) (x : ℤ) : f (x % d) = f x := by
  have h : Function.Periodic f (d : ℤ) := hf
  have h2 := (h.int_mul (x / d)) (x % d)
  rw [← h2]
  congr 1
  rw [Int.emod_def]
  simp only [Int.cast_id]
  ring

lemma f_val (f : ℤ → ℂ) (d : ℕ) [NeZero d] (hf : ∀ x, f (x + d) = f x) (x : ℤ) :
    f (((x : ZMod d).val : ℕ) : ℤ) = f x := by
  rw [ZMod.val_intCast]
  exact per_emod f d hf x

lemma sum_range_zmod (d : ℕ) [NeZero d] (f : ℤ → ℂ) :
    ∑ x ∈ range d, f (x : ℤ) = ∑ y : ZMod d, f ((y.val : ℕ) : ℤ) := by
  symm
  refine Finset.sum_nbij' (fun y => y.val) (fun x => (x : ZMod d)) ?_ ?_ ?_ ?_ ?_
  · intro y _
    simpa using ZMod.val_lt y
  · intro x _
    simp
  · intro y _
    simp
  · intro x hx
    exact ZMod.val_cast_of_lt (by simpa using hx)
  · intro y _
    rfl

lemma sum_affine (d : ℕ) (hd : 0 < d) (f : ℤ → ℂ) (hf : ∀ x, f (x + d) = f x) (u t : ℤ)
    (hu : IsCoprime u (d : ℤ)) :
    ∑ x ∈ range d, f (u * (x : ℤ) + t) = ∑ x ∈ range d, f (x : ℤ) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hU : IsUnit (u : ZMod d) := by
    obtain ⟨p, q, hpq⟩ := hu
    have h1 : ((p * u + q * d : ℤ) : ZMod d) = 1 := by rw [hpq]; simp
    push_cast at h1
    simp only [ZMod.natCast_self, mul_zero, add_zero] at h1
    exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h1)
  rw [sum_range_zmod d (fun x => f (u * x + t)), sum_range_zmod d f]
  let e : ZMod d → ZMod d := fun y => (u : ZMod d) * y + (t : ZMod d)
  have hinj : Function.Injective e := by
    intro y z hyz
    have : (u : ZMod d) * y = (u : ZMod d) * z := add_right_cancel hyz
    exact hU.mul_left_cancel this
  have he : Function.Bijective e := Finite.injective_iff_bijective.1 hinj
  rw [← he.sum_comp (fun y => f ((y.val : ℕ) : ℤ))]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h3 : e y = ((u * ((y.val : ℕ) : ℤ) + t : ℤ) : ZMod d) := by
    simp [e]
  rw [h3, f_val f d hf]

lemma sum_crt (M d : ℕ) (hM : 0 < M) (hd : 0 < d) (h : Nat.Coprime M d) (G : ℤ → ℂ)
    (hG : ∀ x, G (x + ((M * d : ℕ) : ℤ)) = G x) :
    ∑ x ∈ range (M * d), G (x : ℤ) =
      ∑ x1 ∈ range M, ∑ x2 ∈ range d, G ((d : ℤ) * x1 + M * x2) := by
  haveI : NeZero (M * d) := ⟨(Nat.mul_pos hM hd).ne'⟩
  rw [sum_range_zmod (M * d) G, ← Finset.sum_product']
  symm
  let i : ℕ × ℕ → ZMod (M * d) := fun p => ((d * p.1 + M * p.2 : ℕ) : ZMod (M * d))
  have hinj : Set.InjOn i (range M ×ˢ range d : Finset (ℕ × ℕ)) := by
    rintro ⟨x1, x2⟩ hx ⟨y1, y2⟩ hy hxy
    simp only [coe_product, Set.mem_prod, mem_coe, mem_range] at hx hy
    have hm : (d * x1 + M * x2) ≡ (d * y1 + M * y2) [MOD M * d] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).1 hxy
    have h1 : (d * x1 + M * x2) ≡ (d * y1 + M * y2) [MOD M] := hm.of_mul_right d
    have h2 : (d * x1 + M * x2) ≡ (d * y1 + M * y2) [MOD d] := hm.of_mul_left M
    have h1' : d * x1 ≡ d * y1 [MOD M] := by
      simpa [Nat.ModEq] using h1
    have h2' : M * x2 ≡ M * y2 [MOD d] := by
      simpa [Nat.ModEq] using h2
    have e1' : x1 ≡ y1 [MOD M] := Nat.ModEq.cancel_left_of_coprime h h1'
    have e2' : x2 ≡ y2 [MOD d] := Nat.ModEq.cancel_left_of_coprime h.symm h2'
    have r1 := Nat.ModEq.eq_of_lt_of_lt e1' hx.1 hy.1
    have r2 := Nat.ModEq.eq_of_lt_of_lt e2' hx.2 hy.2
    simp [r1, r2]
  have hsurj : Set.SurjOn i (range M ×ˢ range d : Finset (ℕ × ℕ)) (univ : Finset (ZMod (M * d))) :=
    Finset.surjOn_of_injOn_of_card_le i (fun _ _ => mem_coe.2 (mem_univ _)) hinj
      (by simp [ZMod.card])
  refine Finset.sum_bij (fun p _ => i p) (fun _ _ => mem_univ _) (fun p hp q hq hpq => hinj hp hq hpq) ?_ ?_
  · intro y _
    obtain ⟨p, hp, hpy⟩ := hsurj (mem_coe.2 (mem_univ y))
    exact ⟨p, hp, hpy⟩
  · intro p _
    have : i p = (((d : ℤ) * p.1 + M * p.2 : ℤ) : ZMod (M * d)) := by
      simp [i]
    rw [this, f_val G (M * d) hG]

lemma inner_sum (M d : ℕ) (hd : 0 < d) (a b c' n : ℤ) (hcop : IsCoprime (M : ℤ) (d : ℤ))
    (hyp : a * d - b * (4 * (M : ℤ) ^ 2 * c') = 1) :
    ∑ x ∈ range d, e1 d (b * (M : ℤ) ^ 2 * (x : ℤ) ^ 2 + n * x) = e1 d (c' * n ^ 2) * GS b d := by
  have hper : ∀ (A B : ℤ) (x : ℤ), e1 d (A * (x + d) ^ 2 + B * (x + d)) = e1 d (A * x ^ 2 + B * x) := by
    intro A B x
    rw [← root_of_unity_character_periodic d hd (A * x ^ 2 + B * x) (A * (2 * x + d) + B)]
    congr 1
    ring
  have h1 := sum_affine d hd (fun x => e1 d (b * (M : ℤ) ^ 2 * x ^ 2 + n * x))
    (fun x => hper (b * (M : ℤ) ^ 2) n x) 1 (2 * c' * n)
    isCoprime_one_left
  have h2 := sum_affine d hd (fun x => e1 d (b * x ^ 2 + 0 * x))
    (fun x => hper b 0 x) M 0 hcop
  rw [← h1]
  have h3 : ∀ x : ℕ, e1 d (b * (M : ℤ) ^ 2 * (1 * (x : ℤ) + 2 * c' * n) ^ 2 + n * (1 * (x : ℤ) + 2 * c' * n)) =
      e1 d (c' * n ^ 2) * e1 d (b * ((M : ℤ) * x + 0) ^ 2 + 0 * ((M : ℤ) * x + 0)) := by
    intro x
    rw [← root_of_unity_character_add, ← root_of_unity_character_periodic d hd _ (-(a * (n * x + c' * n ^ 2)))]
    congr 1
    linear_combination (n * x + c' * n ^ 2) * (-hyp)
  rw [Finset.sum_congr rfl fun x _ => h3 x, ← Finset.mul_sum, h2]
  congr 1
  unfold GS e1
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  push_cast
  ring

theorem finite_sum_splitting : T2 := by
  intro M d _ ψ a b c' n hd hyp
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hcop : IsCoprime (M : ℤ) (d : ℤ) := ⟨-(b * 4 * M * c'), a, by linear_combination hyp⟩
  have hnc : Nat.Coprime M d := Nat.isCoprime_iff_coprime.1 hcop
  let G : ℤ → ℂ := fun x => ψ (x : ZMod M) * e1 d (b * x ^ 2) * e1 (M * d) (n * x)
  have hG : ∀ x, G (x + ((M * d : ℕ) : ℤ)) = G x := by
    intro x
    have h1 : (((x + ((M * d : ℕ) : ℤ) : ℤ)) : ZMod M) = (x : ZMod M) := by
      simp
    have h2 : e1 d (b * (x + ((M * d : ℕ) : ℤ)) ^ 2) = e1 d (b * x ^ 2) := by
      rw [← root_of_unity_character_periodic d hd (b * x ^ 2) (b * (2 * x * M + (M : ℤ) ^ 2 * d))]
      congr 1
      push_cast
      ring
    have h3 : e1 (M * d) (n * (x + ((M * d : ℕ) : ℤ))) = e1 (M * d) (n * x) := by
      rw [← root_of_unity_character_periodic (M * d) (Nat.mul_pos hM hd) (n * x) n]
      congr 1
      ring
    simp only [G]
    rw [h1, h2, h3]
  have hL : ∑ x ∈ range (M * d), ψ (x : ZMod M) * ee (b * (x : ℂ) ^ 2 / d) *
      ee (n * x / ((M * d : ℕ) : ℂ)) = ∑ x ∈ range (M * d), G (x : ℤ) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [G, e1]
  have hsplit : ∀ x1 x2 : ℕ, G ((d : ℤ) * x1 + M * x2) =
      ψ (d : ZMod M) * (ψ (x1 : ZMod M) * ee (n * x1 / M)) *
        e1 d (b * (M : ℤ) ^ 2 * (x2 : ℤ) ^ 2 + n * x2) := by
    intro x1 x2
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    have h1 : ((((d : ℤ) * x1 + M * x2 : ℤ)) : ZMod M) = (d : ZMod M) * (x1 : ZMod M) := by
      simp
    have h2 : e1 d (b * ((d : ℤ) * x1 + M * x2) ^ 2) = e1 d (b * (M : ℤ) ^ 2 * (x2 : ℤ) ^ 2) := by
      rw [← root_of_unity_character_periodic d hd (b * (M : ℤ) ^ 2 * (x2 : ℤ) ^ 2) (b * ((d : ℤ) * x1 ^ 2 + 2 * x1 * M * x2))]
      congr 1
      ring
    have h3 : e1 (M * d) (n * ((d : ℤ) * x1 + M * x2)) = ee (n * x1 / M) * e1 d (n * x2) := by
      unfold e1
      rw [← ee_add]
      congr 1
      push_cast
      field_simp
    simp only [G]
    rw [h1, h2, h3, root_of_unity_character_add, map_mul]
    ring
  rw [hL, sum_crt M d hM hd hnc G hG]
  simp only [hsplit]
  simp only [← Finset.mul_sum]
  rw [inner_sum M d hd a b c' n hcop hyp, ← Finset.sum_mul, ← Finset.mul_sum]
  have hc : e1 d (c' * n ^ 2) = ee (c' * (n : ℂ) ^ 2 / d) := by
    unfold e1
    push_cast
    rfl
  rw [hc]
  ring

end GlobalTheory.CompanionTheory.HalfWeight

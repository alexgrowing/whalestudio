import Mathlib
open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.TwoStepUnipotent

section
variable {S : Type} [Ring S] (st : S →+ S) (e₁ e₃ h : S)

def elt (b w : S) : S := 1 - st b + b + (w - h * (st b * b))

variable {st e₁ e₃ h}

theorem st_one (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x) : st 1 = 1 := by
  have h1 := hm 1 (st 1)
  rw [one_mul, hi, one_mul] at h1
  exact h1.symm

theorem st_half (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (hh : h + h = 1) (hc : ∀ x, h * x = x * h) : st h = h := by
  have h2 : st h + st h = 1 := by rw [← map_add, hh, st_one hm hi]
  have hd : (h - st h) + (h - st h) = 0 := by
    calc (h - st h) + (h - st h) = (h + h) - (st h + st h) := by abel
      _ = 0 := by rw [hh, h2, sub_self]
  have h3 : h - st h = 0 := by
    calc h - st h = (h - st h) * (h + h) := by rw [hh, mul_one]
      _ = ((h - st h) + (h - st h)) * h := by rw [mul_add, add_mul]
      _ = 0 := by rw [hd, zero_mul]
  exact (sub_eq_zero.mp h3).symm

theorem mul_aux {b c z b' c' z' : S} (h31 : e₃ * e₁ = 0)
    (h1 : b * e₃ = b) (h2 : z * e₃ = z) (h3 : e₃ * b' = 0) (h4 : e₁ * c' = c')
    (h5 : e₁ * z' = z') (h6 : c * e₁ = 0) :
    (1 - c + b + z) * (1 - c' + b' + z') = 1 - (c + c') + (b + b') + (z + z' - c * b') := by
  have k1 : c * c' = 0 := by
    calc c * c' = c * e₁ * c' := by rw [mul_assoc, h4]
      _ = 0 := by rw [h6, zero_mul]
  have k2 : c * z' = 0 := by
    calc c * z' = c * e₁ * z' := by rw [mul_assoc, h5]
      _ = 0 := by rw [h6, zero_mul]
  have k3 : b * c' = 0 := by
    calc b * c' = b * e₃ * (e₁ * c') := by rw [h1, h4]
      _ = b * (e₃ * e₁) * c' := by simp only [mul_assoc]
      _ = 0 := by rw [h31, mul_zero, zero_mul]
  have k4 : b * b' = 0 := by
    calc b * b' = b * e₃ * b' := by rw [h1]
      _ = 0 := by rw [mul_assoc, h3, mul_zero]
  have k5 : b * z' = 0 := by
    calc b * z' = b * e₃ * (e₁ * z') := by rw [h1, h5]
      _ = b * (e₃ * e₁) * z' := by simp only [mul_assoc]
      _ = 0 := by rw [h31, mul_zero, zero_mul]
  have k6 : z * c' = 0 := by
    calc z * c' = z * e₃ * (e₁ * c') := by rw [h2, h4]
      _ = z * (e₃ * e₁) * c' := by simp only [mul_assoc]
      _ = 0 := by rw [h31, mul_zero, zero_mul]
  have k7 : z * b' = 0 := by
    calc z * b' = z * e₃ * b' := by rw [h2]
      _ = 0 := by rw [mul_assoc, h3, mul_zero]
  have k8 : z * z' = 0 := by
    calc z * z' = z * e₃ * (e₁ * z') := by rw [h2, h5]
      _ = z * (e₃ * e₁) * z' := by simp only [mul_assoc]
      _ = 0 := by rw [h31, mul_zero, zero_mul]
  simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, k1, k2, k3, k4, k5, k6, k7, k8]
  abel

theorem elt_mul (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (hs : st e₁ = e₃) (h31 : e₃ * e₁ = 0) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    {b w b' w' : S} (hb : e₃ * b = 0 ∧ b * e₃ = b) (hb' : e₃ * b' = 0 ∧ b' * e₃ = b')
    (hw : w * e₃ = w) (hw' : e₁ * w' = w') :
    elt st h b w * elt st h b' w'
      = elt st h (b + b') (w + w' + h * (st b' * b - st b * b')) := by
  have he3 : st e₃ = e₁ := by rw [← hs, hi]
  have sb' : e₁ * st b' = st b' := by
    calc e₁ * st b' = st (b' * e₃) := by rw [hm, he3]
      _ = st b' := by rw [hb'.2]
  have sb : st b * e₁ = 0 := by
    calc st b * e₁ = st (e₃ * b) := by rw [hm, he3]
      _ = 0 := by rw [hb.1, map_zero]
  have hz : (w - h * (st b * b)) * e₃ = w - h * (st b * b) := by
    rw [sub_mul, hw, mul_assoc, mul_assoc, hb.2]
  have hz' : e₁ * (w' - h * (st b' * b')) = w' - h * (st b' * b') := by
    rw [mul_sub, hw', ← mul_assoc, ← hc e₁, mul_assoc, ← mul_assoc e₁, sb']
  have hprod := mul_aux (c := st b) (c' := st b') h31 hb.2 hz hb'.1 sb' hz' sb
  have e : ∀ x : S, x = h * x + h * x := fun x => by rw [← add_mul, hh, one_mul]
  simp only [elt]
  rw [hprod]
  conv_lhs => rw [e (st b * b')]
  simp only [map_add, add_mul, mul_add, mul_sub]
  abel

theorem st_elt (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (hh : h + h = 1) (hc : ∀ x, h * x = x * h) (b : S) {w : S} (hw : st w = -w) :
    st (elt st h b w) = elt st h (-b) (-w) := by
  simp only [elt, map_add, map_sub, map_neg, st_one hm hi, hi, hm, hw, st_half hm hi hh hc, neg_mul,
    mul_neg, neg_neg]
  rw [hc (st b * b)]
  abel

theorem elt_neg_mul (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (hs : st e₁ = e₃) (h31 : e₃ * e₁ = 0) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    {b w : S} (hb : e₃ * b = 0 ∧ b * e₃ = b) (hw : e₁ * w = w ∧ w * e₃ = w) :
    elt st h (-b) (-w) * elt st h b w = 1 := by
  rw [elt_mul hm hi hs h31 hh hc ⟨by rw [mul_neg, hb.1, neg_zero], by rw [neg_mul, hb.2]⟩ hb
    (by rw [neg_mul, hw.2]) hw.1]
  simp [elt]

theorem elt_mul_neg (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (hs : st e₁ = e₃) (h31 : e₃ * e₁ = 0) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    {b w : S} (hb : e₃ * b = 0 ∧ b * e₃ = b) (hw : e₁ * w = w ∧ w * e₃ = w) :
    elt st h b w * elt st h (-b) (-w) = 1 := by
  rw [elt_mul hm hi hs h31 hh hc hb ⟨by rw [mul_neg, hb.1, neg_zero], by rw [neg_mul, hb.2]⟩ hw.2
    (by rw [mul_neg, hw.1])]
  simp [elt]

theorem elt_cond (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (hs : st e₁ = e₃) (h31 : e₃ * e₁ = 0) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    {b w : S} (hb : e₁ * b = 0 ∧ e₃ * b = 0 ∧ b * e₃ = b)
    (hw : e₁ * w = w ∧ w * e₃ = w ∧ st w = -w) :
    st (elt st h b w) * elt st h b w = 1 ∧ (elt st h b w - 1) * e₁ = 0 ∧
      (1 - e₁) * (elt st h b w - 1) * (1 - e₃) = 0 := by
  obtain ⟨hb1, hb3, hb3'⟩ := hb
  obtain ⟨hw1, hw3, hws⟩ := hw
  have he3 : st e₃ = e₁ := by rw [← hs, hi]
  have f1 : st b * e₃ = 0 := by rw [← hs, ← hm, hb1, map_zero]
  have f2 : e₁ * st b = st b := by rw [← he3, ← hm, hb3']
  have f3 : b * e₁ = 0 := by rw [← hb3', mul_assoc, h31, mul_zero]
  have f4 : w * e₁ = 0 := by rw [← hw3, mul_assoc, h31, mul_zero]
  have f5 : st b * e₁ = 0 := by rw [← he3, ← hm, hb3, map_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [st_elt hm hi hh hc b hws]
    exact elt_neg_mul hm hi hs h31 hh hc ⟨hb3, hb3'⟩ ⟨hw1, hw3⟩
  · have e : (elt st h b w - 1) * e₁ = -(st b * e₁) + b * e₁ + (w * e₁ - h * (st b * (b * e₁))) := by
      simp only [elt, sub_mul, add_mul, one_mul, mul_assoc]
      abel
    rw [e, f5, f3, f4]
    simp
  · have hX : (elt st h b w - 1) * (1 - e₃) = -st b := by
      have e : (elt st h b w - 1) * (1 - e₃) =
          -st b + b + (w - h * (st b * b)) - (-(st b * e₃) + b * e₃ + (w * e₃ - h * (st b * (b * e₃)))) := by
        simp only [elt, sub_mul, mul_sub, add_mul, one_mul, mul_one, mul_assoc]
        abel
      rw [e, f1, hb3', hw3]
      abel
    rw [mul_assoc, hX, mul_neg, sub_mul, one_mul, f2, sub_self, neg_zero]

theorem exists_elt (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (h11 : e₁ * e₁ = e₁)
    (hs : st e₁ = e₃) (h31 : e₃ * e₁ = 0) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    {g : S} (h1 : st g * g = 1) (h2 : (g - 1) * e₁ = 0)
    (h3 : (1 - e₁) * (g - 1) * (1 - e₃) = 0) :
    ∃ b w, (e₁ * b = 0 ∧ e₃ * b = 0 ∧ b * e₃ = b) ∧ (e₁ * w = w ∧ w * e₃ = w ∧ st w = -w) ∧
      g = elt st h b w := by
  have he3 : st e₃ = e₁ := by rw [← hs, hi]
  have he33 : e₃ * e₃ = e₃ := by rw [← hs, ← hm, h11]
  obtain ⟨X, rfl⟩ : ∃ X, g = 1 + X := ⟨g - 1, by abel⟩
  have hX1 : X * e₁ = 0 := by rwa [add_sub_cancel_left] at h2
  have h3' : (1 - e₁) * X * (1 - e₃) = 0 := by rwa [add_sub_cancel_left] at h3
  have hU : st X + X + st X * X = 0 := by
    rw [map_add, st_one hm hi] at h1
    have e : (1 + st X) * (1 + X) = 1 + (st X + X + st X * X) := by noncomm_ring
    rw [e] at h1
    exact add_left_cancel (h1.trans (add_zero 1).symm)
  have hsX1 : st X * e₁ = 0 := by
    have e := congrArg (· * e₁) hU
    simp only [add_mul, mul_assoc, hX1, mul_zero, add_zero, zero_mul] at e
    exact e
  have he3X : e₃ * X = 0 := by
    have e : st (e₃ * X) = 0 := by rw [hm, he3, hsX1]
    rw [← hi (e₃ * X), e, map_zero]
  obtain ⟨b, hbdef⟩ : ∃ b, b = (1 - e₁) * X * e₃ := ⟨_, rfl⟩
  have hXb : X = b + e₁ * X := by
    have e : (1 - e₁) * X = b := by
      rw [hbdef]
      have e' := h3'
      rw [mul_sub, mul_one, sub_eq_zero] at e'
      exact e'
    rw [← e, sub_mul, one_mul]
    abel
  have hb1 : e₁ * b = 0 := by
    rw [hbdef]
    simp only [← mul_assoc, mul_sub, mul_one, h11, sub_self, zero_mul]
  have hb3 : e₃ * b = 0 := by
    rw [hbdef]
    simp only [← mul_assoc, mul_sub, mul_one, h31, sub_zero, he3X, zero_mul]
  have hb3' : b * e₃ = b := by rw [hbdef, mul_assoc, he33]
  have sb1 : e₁ * st b = st b := by rw [← he3, ← hm, hb3']
  have sb3 : st b * e₃ = 0 := by rw [← hs, ← hm, hb1, map_zero]
  have hsX : st X = st b + st X * e₃ := by
    conv_lhs => rw [hXb]
    rw [map_add, hm, hs]
  have hXX : st X * X = st b * b := by
    calc st X * X = st X * (b + e₁ * X) := by rw [← hXb]
      _ = st X * b + st X * e₁ * X := by rw [mul_add, mul_assoc]
      _ = (st b + st X * e₃) * b := by rw [hsX1, zero_mul, add_zero, ← hsX]
      _ = st b * b := by rw [add_mul, mul_assoc, hb3, mul_zero, add_zero]
  have hstar : st b + st X * e₃ + b + e₁ * X + st b * b = 0 := by
    have e := hU
    rw [hXX] at e
    calc st b + st X * e₃ + b + e₁ * X + st b * b = (st b + st X * e₃) + (b + e₁ * X) + st b * b := by abel
      _ = st X + X + st b * b := by rw [← hsX, ← hXb]
      _ = 0 := e
  have hYe : e₁ * X * e₃ = e₁ * X + st b := by
    have e := congrArg (· * e₃) hstar
    simp only [add_mul, zero_mul] at e
    rw [sb3, mul_assoc (st X), he33, hb3', mul_assoc (st b), hb3'] at e
    have key : e₁ * X * e₃ - (e₁ * X + st b) =
        (0 + st X * e₃ + b + e₁ * X * e₃ + st b * b) - (st b + st X * e₃ + b + e₁ * X + st b * b) := by abel
    rw [e, hstar, sub_zero] at key
    exact sub_eq_zero.mp key
  have hq : h * (st b * b) + h * (st b * b) = st b * b := by rw [← add_mul, hh, one_mul]
  refine ⟨b, e₁ * X + st b + h * (st b * b), ⟨hb1, hb3, hb3'⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [mul_add, mul_add, ← mul_assoc, h11, sb1, ← mul_assoc, ← hc e₁, mul_assoc, ← mul_assoc e₁, sb1]
  · rw [add_mul, add_mul, hYe, sb3, add_zero, mul_assoc h, mul_assoc (st b), hb3']
  · have e : st (e₁ * X + st b + h * (st b * b)) + (e₁ * X + st b + h * (st b * b)) = 0 := by
      simp only [map_add, hm, hs, hi, st_half hm hi hh hc]
      rw [← hc (st b * b)]
      calc st X * e₃ + b + h * (st b * b) + (e₁ * X + st b + h * (st b * b))
          = st b + st X * e₃ + b + e₁ * X + (h * (st b * b) + h * (st b * b)) := by abel
        _ = 0 := by rw [hq]; exact hstar
    exact eq_neg_of_add_eq_zero_left e
  · simp only [elt]
    conv_lhs => rw [hXb]
    abel

end

theorem compact_mod_subring (S : Type) [Ring S] [TopologicalSpace S] [IsTopologicalRing S]
    (st : S →+ S) (S₀ : Subring S) (e₁ e₃ h : S) (K : Set S) (hcont : Continuous st)
    (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (h0 : ∀ x ∈ S₀, st x ∈ S₀) (he : e₁ ∈ S₀) (hh0 : h ∈ S₀) (h11 : e₁ * e₁ = e₁)
    (hs : st e₁ = e₃) (h13 : e₁ * e₃ = 0) (h31 : e₃ * e₁ = 0) (hh : h + h = 1)
    (hc : ∀ x, h * x = x * h) (hK : IsCompact K) (hcov : ∀ x, ∃ y ∈ S₀, x - y ∈ K) :
    ∃ K' : Set Sˣ, IsCompact K' ∧ (∀ g ∈ K', (st (g : S) * (g : S) = 1 ∧ ((g : S) - 1) * e₁ = 0 ∧
      (1 - e₁) * ((g : S) - 1) * (1 - e₃) = 0)) ∧ ∀ g : Sˣ, (st (g : S) * (g : S) = 1 ∧
      ((g : S) - 1) * e₁ = 0 ∧ (1 - e₁) * ((g : S) - 1) * (1 - e₃) = 0) →
      ∃ γ : Sˣ, (st (γ : S) * (γ : S) = 1 ∧ ((γ : S) - 1) * e₁ = 0 ∧
      (1 - e₁) * ((γ : S) - 1) * (1 - e₃) = 0) ∧ (γ : S) ∈ S₀ ∧ ((γ⁻¹ : Sˣ) : S) ∈ S₀ ∧
      γ * g ∈ K' := by
  have he3 : st e₃ = e₁ := by rw [← hs, hi]
  have he33 : e₃ * e₃ = e₃ := by rw [← hs, ← hm, h11]
  have he3S : e₃ ∈ S₀ := hs ▸ h0 e₁ he
  obtain ⟨pb, hpb⟩ : ∃ f : S → S, ∀ x, f x = (1 - e₁ - e₃) * x * e₃ := ⟨_, fun _ => rfl⟩
  obtain ⟨pw, hpw⟩ : ∃ f : S → S, ∀ x, f x = e₁ * (h * (x - st x)) * e₃ := ⟨_, fun _ => rfl⟩
  have pb_sub : ∀ x y, pb (x - y) = pb x - pb y := fun x y => by
    simp only [hpb, mul_sub, sub_mul]
  have pw_sub : ∀ x y, pw (x - y) = pw x - pw y := fun x y => by
    simp only [hpw, map_sub, mul_sub, sub_mul]
    abel
  have hbx : ∀ x, e₁ * pb x = 0 ∧ e₃ * pb x = 0 ∧ pb x * e₃ = pb x := fun x => by
    refine ⟨?_, ?_, ?_⟩
    · simp only [hpb, ← mul_assoc, mul_sub, mul_one, h11, h13, sub_self, zero_mul]
    · simp only [hpb, ← mul_assoc, mul_sub, mul_one, h31, he33, sub_self, sub_zero, zero_mul]
    · simp only [hpb, mul_assoc, he33]
  have hwx : ∀ y, e₁ * pw y = pw y ∧ pw y * e₃ = pw y ∧ st (pw y) = -pw y := fun y => by
    refine ⟨?_, ?_, ?_⟩
    · simp only [hpw, ← mul_assoc, h11]
    · simp only [hpw, mul_assoc, he33]
    · simp only [hpw, hm, he3, hs, map_sub, hi, st_half hm hi hh hc]
      rw [← hc (st y - y)]
      noncomm_ring
  have pb_id : ∀ b, e₁ * b = 0 → e₃ * b = 0 → b * e₃ = b → pb b = b := fun b h1 h3 h3' => by
    simp only [hpb, sub_mul, one_mul, h1, h3, sub_zero, h3']
  have pw_id : ∀ w, e₁ * w = w → w * e₃ = w → st w = -w → pw w = w := fun w h1 h3 hs' => by
    rw [hpw, hs', sub_neg_eq_add, mul_add, ← add_mul, hh, one_mul, h1, h3]
  have pbS : ∀ x ∈ S₀, pb x ∈ S₀ := fun x hx => by
    rw [hpb]
    exact S₀.mul_mem (S₀.mul_mem (S₀.sub_mem (S₀.sub_mem S₀.one_mem he) he3S) hx) he3S
  have pwS : ∀ x ∈ S₀, pw x ∈ S₀ := fun x hx => by
    rw [hpw]
    exact S₀.mul_mem (S₀.mul_mem he (S₀.mul_mem hh0 (S₀.sub_mem hx (h0 x hx)))) he3S
  have pb_cont : Continuous pb := by
    rw [show pb = fun x => (1 - e₁ - e₃) * x * e₃ from funext hpb]
    exact (continuous_const.mul continuous_id).mul continuous_const
  have pw_cont : Continuous pw := by
    rw [show pw = fun x => e₁ * (h * (x - st x)) * e₃ from funext hpw]
    exact (continuous_const.mul (continuous_const.mul (continuous_id.sub hcont))).mul continuous_const
  have hE : ∀ {f g : S × S → S}, Continuous f → Continuous g →
      Continuous (fun p => elt st h (f p) (g p)) := by
    intro f g hf hg
    show Continuous (fun p => 1 - st (f p) + f p + (g p - h * (st (f p) * f p)))
    exact ((continuous_const.sub (hcont.comp hf)).add hf).add
      (hg.sub (continuous_const.mul ((hcont.comp hf).mul hf)))
  have eltS : ∀ x y, x ∈ S₀ → y ∈ S₀ → elt st h x y ∈ S₀ := fun x y hx hy =>
    S₀.add_mem (S₀.add_mem (S₀.sub_mem S₀.one_mem (h0 x hx)) hx)
      (S₀.sub_mem hy (S₀.mul_mem hh0 (S₀.mul_mem (h0 x hx) hx)))
  have hbneg : ∀ b, (e₁ * b = 0 ∧ e₃ * b = 0 ∧ b * e₃ = b) → (e₁ * -b = 0 ∧ e₃ * -b = 0 ∧ -b * e₃ = -b) :=
    fun b ⟨a1, a2, a3⟩ => ⟨by rw [mul_neg, a1, neg_zero], by rw [mul_neg, a2, neg_zero], by rw [neg_mul, a3]⟩
  have hwneg : ∀ w, (e₁ * w = w ∧ w * e₃ = w ∧ st w = -w) →
      (e₁ * -w = -w ∧ -w * e₃ = -w ∧ st (-w) = -(-w)) :=
    fun w ⟨a1, a2, a3⟩ => ⟨by rw [mul_neg, a1], by rw [neg_mul, a2], by rw [map_neg, a3]⟩
  have hQ : ∀ x y, (e₁ * x = 0 ∧ e₃ * x = 0 ∧ x * e₃ = x) → (e₁ * y = 0 ∧ e₃ * y = 0 ∧ y * e₃ = y) →
      e₁ * (st x * y - st y * x) = st x * y - st y * x ∧ (st x * y - st y * x) * e₃ = st x * y - st y * x ∧
        st (st x * y - st y * x) = -(st x * y - st y * x) := by
    intro x y hx hy
    have sx1 : e₁ * st x = st x := by rw [← he3, ← hm, hx.2.2]
    have sy1 : e₁ * st y = st y := by rw [← he3, ← hm, hy.2.2]
    refine ⟨?_, ?_, ?_⟩
    · rw [mul_sub, ← mul_assoc, ← mul_assoc, sx1, sy1]
    · rw [sub_mul, mul_assoc, mul_assoc, hy.2.2, hx.2.2]
    · rw [map_sub, hm, hm, hi, hi, neg_sub]
  obtain ⟨F, hF⟩ : ∃ F : S × S → Sˣ, ∀ p, (F p : S) = elt st h (pb p.1) (pw p.2) ∧
      (((F p)⁻¹ : Sˣ) : S) = elt st h (-pb p.1) (-pw p.2) :=
    ⟨fun p => ⟨elt st h (pb p.1) (pw p.2), elt st h (-pb p.1) (-pw p.2),
      elt_mul_neg hm hi hs h31 hh hc ⟨(hbx p.1).2.1, (hbx p.1).2.2⟩ ⟨(hwx p.2).1, (hwx p.2).2.1⟩,
      elt_neg_mul hm hi hs h31 hh hc ⟨(hbx p.1).2.1, (hbx p.1).2.2⟩ ⟨(hwx p.2).1, (hwx p.2).2.1⟩⟩,
      fun p => ⟨rfl, rfl⟩⟩
  have hFc : Continuous F := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · rw [show (Units.val ∘ F) = fun p => elt st h (pb p.1) (pw p.2) from funext fun p => (hF p).1]
      exact hE (pb_cont.comp continuous_fst) (pw_cont.comp continuous_snd)
    · rw [show (fun p => (((F p)⁻¹ : Sˣ) : S)) = fun p => elt st h (-pb p.1) (-pw p.2)
        from funext fun p => (hF p).2]
      exact hE (pb_cont.comp continuous_fst).neg (pw_cont.comp continuous_snd).neg
  refine ⟨F '' (K ×ˢ K), (hK.prod hK).image hFc, ?_, ?_⟩
  · rintro _ ⟨p, _, rfl⟩
    rw [(hF p).1]
    exact elt_cond hm hi hs h31 hh hc (hbx p.1) (hwx p.2)
  · intro g hg
    obtain ⟨b, w, hb, hw, hgeq⟩ := exists_elt hm hi h11 hs h31 hh hc hg.1 hg.2.1 hg.2.2
    obtain ⟨y₁, hy₁, hk₁⟩ := hcov b
    obtain ⟨q1, q3, qs⟩ := hQ b (-pb y₁) hb (hbneg _ (hbx y₁))
    have hw1 : e₁ * (w + h * (st b * -pb y₁ - st (-pb y₁) * b)) = w + h * (st b * -pb y₁ - st (-pb y₁) * b) := by
      rw [mul_add, hw.1, ← mul_assoc, ← hc e₁, mul_assoc, q1]
    have hw3 : (w + h * (st b * -pb y₁ - st (-pb y₁) * b)) * e₃ = w + h * (st b * -pb y₁ - st (-pb y₁) * b) := by
      rw [add_mul, hw.2.1, mul_assoc, q3]
    have hws : st (w + h * (st b * -pb y₁ - st (-pb y₁) * b)) = -(w + h * (st b * -pb y₁ - st (-pb y₁) * b)) := by
      rw [map_add, hm, st_half hm hi hh hc, hw.2.2, qs, ← hc, mul_neg, neg_add]
    obtain ⟨y₂, hy₂, hk₂⟩ := hcov (w + h * (st b * -pb y₁ - st (-pb y₁) * b))
    have hb0 := hbx y₁
    have hw0 := hwx y₂
    let γ : Sˣ := ⟨elt st h (-pb y₁) (-pw y₂), elt st h (pb y₁) (pw y₂),
      elt_neg_mul hm hi hs h31 hh hc ⟨hb0.2.1, hb0.2.2⟩ ⟨hw0.1, hw0.2.1⟩,
      elt_mul_neg hm hi hs h31 hh hc ⟨hb0.2.1, hb0.2.2⟩ ⟨hw0.1, hw0.2.1⟩⟩
    refine ⟨γ, ?_, ?_, ?_, ?_⟩
    · exact elt_cond hm hi hs h31 hh hc (hbneg _ hb0) (hwneg _ hw0)
    · exact eltS _ _ (S₀.neg_mem (pbS y₁ hy₁)) (S₀.neg_mem (pwS y₂ hy₂))
    · exact eltS _ _ (pbS y₁ hy₁) (pwS y₂ hy₂)
    · refine ⟨(b - y₁, w + h * (st b * -pb y₁ - st (-pb y₁) * b) - y₂), ⟨hk₁, hk₂⟩, ?_⟩
      apply Units.ext
      rw [Units.val_mul, (hF _).1]
      show elt st h (pb (b - y₁)) (pw (w + h * (st b * -pb y₁ - st (-pb y₁) * b) - y₂)) =
        elt st h (-pb y₁) (-pw y₂) * (g : S)
      rw [hgeq, elt_mul hm hi hs h31 hh hc ⟨(hbneg _ hb0).2.1, (hbneg _ hb0).2.2⟩ ⟨hb.2.1, hb.2.2⟩
        (hwneg _ hw0).2.1 hw.1]
      rw [pb_sub, pb_id b hb.1 hb.2.1 hb.2.2, pw_sub, pw_id _ hw1 hw3 hws]
      congr 1 <;> abel

end GlobalTheory.TwoStepUnipotent

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

def IsCAR (cp cm : Fin n → Fin n → Module.End ℂ W) : Prop :=
  ∀ i a j b : Fin n, cp i a * cp j b + cp j b * cp i a = 0 ∧ cm i a * cm j b + cm j b * cm i a = 0 ∧
    cm i a * cp j b + cp j b * cm i a = if i = j ∧ a = b then 1 else 0

def CommutesCAR (E cp cm : Fin n → Fin n → Module.End ℂ W) : Prop :=
  ∀ a b i j : Fin n, E a b * cp i j = cp i j * E a b ∧ E a b * cm i j = cm i j * E a b

def plusIdx (ε : Fin n → Bool) : Finset (Fin n) := univ.filter fun a => ε a = true

def minusIdx (ε : Fin n → Bool) : Finset (Fin n) := univ.filter fun a => ε a = false

def sgE (ε : Fin n → Bool) (cp cm : Fin n → Fin n → Module.End ℂ W) (a b : Fin n) : Module.End ℂ W :=
  if ε a = true ∧ ε b = true then ∑ x ∈ minusIdx ε, cp a x * cm b x
  else if ε a = false ∧ ε b = false then -∑ i ∈ plusIdx ε, cp i b * cm i a
  else 0

def diagE (ε : Fin n → Bool) (E cp cm : Fin n → Fin n → Module.End ℂ W) (a b : Fin n) : Module.End ℂ W :=
  E a b + sgE ε cp cm a b

def dOp (ε : Fin n → Bool) (E cp : Fin n → Fin n → Module.End ℂ W) : Module.End ℂ W :=
  ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, E a i * cp i a

def dOp' (ε : Fin n → Bool) (E cm : Fin n → Fin n → Module.End ℂ W) : Module.End ℂ W :=
  -∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, E i a * cm i a

def rhoHol (ε : Fin n → Bool) : Fin n → ℝ := fun a => if ε a then (qOf ε : ℝ) / 2 else -(pOf ε : ℝ) / 2

theorem car_bil_abs {R : Type*} [Ring R] (p1 m1 p2 m2 δ δ' : R) (h1 : m1 * p2 + p2 * m1 = δ)
    (h2 : m2 * p1 + p1 * m2 = δ') (hp : p1 * p2 + p2 * p1 = 0) (hm : m1 * m2 + m2 * m1 = 0) :
    p1 * m1 * (p2 * m2) - p2 * m2 * (p1 * m1) = p1 * δ * m2 - p2 * δ' * m1 := by
  have e1 : m1 * p2 = δ - p2 * m1 := eq_sub_of_add_eq h1
  have e2 : m2 * p1 = δ' - p1 * m2 := eq_sub_of_add_eq h2
  have e3 : p2 * p1 = -(p1 * p2) := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hp)
  have e4 : m2 * m1 = -(m1 * m2) := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hm)
  have e5 : p2 * (p1 * m2) * m1 = p1 * (p2 * m1) * m2 := by
    calc p2 * (p1 * m2) * m1 = p2 * p1 * (m2 * m1) := by simp only [mul_assoc]
      _ = p1 * p2 * (m1 * m2) := by rw [e3, e4, neg_mul_neg]
      _ = p1 * (p2 * m1) * m2 := by simp only [mul_assoc]
  calc p1 * m1 * (p2 * m2) - p2 * m2 * (p1 * m1)
        = p1 * (m1 * p2) * m2 - p2 * (m2 * p1) * m1 := by simp only [mul_assoc]
    _ = p1 * (δ - p2 * m1) * m2 - p2 * (δ' - p1 * m2) * m1 := by rw [e1, e2]
    _ = p1 * δ * m2 - p2 * δ' * m1 - (p1 * (p2 * m1) * m2 - p2 * (p1 * m2) * m1) := by
      simp only [mul_sub, sub_mul]; abel
    _ = p1 * δ * m2 - p2 * δ' * m1 := by rw [e5, sub_self, sub_zero]

theorem car_bil {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (i a j b k c l d : Fin n) :
    cp i a * cm j b * (cp k c * cm l d) - cp k c * cm l d * (cp i a * cm j b) =
      (if j = k ∧ b = c then cp i a * cm l d else 0) - (if l = i ∧ d = a then cp k c * cm j b else 0) := by
  rw [car_bil_abs _ _ _ _ _ _ (hC j b k c).2.2 (hC l d i a).2.2 (hC i a k c).1
    (hC j b l d).2.1]
  split_ifs <;> simp

theorem car_comm_sum {R ι κ : Type*} [Ring R] (s : Finset ι) (t : Finset κ) (A : ι → R) (B : κ → R) :
    (∑ x ∈ s, A x) * (∑ y ∈ t, B y) - (∑ y ∈ t, B y) * (∑ x ∈ s, A x) =
      ∑ x ∈ s, ∑ y ∈ t, (A x * B y - B y * A x) := by
  have h1 : (∑ x ∈ s, A x) * (∑ y ∈ t, B y) = ∑ x ∈ s, ∑ y ∈ t, A x * B y := by
    rw [Finset.sum_mul]; simp only [Finset.mul_sum]
  have h2 : (∑ y ∈ t, B y) * (∑ x ∈ s, A x) = ∑ x ∈ s, ∑ y ∈ t, B y * A x := by
    rw [Finset.sum_mul]; simp only [Finset.mul_sum]; exact Finset.sum_comm
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_sub_distrib]

private theorem eq_zero_of_eq_neg_of_module_complex {M : Type*} [AddCommGroup M] [Module ℂ M] {v : M}
    (h : v = -v) : v = 0 := by
  have h3 : (2 : ℂ) • v = 0 := by
    rw [two_smul]; exact eq_neg_iff_add_eq_zero.mp h
  calc v = (2 : ℂ)⁻¹ • ((2 : ℂ) • v) := by rw [smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    _ = 0 := by rw [h3, smul_zero]

theorem car_sum_sq_zero_of_anti {R ι : Type*} [Ring R] [Module ℂ R] (s : Finset ι) (F : ι → R)
    (h : ∀ x ∈ s, ∀ y ∈ s, F x * F y = -(F y * F x)) : (∑ x ∈ s, F x) * (∑ y ∈ s, F y) = 0 := by
  have e : (∑ x ∈ s, F x) * (∑ y ∈ s, F y) = ∑ x ∈ s, ∑ y ∈ s, F x * F y := by
    rw [Finset.sum_mul]; simp only [Finset.mul_sum]
  have e2 : ∑ x ∈ s, ∑ y ∈ s, F x * F y = -∑ x ∈ s, ∑ y ∈ s, F x * F y := by
    calc ∑ x ∈ s, ∑ y ∈ s, F x * F y = ∑ x ∈ s, ∑ y ∈ s, -(F y * F x) :=
          Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => h x hx y hy
      _ = ∑ y ∈ s, ∑ x ∈ s, -(F y * F x) := Finset.sum_comm
      _ = -∑ y ∈ s, ∑ x ∈ s, F y * F x := by simp only [Finset.sum_neg_distrib]
  rw [e]
  exact eq_zero_of_eq_neg_of_module_complex e2

theorem car_anti_abs {R : Type*} [Ring R] (A B c e : R) (hcB : c * B = B * c) (heA : e * A = A * e)
    (hAB : A * B = B * A) (hce : c * e = -(e * c)) : A * c * (B * e) = -(B * e * (A * c)) := by
  calc A * c * (B * e) = A * (c * B) * e := by simp only [mul_assoc]
    _ = A * (B * c) * e := by rw [hcB]
    _ = A * B * (c * e) := by simp only [mul_assoc]
    _ = B * A * -(e * c) := by rw [hAB, hce]
    _ = -(B * (A * e) * c) := by simp only [mul_neg, mul_assoc]
    _ = -(B * (e * A) * c) := by rw [heA]
    _ = -(B * e * (A * c)) := by simp only [mul_assoc]

private theorem mem_plusIdx_iff_eq_true {ε : Fin n → Bool} {a : Fin n} :
    a ∈ plusIdx ε ↔ ε a = true := by
  simp [plusIdx]

private theorem mem_minusIdx_iff_eq_false {ε : Fin n → Bool} {a : Fin n} :
    a ∈ minusIdx ε ↔ ε a = false := by
  simp [minusIdx]

private theorem sum_sum_eq_sum_diag_of_offdiag_eq_zero {M ι : Type*} [AddCommMonoid M] (s : Finset ι) (F : ι → ι → M)
    (hF : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → F x y = 0) : ∑ x ∈ s, ∑ y ∈ s, F x y = ∑ x ∈ s, F x x :=
  Finset.sum_congr rfl fun x hx =>
    Finset.sum_eq_single x (fun y hy hyx => hF x hx y hy (Ne.symm hyx)) (fun h => absurd hx h)

private theorem sum_sum_eq_apply_of_eq_zero_off_point {M ι κ : Type*} [AddCommMonoid M] (s : Finset ι) (t : Finset κ)
    (x0 : ι) (y0 : κ) (hx0 : x0 ∈ s) (hy0 : y0 ∈ t) (F : ι → κ → M)
    (hF : ∀ x ∈ s, ∀ y ∈ t, (x ≠ x0 ∨ y ≠ y0) → F x y = 0) :
    ∑ x ∈ s, ∑ y ∈ t, F x y = F x0 y0 := by
  rw [Finset.sum_eq_single x0]
  · exact Finset.sum_eq_single y0 (fun y hy hne => hF x0 hx0 y hy (Or.inr hne)) (fun h => absurd hy0 h)
  · exact fun x hx hne => Finset.sum_eq_zero fun y hy => hF x hx y hy (Or.inl hne)
  · exact fun h => absurd hx0 h

private theorem sgE_eq_sum_minusIdx_of_true (ε : Fin n → Bool) (cp cm : Fin n → Fin n → Module.End ℂ W)
    {a b : Fin n} (ha : ε a = true) (hb : ε b = true) :
    sgE ε cp cm a b = ∑ x ∈ minusIdx ε, cp a x * cm b x := by
  unfold sgE
  rw [if_pos (And.intro ha hb)]

private theorem sgE_eq_neg_sum_plusIdx_of_false (ε : Fin n → Bool) (cp cm : Fin n → Fin n → Module.End ℂ W)
    {a b : Fin n} (ha : ε a = false) (hb : ε b = false) :
    sgE ε cp cm a b = -∑ i ∈ plusIdx ε, cp i b * cm i a := by
  unfold sgE
  have h1 : ¬(ε a = true ∧ ε b = true) := by simp [ha]
  rw [if_neg h1, if_pos (And.intro ha hb)]

theorem sgE_comm {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (ε : Fin n → Bool)
    (a b c d : Fin n) (hab : ε a = ε b) (hcd : ε c = ε d) :
    sgE ε cp cm a b * sgE ε cp cm c d - sgE ε cp cm c d * sgE ε cp cm a b =
      (if b = c then sgE ε cp cm a d else 0) - (if d = a then sgE ε cp cm c b else 0) := by
  by_cases ha : ε a = true <;> by_cases hc : ε c = true
  · have hb : ε b = true := by rw [← hab]; exact ha
    have hd : ε d = true := by rw [← hcd]; exact hc
    rw [sgE_eq_sum_minusIdx_of_true ε cp cm ha hb, sgE_eq_sum_minusIdx_of_true ε cp cm hc hd,
      sgE_eq_sum_minusIdx_of_true ε cp cm ha hd, sgE_eq_sum_minusIdx_of_true ε cp cm hc hb]
    simp only [car_comm_sum, car_bil hC]
    refine (sum_sum_eq_sum_diag_of_offdiag_eq_zero _ _ ?_).trans ?_
    · intro x _ y _ hxy
      simp [hxy, Ne.symm hxy]
    · rcases eq_or_ne b c with h1 | h1 <;> rcases eq_or_ne d a with h2 | h2
      · subst h1; subst h2; simp [Finset.sum_sub_distrib]
      · subst h1; simp [h2]
      · subst h2; simp [h1]
      · simp [h1, h2]
  · have hc' : ε c = false := by simpa using hc
    have hb : ε b = true := by rw [← hab]; exact ha
    have hd : ε d = false := by rw [← hcd]; exact hc'
    have hbc : b ≠ c := fun h => by simp [h, hc'] at hb
    have hda : d ≠ a := fun h => by simp [h, ha] at hd
    rw [if_neg hbc, if_neg hda, sub_zero, sgE_eq_sum_minusIdx_of_true ε cp cm ha hb,
      sgE_eq_neg_sum_plusIdx_of_false ε cp cm hc' hd]
    have e1 : ∑ x ∈ minusIdx ε, ∑ i ∈ plusIdx ε,
        (if b = i ∧ x = d then cp a x * cm i c else 0) = cp a d * cm b c := by
      refine (sum_sum_eq_apply_of_eq_zero_off_point _ _ d b (mem_minusIdx_iff_eq_false.mpr hd) (mem_plusIdx_iff_eq_true.mpr hb) _ ?_).trans ?_
      · intro x _ i _ hne
        rw [if_neg]
        rintro ⟨rfl, rfl⟩
        simp at hne
      · simp
    have e2 : ∑ x ∈ minusIdx ε, ∑ i ∈ plusIdx ε,
        (if i = a ∧ c = x then cp i d * cm b x else 0) = cp a d * cm b c := by
      refine (sum_sum_eq_apply_of_eq_zero_off_point _ _ c a (mem_minusIdx_iff_eq_false.mpr hc') (mem_plusIdx_iff_eq_true.mpr ha) _ ?_).trans ?_
      · intro x _ i _ hne
        rw [if_neg]
        rintro ⟨rfl, rfl⟩
        simp at hne
      · simp
    have key : (∑ x ∈ minusIdx ε, cp a x * cm b x) * (∑ i ∈ plusIdx ε, cp i d * cm i c) -
        (∑ i ∈ plusIdx ε, cp i d * cm i c) * (∑ x ∈ minusIdx ε, cp a x * cm b x) = 0 := by
      simp only [car_comm_sum, car_bil hC, Finset.sum_sub_distrib, e1, e2, sub_self]
    rw [mul_neg, neg_mul, neg_sub_neg, ← neg_sub, key, neg_zero]
  · have ha' : ε a = false := by simpa using ha
    have hb : ε b = false := by rw [← hab]; exact ha'
    have hd : ε d = true := by rw [← hcd]; exact hc
    have hbc : b ≠ c := fun h => by simp [h, hc] at hb
    have hda : d ≠ a := fun h => by simp [h, ha'] at hd
    rw [if_neg hbc, if_neg hda, sub_zero, sgE_eq_neg_sum_plusIdx_of_false ε cp cm ha' hb,
      sgE_eq_sum_minusIdx_of_true ε cp cm hc hd]
    have e1 : ∑ i ∈ plusIdx ε, ∑ y ∈ minusIdx ε,
        (if i = c ∧ a = y then cp i b * cm d y else 0) = cp c b * cm d a := by
      refine (sum_sum_eq_apply_of_eq_zero_off_point _ _ c a (mem_plusIdx_iff_eq_true.mpr hc) (mem_minusIdx_iff_eq_false.mpr ha') _ ?_).trans ?_
      · intro i _ y _ hne
        rw [if_neg]
        rintro ⟨rfl, rfl⟩
        simp at hne
      · simp
    have e2 : ∑ i ∈ plusIdx ε, ∑ y ∈ minusIdx ε,
        (if d = i ∧ y = b then cp c y * cm i a else 0) = cp c b * cm d a := by
      refine (sum_sum_eq_apply_of_eq_zero_off_point _ _ d b (mem_plusIdx_iff_eq_true.mpr hd) (mem_minusIdx_iff_eq_false.mpr hb) _ ?_).trans ?_
      · intro i _ y _ hne
        rw [if_neg]
        rintro ⟨rfl, rfl⟩
        simp at hne
      · simp
    have key : (∑ i ∈ plusIdx ε, cp i b * cm i a) * (∑ y ∈ minusIdx ε, cp c y * cm d y) -
        (∑ y ∈ minusIdx ε, cp c y * cm d y) * (∑ i ∈ plusIdx ε, cp i b * cm i a) = 0 := by
      simp only [car_comm_sum, car_bil hC, Finset.sum_sub_distrib, e1, e2, sub_self]
    rw [neg_mul, mul_neg, neg_sub_neg, ← neg_sub, key, neg_zero]
  · have ha' : ε a = false := by simpa using ha
    have hc' : ε c = false := by simpa using hc
    have hb : ε b = false := by rw [← hab]; exact ha'
    have hd : ε d = false := by rw [← hcd]; exact hc'
    rw [sgE_eq_neg_sum_plusIdx_of_false ε cp cm ha' hb, sgE_eq_neg_sum_plusIdx_of_false ε cp cm hc' hd,
      sgE_eq_neg_sum_plusIdx_of_false ε cp cm ha' hd, sgE_eq_neg_sum_plusIdx_of_false ε cp cm hc' hb, neg_mul_neg, neg_mul_neg]
    simp only [car_comm_sum, car_bil hC]
    refine (sum_sum_eq_sum_diag_of_offdiag_eq_zero _ _ ?_).trans ?_
    · intro x _ y _ hxy
      simp [hxy, Ne.symm hxy]
    · rcases eq_or_ne b c with h1 | h1 <;> rcases eq_or_ne d a with h2 | h2
      · subst h1; subst h2; simp [Finset.sum_sub_distrib]; try abel
      · subst h1; simp [h2, Ne.symm h2]; try abel
      · subst h2; simp [h1, Ne.symm h1]; try abel
      · simp [h1, Ne.symm h1, h2, Ne.symm h2]

theorem dOp_sq {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) : dOp ε E cp * dOp ε E cp = 0 := by
  have hsum : dOp ε E cp =
      ∑ p ∈ plusIdx ε ×ˢ minusIdx ε, E p.2 p.1 * cp p.1 p.2 := by
    simp only [dOp, Finset.sum_product]
  rw [hsum]
  apply car_sum_sq_zero_of_anti
  intro x hx y hy
  simp only [Finset.mem_product, mem_plusIdx_iff_eq_true, mem_minusIdx_iff_eq_false] at hx hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have n1 : x.1 ≠ y.2 := fun h => by simp [h, hy2] at hx1
  have n2 : y.1 ≠ x.2 := fun h => by simp [h, hx2] at hy1
  have hAB : E x.2 x.1 * E y.2 y.1 = E y.2 y.1 * E x.2 x.1 := by
    have h := hE x.2 x.1 y.2 y.1
    rw [if_neg n1, if_neg n2, sub_zero] at h
    exact sub_eq_zero.mp h
  exact car_anti_abs _ _ _ _ ((hEC y.2 y.1 x.1 x.2).1).symm ((hEC x.2 x.1 y.1 y.2).1).symm hAB
    (eq_neg_iff_add_eq_zero.mpr (hC x.1 x.2 y.1 y.2).1)

theorem dOp'_sq {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) : dOp' ε E cm * dOp' ε E cm = 0 := by
  have hsum : dOp' ε E cm =
      -∑ p ∈ plusIdx ε ×ˢ minusIdx ε, E p.1 p.2 * cm p.1 p.2 := by
    simp only [dOp', Finset.sum_product]
  rw [hsum, neg_mul_neg]
  apply car_sum_sq_zero_of_anti
  intro x hx y hy
  simp only [Finset.mem_product, mem_plusIdx_iff_eq_true, mem_minusIdx_iff_eq_false] at hx hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have n1 : x.2 ≠ y.1 := fun h => by simp [h, hy1] at hx2
  have n2 : y.2 ≠ x.1 := fun h => by simp [h, hx1] at hy2
  have hAB : E x.1 x.2 * E y.1 y.2 = E y.1 y.2 * E x.1 x.2 := by
    have h := hE x.1 x.2 y.1 y.2
    rw [if_neg n1, if_neg n2, sub_zero] at h
    exact sub_eq_zero.mp h
  exact car_anti_abs _ _ _ _ ((hEC y.1 y.2 x.1 x.2).2).symm ((hEC x.1 x.2 y.1 y.2).2).symm hAB
    (eq_neg_iff_add_eq_zero.mpr (hC x.1 x.2 y.1 y.2).2.1)

end ReciprocityTheory.ChartRestriction.DS

import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit

open PositivityTheory.RgEis

section Gen

variable {α κ β : Type} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] {R : Type} [CommRing R]

def Pm (R : Type) [CommRing R] (e : κ → α) : Matrix α κ R := (1 : Matrix α α R).submatrix id e

open Classical in

def Dm (R : Type) [CommRing R] (e : κ → α) : Matrix α α R :=
  Matrix.diagonal fun a => if a ∈ Set.range e then 0 else 1

def jM (e : κ → α) (m : Matrix κ κ R) : Matrix α α R := Pm R e * m * (Pm R e)ᵀ + Dm R e

theorem Pm_apply (e : κ → α) (a : α) (x : κ) : Pm R e a x = if a = e x then 1 else 0 := by
  simp [Pm, Matrix.one_apply]

theorem Pmt_mul [Fintype β] (e : κ → α) (g : Matrix α β R) (x : κ) (b : β) :
    ((Pm R e)ᵀ * g) x b = g (e x) b := by
  simp [Matrix.mul_apply, Pm_apply]

theorem mul_Pm [Fintype β] (e : κ → α) (g : Matrix β α R) (b : β) (x : κ) :
    (g * Pm R e) b x = g b (e x) := by
  simp [Matrix.mul_apply, Pm_apply]

theorem Dm_apply (e : κ → α) (a b : α) :
    Dm R e a b = if a = b ∧ a ∉ Set.range e then 1 else 0 := by
  classical
  unfold Dm
  by_cases h : a = b
  · subst h
    rw [Matrix.diagonal_apply_eq]
    by_cases h2 : a ∈ Set.range e
    · rw [if_pos h2, if_neg fun hh => hh.2 h2]
    · rw [if_neg h2, if_pos ⟨rfl, h2⟩]
  · rw [Matrix.diagonal_apply_ne _ h, if_neg fun hh => h hh.1]

theorem Pmt_Pm {e : κ → α} (he : Function.Injective e) : (Pm R e)ᵀ * Pm R e = 1 := by
  ext x y
  rw [Pmt_mul, Pm_apply, Matrix.one_apply]
  simp [he.eq_iff]

theorem Pmt_Dm (e : κ → α) : (Pm R e)ᵀ * Dm R e = 0 := by
  ext x a
  rw [Pmt_mul, Dm_apply, if_neg fun hh => hh.2 ⟨x, rfl⟩]
  rfl

theorem Dm_Pm (e : κ → α) : Dm R e * Pm R e = 0 := by
  ext a x
  rw [mul_Pm, Dm_apply, if_neg fun hh => hh.2 ⟨x, hh.1.symm⟩]
  rfl

theorem Dm_Dm (e : κ → α) : Dm R e * Dm R e = Dm R e := by
  classical
  unfold Dm
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases h : a ∈ Set.range e <;> simp [h]

theorem Pm_Pmt_add {e : κ → α} (he : Function.Injective e) :
    Pm R e * (Pm R e)ᵀ + Dm R e = 1 := by
  ext a b
  rw [Matrix.add_apply, Dm_apply, Matrix.one_apply]
  by_cases h : a ∈ Set.range e
  · obtain ⟨x, rfl⟩ := h
    have : (Pm R e * (Pm R e)ᵀ) (e x) b = if e x = b then 1 else 0 := by
      rw [Matrix.mul_apply, Finset.sum_eq_single x]
      · simp [Pm_apply, eq_comm]
      · intro y _ hy
        simp [Pm_apply, he.eq_iff, Ne.symm hy]
      · simp
    rw [this]
    simp
  · have : (Pm R e * (Pm R e)ᵀ) a b = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun y _ => ?_
      have : a ≠ e y := fun hh => h ⟨y, hh.symm⟩
      simp [Pm_apply, this]
    rw [this]
    simp [h]

theorem jM_one {e : κ → α} (he : Function.Injective e) : jM e (1 : Matrix κ κ R) = 1 := by
  simp [jM, Pm_Pmt_add he]

theorem jM_mul {e : κ → α} (he : Function.Injective e) (m n : Matrix κ κ R) :
    jM e (m * n) = jM e m * jM e n := by
  unfold jM
  have h1 : Pm R e * m * (Pm R e)ᵀ * (Pm R e * n * (Pm R e)ᵀ) = Pm R e * (m * n) * (Pm R e)ᵀ := by
    calc _ = Pm R e * m * ((Pm R e)ᵀ * Pm R e) * n * (Pm R e)ᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [Pmt_Pm he]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have h2 : Pm R e * m * (Pm R e)ᵀ * Dm R e = 0 := by
    rw [Matrix.mul_assoc, Pmt_Dm, Matrix.mul_zero]
  have h3 : Dm R e * (Pm R e * n * (Pm R e)ᵀ) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Dm_Pm]; simp
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h1, h2, h3, Dm_Dm]
  simp

theorem sub_eq (e : κ → α) (g : Matrix α α R) : g.submatrix e e = (Pm R e)ᵀ * g * Pm R e := by
  ext x y
  rw [mul_Pm, Pmt_mul]
  rfl

theorem sub_jM {e : κ → α} (he : Function.Injective e) (m : Matrix κ κ R) :
    (jM e m).submatrix e e = m := by
  rw [sub_eq]
  unfold jM
  have : (Pm R e)ᵀ * (Pm R e * m * (Pm R e)ᵀ + Dm R e) * Pm R e =
      ((Pm R e)ᵀ * Pm R e) * m * ((Pm R e)ᵀ * Pm R e) + (Pm R e)ᵀ * Dm R e * Pm R e := by
    rw [Matrix.mul_add, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
  rw [this, Pmt_Pm he, Pmt_Dm]
  simp

theorem jM_off_left (e : κ → α) (m : Matrix κ κ R) (a b : α) (h : a ∉ Set.range e) :
    jM e m a b = (1 : Matrix α α R) a b := by
  have h0 : ∀ y, Pm R e a y = 0 := fun y => by
    have : a ≠ e y := fun hh => h ⟨y, hh.symm⟩
    simp [Pm_apply, this]
  unfold jM
  rw [Matrix.add_apply, Matrix.mul_assoc, Matrix.mul_apply, Dm_apply, Matrix.one_apply]
  simp [h0, h]

theorem jM_off_right (e : κ → α) (m : Matrix κ κ R) (a b : α) (h : b ∉ Set.range e) :
    jM e m a b = (1 : Matrix α α R) a b := by
  have h0 : ∀ y, Pm R e b y = 0 := fun y => by
    have : b ≠ e y := fun hh => h ⟨y, hh.symm⟩
    simp [Pm_apply, this]
  unfold jM
  rw [Matrix.add_apply, Matrix.mul_apply, Dm_apply, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab
    simp [h0, h]
  · simp [h0, hab]

theorem jM_apply {e : κ → α} (he : Function.Injective e) (m : Matrix κ κ R) (x y : κ) :
    jM e m (e x) (e y) = m x y := by
  have := congrFun (congrFun (sub_jM he m) x) y
  simpa using this

theorem Pm_map {S : Type} [CommRing S] (f : R →+* S) (e : κ → α) : (Pm R e).map f = Pm S e := by
  ext a x
  simp only [Matrix.map_apply, Pm_apply]
  split_ifs <;> simp

theorem Dm_map {S : Type} [CommRing S] (f : R →+* S) (e : κ → α) : (Dm R e).map f = Dm S e := by
  ext a b
  simp only [Matrix.map_apply, Dm_apply]
  split_ifs <;> simp

theorem jM_map {S : Type} [CommRing S] (f : R →+* S) (e : κ → α) (m : Matrix κ κ R) :
    (jM e m).map f = jM e (m.map f) := by
  unfold jM
  rw [Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_mul, Pm_map, Dm_map, Matrix.transpose_map, Pm_map]

theorem Dm_transpose (e : κ → α) : (Dm R e)ᵀ = Dm R e := by
  classical
  unfold Dm
  simp

theorem jM_transpose (e : κ → α) (m : Matrix κ κ R) : (jM e m)ᵀ = jM e mᵀ := by
  unfold jM
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Dm_transpose,
    Matrix.mul_assoc]

theorem jM_star (e : κ → α) (m : Matrix κ κ ℂ) : star (jM e m) = jM e (star m) := by
  have hs : ∀ {n : Type} [Fintype n] (x : Matrix n n ℂ), star x = (x.map (starRingEnd ℂ))ᵀ := fun x => by
    ext a b
    rfl
  rw [hs, hs, jM_map, jM_transpose]

def jH (e : κ → α) (he : Function.Injective e) : Matrix κ κ R →* Matrix α α R where
  toFun := jM e
  map_one' := jM_one he
  map_mul' := jM_mul he

theorem sub_mul_of (e : κ → α) (he : Function.Injective e) (a b : Matrix α α R)
    (h : ∀ x y, ∀ m, m ∉ Set.range e → a (e x) m * b m (e y) = 0) :
    (a * b).submatrix e e = a.submatrix e e * b.submatrix e e := by
  ext x y
  rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply]
  symm
  exact Fintype.sum_of_injective e he _ _ (fun m hm => h x y m hm) (fun _ => rfl)

end Gen

section Split

variable {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R] {s : Set ι}

def emb (s : Set ι) : (↥sᶜ ⊕ ↥sᶜ) → ι ⊕ ι := Sum.map Subtype.val Subtype.val

theorem emb_inj : Function.Injective (emb s) :=
  Sum.map_injective.2 ⟨Subtype.val_injective, Subtype.val_injective⟩

theorem inl_mem_range (i : ι) : Sum.inl i ∈ Set.range (emb s) ↔ i ∉ s := by
  constructor
  · rintro ⟨x | x, h⟩
    · have : x.1 = i := Sum.inl_injective h
      exact this ▸ x.2
    · cases h
  · exact fun h => ⟨Sum.inl ⟨i, h⟩, rfl⟩

theorem inr_mem_range (i : ι) : Sum.inr i ∈ Set.range (emb s) ↔ i ∉ s := by
  constructor
  · rintro ⟨x | x, h⟩
    · cases h
    · have : x.1 = i := Sum.inr_injective h
      exact this ▸ x.2
  · exact fun h => ⟨Sum.inr ⟨i, h⟩, rfl⟩

theorem not_range_cases {m : ι ⊕ ι} (h : m ∉ Set.range (emb s)) :
    (∃ i ∈ s, m = Sum.inl i) ∨ ∃ i ∈ s, m = Sum.inr i := by
  rcases m with i | i
  · exact Or.inl ⟨i, by_contra fun hi => h ((inl_mem_range i).2 hi), rfl⟩
  · exact Or.inr ⟨i, by_contra fun hi => h ((inr_mem_range i).2 hi), rfl⟩

theorem emb_not_inl (x : ↥sᶜ ⊕ ↥sᶜ) : emb s x ∉ (Sum.inl '' s : Set (ι ⊕ ι)) := by
  rintro ⟨i, hi, h⟩
  exact (inl_mem_range i).1 ⟨x, h.symm⟩ hi

theorem emb_not_inr (x : ↥sᶜ ⊕ ↥sᶜ) : emb s x ∉ (Sum.inr '' s : Set (ι ⊕ ι)) := by
  rintro ⟨i, hi, h⟩
  exact (inr_mem_range i).1 ⟨x, h.symm⟩ hi

theorem J_mul_inl {β : Type} (ε : ℤˣ) (b : Matrix (ι ⊕ ι) β R) (i : ι) (c : β) :
    (Ad.J R ε ι * b) (Sum.inl i) c = b (Sum.inr i) c := by
  simp [Ad.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem J_mul_inr {β : Type} (ε : ℤˣ) (b : Matrix (ι ⊕ ι) β R) (i : ι) (c : β) :
    (Ad.J R ε ι * b) (Sum.inr i) c = ((ε : ℤ) : R) * b (Sum.inl i) c := by
  simp [Ad.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem mul_J_inl {β : Type} [Fintype β] (ε : ℤˣ) (b : Matrix β (ι ⊕ ι) R) (a : β) (j : ι) :
    (b * Ad.J R ε ι) a (Sum.inl j) = ((ε : ℤ) : R) * b a (Sum.inr j) := by
  simp [Ad.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, mul_comm]

theorem mul_J_inr {β : Type} [Fintype β] (ε : ℤˣ) (b : Matrix β (ι ⊕ ι) R) (a : β) (j : ι) :
    (b * Ad.J R ε ι) a (Sum.inr j) = b a (Sum.inl j) := by
  simp [Ad.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem J_off (ε : ℤˣ) {m : ι ⊕ ι} (h : m ∉ Set.range (emb s))
    (y : ↥sᶜ ⊕ ↥sᶜ) : Ad.J R ε ι m (emb s y) = 0 := by
  rcases not_range_cases h with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;> rcases y with y | y <;>
    have hne : i ≠ y.1 := fun h => y.2 (h ▸ hi)
  all_goals simp [Ad.J, emb, Matrix.one_apply, hne]

section Comp

variable [Fintype ↥sᶜ] [DecidableEq ↥sᶜ]

theorem sub_J (ε : ℤˣ) : (Ad.J R ε ι).submatrix (emb s) (emb s) = Ad.J R ε ↥sᶜ := by
  ext (a | a) (b | b) <;> simp [Ad.J, emb, Matrix.one_apply, Subtype.ext_iff]

theorem J_Pm (ε : ℤˣ) : Ad.J R ε ι * Pm R (emb s) = Pm R (emb s) * Ad.J R ε ↥sᶜ := by
  ext (a | a) (b | b)
  · rw [J_mul_inl, mul_J_inl, Pm_apply, Pm_apply]; simp [emb]
  · rw [J_mul_inl, mul_J_inr, Pm_apply, Pm_apply]; simp [emb]
  · rw [J_mul_inr, mul_J_inl, Pm_apply, Pm_apply]; simp [emb]
  · rw [J_mul_inr, mul_J_inr, Pm_apply, Pm_apply]; simp [emb]

theorem Pmt_J (ε : ℤˣ) : (Pm R (emb s))ᵀ * Ad.J R ε ι = Ad.J R ε ↥sᶜ * (Pm R (emb s))ᵀ := by
  ext (a | a) (b | b)
  · rw [Pmt_mul, J_mul_inl, Matrix.transpose_apply, Pm_apply]; simp [Ad.J, emb]
  · rw [Pmt_mul, J_mul_inl, Matrix.transpose_apply, Pm_apply]
    simp [Ad.J, emb, Matrix.one_apply, eq_comm]
  · rw [Pmt_mul, J_mul_inr, Matrix.transpose_apply, Pm_apply]
    simp [Ad.J, emb, Matrix.one_apply, eq_comm]
  · rw [Pmt_mul, J_mul_inr, Matrix.transpose_apply, Pm_apply]; simp [Ad.J, emb]

theorem J_Dm (ε : ℤˣ) : Ad.J R ε ι * Dm R (emb s) = Dm R (emb s) * Ad.J R ε ι := by
  have hd : ∀ a b : ι, Dm R (emb s) (Sum.inl a) (Sum.inl b) = Dm R (emb s) (Sum.inr a) (Sum.inr b) := fun a b => by
    rw [Dm_apply, Dm_apply]
    refine if_congr ?_ rfl rfl
    rw [inl_mem_range, inr_mem_range, Sum.inl.injEq, Sum.inr.injEq]
  ext (a | a) (b | b)
  · rw [J_mul_inl, mul_J_inl, Dm_apply, Dm_apply]; simp
  · rw [J_mul_inl, mul_J_inr, hd]
  · rw [J_mul_inr, mul_J_inl, hd]
  · rw [J_mul_inr, mul_J_inr, Dm_apply, Dm_apply]; simp

theorem jM_unitary (ε : ℤˣ) (x y : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) R)
    (h : x * Ad.J R ε ↥sᶜ * y = Ad.J R ε ↥sᶜ) :
    jM (emb s) x * Ad.J R ε ι * jM (emb s) y = Ad.J R ε ι := by
  unfold jM
  set p := Pm R (emb s)
  set D := Dm R (emb s)
  have hp : pᵀ * p = 1 := Pmt_Pm emb_inj
  have hc : p * pᵀ + D = 1 := Pm_Pmt_add emb_inj
  have h1 : pᵀ * D = 0 := Pmt_Dm _
  have h2 : D * p = 0 := Dm_Pm _
  have h3 : D * D = D := Dm_Dm _
  have h4 : Ad.J R ε ι * p = p * Ad.J R ε ↥sᶜ := J_Pm ε
  have h5 : pᵀ * Ad.J R ε ι = Ad.J R ε ↥sᶜ * pᵀ := Pmt_J ε
  have h6 : Ad.J R ε ι * D = D * Ad.J R ε ι := J_Dm ε
  have e1 : (p * x * pᵀ + D) * Ad.J R ε ι = p * x * Ad.J R ε ↥sᶜ * pᵀ + D * Ad.J R ε ι := by
    rw [Matrix.add_mul, Matrix.mul_assoc (p * x), h5]
    simp only [Matrix.mul_assoc]
  have e2 : p * x * Ad.J R ε ↥sᶜ * pᵀ * (p * y * pᵀ) = Ad.J R ε ι * (p * pᵀ) := by
    calc _ = p * x * Ad.J R ε ↥sᶜ * (pᵀ * p) * y * pᵀ := by simp only [Matrix.mul_assoc]
      _ = p * (x * Ad.J R ε ↥sᶜ * y) * pᵀ := by rw [hp]; simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = _ := by rw [h, ← Matrix.mul_assoc, ← h4]
  have e3 : p * x * Ad.J R ε ↥sᶜ * pᵀ * D = 0 := by
    rw [Matrix.mul_assoc, h1, Matrix.mul_zero]
  have e4 : D * Ad.J R ε ι * (p * y * pᵀ) = 0 := by
    calc _ = D * (Ad.J R ε ι * p) * y * pᵀ := by simp only [Matrix.mul_assoc]
      _ = (D * p) * Ad.J R ε ↥sᶜ * y * pᵀ := by rw [h4]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h2]; simp
  have e5 : D * Ad.J R ε ι * D = Ad.J R ε ι * D := by
    rw [← h6, Matrix.mul_assoc, h3]
  rw [e1, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e2, e3, e4, e5, add_zero, zero_add, ← Matrix.mul_add, hc,
    Matrix.mul_one]

end Comp

structure Tri (s : Set ι) (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) : Prop where
  col : ∀ r, r ∉ (Sum.inl '' s : Set (ι ⊕ ι)) → ∀ i ∈ s, g r (Sum.inl i) = 0
  row : ∀ i ∈ s, ∀ c, c ∉ (Sum.inr '' s : Set (ι ⊕ ι)) → g (Sum.inr i) c = 0

section Comp2

variable [Fintype ↥sᶜ] [DecidableEq ↥sᶜ]

theorem Tri.sub_mul {a b : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (ha : Tri s a) (hb : Tri s b) :
    (a * b).submatrix (emb s) (emb s) = a.submatrix (emb s) (emb s) * b.submatrix (emb s) (emb s) := by
  refine sub_mul_of _ emb_inj a b fun x y m hm => ?_
  rcases not_range_cases hm with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · rw [ha.col _ (emb_not_inl x) i hi, zero_mul]
  · rw [hb.row i hi _ (emb_not_inr y), mul_zero]

theorem Tri.sub_unitary (ε : ℤˣ) {a b : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (ha : Tri s a) (hb : Tri s b) :
    (aᵀ * Ad.J R ε ι * b).submatrix (emb s) (emb s) =
      (a.submatrix (emb s) (emb s))ᵀ * Ad.J R ε ↥sᶜ * b.submatrix (emb s) (emb s) := by
  rw [sub_mul_of _ emb_inj (aᵀ * Ad.J R ε ι) b, sub_mul_of _ emb_inj aᵀ (Ad.J R ε ι), sub_J]
  · rfl
  · intro x y m hm
    rw [J_off ε hm, mul_zero]
  · intro x y m hm
    rcases not_range_cases hm with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · rw [mul_J_inl, Matrix.transpose_apply, ha.row i hi _ (emb_not_inr x)]
      simp
    · rw [hb.row i hi _ (emb_not_inr y), mul_zero]

end Comp2

theorem row_of_stab (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (ε : ℤˣ) (g : GL (ι ⊕ ι) R)
    (hJ : (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * Ad.J R ε ι * (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map σ = Ad.J R ε ι)
    (hc : ∀ r, r ∉ (Sum.inl '' s : Set (ι ⊕ ι)) → ∀ c ∈ (Sum.inl '' s : Set (ι ⊕ ι)),
      ((g⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) r c = 0) :
    ∀ i ∈ s, ∀ c, c ∉ (Sum.inr '' s : Set (ι ⊕ ι)) → (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr i) c = 0 := by
  intro i hi c hcs
  have h0 : ((g⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have h1 : Ad.J R ε ι * (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map σ =
      ((g⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * Ad.J R ε ι := by
    conv_rhs => rw [← hJ]
    simp only [← Matrix.mul_assoc]
    rw [h0, Matrix.one_mul]
  have h2 := congrFun (congrFun h1 (Sum.inl i)) c
  rw [J_mul_inl, Matrix.map_apply] at h2
  have h3 : σ ((g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr i) c) = 0 := by
    rw [h2]
    rcases c with j | j
    · rw [mul_J_inl, Matrix.transpose_apply, hc _ (by rintro ⟨_, _, h⟩; cases h) _ ⟨i, hi, rfl⟩, mul_zero]
    · have hj : j ∉ s := fun h => hcs ⟨j, h, rfl⟩
      rw [mul_J_inr, Matrix.transpose_apply]
      refine hc _ ?_ _ ⟨i, hi, rfl⟩
      rintro ⟨k, hk, h⟩
      exact hj (Sum.inl_injective h ▸ hk)
  rw [← hσ ((g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr i) c), h3, map_zero]

end Split

section Groups

variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι}

theorem tri_mem (A : Ad E R) (hσ : ∀ x, A.σ (A.σ x) = x) (ε : ℤˣ) (g : GL (ι ⊕ ι) R) (h1 : g ∈ A.uSub ε ι)
    (h2 : g ∈ stab R (Sum.inl '' s : Set (ι ⊕ ι))) : Tri s (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) where
  col := fun r hr i hi => (h2 r hr _ ⟨i, hi, rfl⟩).1
  row := row_of_stab A.σ hσ ε g h1 fun r hr c hc => (h2 r hr c hc).2

variable [Fintype ↥sᶜ] [DecidableEq ↥sᶜ]

def piG {F : Type} [CommRing F] (g : GL (ι ⊕ ι) F) (h : Tri s (g : Matrix (ι ⊕ ι) (ι ⊕ ι) F))
    (h' : Tri s ((g⁻¹ : GL (ι ⊕ ι) F) : Matrix (ι ⊕ ι) (ι ⊕ ι) F)) : GL (↥sᶜ ⊕ ↥sᶜ) F where
  val := (g : Matrix (ι ⊕ ι) (ι ⊕ ι) F).submatrix (emb s) (emb s)
  inv := ((g⁻¹ : GL (ι ⊕ ι) F) : Matrix (ι ⊕ ι) (ι ⊕ ι) F).submatrix (emb s) (emb s)
  val_inv := by rw [← h.sub_mul h', Units.mul_inv, Matrix.submatrix_one _ emb_inj]
  inv_val := by rw [← h'.sub_mul h, Units.inv_mul, Matrix.submatrix_one _ emb_inj]

variable (A : Ad E R) (ε : ℤˣ)

theorem q_stab (q : A.uQ ε s) : (q : A.U ε ι).1 ∈ stab R (Sum.inl '' s : Set (ι ⊕ ι)) :=
  Subgroup.mem_subgroupOf.1 q.2

theorem q_tri (hσ : ∀ x, A.σ (A.σ x) = x) (q : A.uQ ε s) :
    Tri s ((q : A.U ε ι).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
  tri_mem A hσ ε _ (q : A.U ε ι).2 (q_stab A ε q)

theorem q_tri' (hσ : ∀ x, A.σ (A.σ x) = x) (q : A.uQ ε s) :
    Tri s ((((q : A.U ε ι).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
  tri_mem A hσ ε _ ((A.uSub ε ι).inv_mem (q : A.U ε ι).2) ((stab R _).inv_mem (q_stab A ε q))

def piQ (hσ : ∀ x, A.σ (A.σ x) = x) : A.uQ ε s →* A.U ε ↥sᶜ where
  toFun q := ⟨piG (q : A.U ε ι).1 (q_tri A ε hσ q) (q_tri' A ε hσ q), by
    have h : ((q : A.U ε ι).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * Ad.J R ε ι *
        ((q : A.U ε ι).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ = Ad.J R ε ι := (q : A.U ε ι).2
    have h2 := (q_tri A ε hσ q).sub_unitary ε (b := ((q : A.U ε ι).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ)
      ⟨fun r hr i hi => by rw [Matrix.map_apply, (q_tri A ε hσ q).col r hr i hi, map_zero],
        fun i hi c hc => by rw [Matrix.map_apply, (q_tri A ε hσ q).row i hi c hc, map_zero]⟩
    rw [h, sub_J] at h2
    exact h2.symm⟩
  map_one' := Subtype.ext (Units.ext (Matrix.submatrix_one _ emb_inj))
  map_mul' := fun a b => Subtype.ext (Units.ext ((q_tri A ε hσ a).sub_mul (q_tri A ε hσ b)))

def jG (F : Type) [CommRing F] : GL (↥sᶜ ⊕ ↥sᶜ) F →* GL (ι ⊕ ι) F := Units.map (jH (emb s) emb_inj)

theorem jG_val {F : Type} [CommRing F] (m : GL (↥sᶜ ⊕ ↥sᶜ) F) :
    (jG (s := s) F m : Matrix (ι ⊕ ι) (ι ⊕ ι) F) = jM (emb s) (m : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) F) := rfl

theorem jG_inv {F : Type} [CommRing F] (m : GL (↥sᶜ ⊕ ↥sᶜ) F) :
    (((jG (s := s) F m)⁻¹ : GL (ι ⊕ ι) F) : Matrix (ι ⊕ ι) (ι ⊕ ι) F) =
      jM (emb s) ((m⁻¹ : GL (↥sᶜ ⊕ ↥sᶜ) F) : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) F) := by
  rw [← map_inv]
  rfl

theorem jG_stab {F : Type} [CommRing F] (m : GL (↥sᶜ ⊕ ↥sᶜ) F) :
    jG (s := s) F m ∈ stab F (Sum.inl '' s : Set (ι ⊕ ι)) := by
  intro r hr c hc
  have hc' : c ∉ Set.range (emb s) := by
    obtain ⟨i, hi, rfl⟩ := hc
    exact fun h => (inl_mem_range i).1 h hi
  have hne : r ≠ c := fun h => hr (h ▸ hc)
  rw [jG_inv, jG_val, jM_off_right _ _ _ _ hc', jM_off_right _ _ _ _ hc', Matrix.one_apply_ne hne]
  exact ⟨rfl, rfl⟩

def jQ : A.U ε ↥sᶜ →* A.uQ ε s where
  toFun m := ⟨⟨jG R m.1, by
    have h : (m.1 : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) R)ᵀ * Ad.J R ε ↥sᶜ *
      (m.1 : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) R).map A.σ = Ad.J R ε ↥sᶜ := m.2
    change (jM (emb s) (m.1 : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) R))ᵀ * Ad.J R ε ι *
      (jM (emb s) (m.1 : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) R)).map A.σ = Ad.J R ε ι
    rw [jM_transpose, jM_map]
    exact jM_unitary ε _ _ h⟩, Subgroup.mem_subgroupOf.2 (jG_stab m.1)⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (jG R)))
  map_mul' := fun a b => Subtype.ext (Subtype.ext (map_mul (jG R) a.1 b.1))

theorem jQ_val (m : A.U ε ↥sᶜ) : ((jQ A ε m : A.U ε ι).1 : GL (ι ⊕ ι) R) = jG R m.1 := rfl

theorem pi_j (hσ : ∀ x, A.σ (A.σ x) = x) (m : A.U ε ↥sᶜ) : piQ A ε hσ (jQ (s := s) A ε m) = m :=
  Subtype.ext (Units.ext (sub_jM emb_inj _))

end Groups

section Blocks

variable {R : Type} [CommRing R]

theorem block_unit {α : Type} [Fintype α] [DecidableEq α] {S : Set α} [Fintype S] [DecidableEq S] (g : GL α R)
    (hg : g ∈ stab R S) : IsUnit ((g : Matrix α α R).submatrix (Subtype.val : S → α) Subtype.val).det := by
  have h := sub_mul_of (Subtype.val : S → α) Subtype.val_injective (g : Matrix α α R)
    ((g⁻¹ : GL α R) : Matrix α α R) (fun x y m hm => by
      have hm' : m ∉ S := fun h => hm ⟨⟨m, h⟩, rfl⟩
      rw [(hg m hm' y.1 y.2).2, mul_zero])
  rw [Units.mul_inv, Matrix.submatrix_one _ Subtype.val_injective] at h
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_one, Matrix.det_mul] at h2
  exact isUnit_iff_exists_inv.2 ⟨_, h2.symm⟩

open Classical in
theorem bdet_val {α : Type} [Fintype α] [DecidableEq α] (S : Set α) (g : GL α R) (hg : g ∈ stab R S) :
    ((bdet S g : Rˣ) : R) = ((g : Matrix α α R).submatrix (Subtype.val : S → α) Subtype.val).det := by
  unfold bdet
  rw [dif_pos (block_unit g hg)]
  rfl

theorem det_sub_one {α : Type} [Fintype α] [DecidableEq α] {S : Set α} {_ : Fintype S} {_ : DecidableEq S}
    (g : Matrix α α R) (h : ∀ a b : S, g a.1 b.1 = if a = b then 1 else 0) :
    (g.submatrix (Subtype.val : S → α) Subtype.val).det = 1 := by
  have : g.submatrix (Subtype.val : S → α) (Subtype.val : S → α) = 1 := by
    ext a b
    rw [Matrix.submatrix_apply, h, Matrix.one_apply]
  rw [this, Matrix.det_one]

theorem det_range {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (f : β → α)
    (hf : Function.Injective f) (T : Set α) (hT : T = Set.range f) {_ : Fintype T} {_ : DecidableEq T} (g : Matrix α α R) :
    (g.submatrix (Subtype.val : T → α) Subtype.val).det = (g.submatrix f f).det := by
  subst hT
  rw [← Matrix.det_submatrix_equiv_self (Equiv.ofInjective f hf) (g.submatrix _ _), Matrix.submatrix_submatrix]
  rfl

theorem jM_mem {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} [Fintype ↥sᶜ] [DecidableEq ↥sᶜ] (O : Subring R)
    (m : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) R) (h : ∀ x y, m x y ∈ O) (r c : ι ⊕ ι) : jM (emb s) m r c ∈ O := by
  have h1 : ((1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) r c) ∈ O := by
    rw [Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  by_cases hr : r ∈ Set.range (emb s)
  · by_cases hc : c ∈ Set.range (emb s)
    · obtain ⟨x, rfl⟩ := hr
      obtain ⟨y, rfl⟩ := hc
      rw [jM_apply emb_inj]
      exact h x y
    · rw [jM_off_right _ _ _ _ hc]
      exact h1
  · rw [jM_off_left _ _ _ _ hr]
    exact h1

theorem Tri.map {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} {S : Type} [CommRing S] (f : R →+* S)
    {g : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (h : Tri s g) : Tri s (g.map f) :=
  ⟨fun r hr i hi => by rw [Matrix.map_apply, h.col r hr i hi, map_zero],
    fun i hi c hc => by rw [Matrix.map_apply, h.row i hi c hc, map_zero]⟩

theorem Tri.of_map {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} {S : Type} [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) {g : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (h : Tri s (g.map f)) : Tri s g :=
  ⟨fun r hr i hi => hf (by rw [map_zero]; exact h.col r hr i hi),
    fun i hi c hc => hf (by rw [map_zero]; exact h.row i hi c hc)⟩

end Blocks

section Parts

variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι}
  [Fintype ↥sᶜ] [DecidableEq ↥sᶜ] (A : Ad E R) (ε : ℤˣ) (hσ : ∀ x, A.σ (A.σ x) = x)

include hσ in
theorem pi_K (q : A.uQ ε s) (hq : (q : A.U ε ι) ∈ A.uK ε ι) : piQ A ε hσ q ∈ A.uK ε ↥sᶜ := by
  have h := Subgroup.mem_subgroupOf.1 hq
  refine Subgroup.mem_subgroupOf.2 ⟨fun r c => h.1 (emb s r) (emb s c), fun w => ?_⟩
  have hU := h.2 w
  set g := ((q : A.U ε ι).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) with hg
  set gi := ((((q : A.U ε ι).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) with hgi
  have hmul : g.map (A.φ w) * gi.map (A.φ w) = 1 := by
    rw [← Matrix.map_mul, hg, hgi, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 := Matrix.mem_unitaryGroup_iff'.1 hU
  have e : gi.map (A.φ w) = star (g.map (A.φ w)) := by
    rw [← Matrix.one_mul (gi.map (A.φ w)), ← h2, Matrix.mul_assoc, hmul, Matrix.mul_one]
  have t1 : Tri s (g.map (A.φ w)) := (q_tri A ε hσ q).map _
  have t2 : Tri s (gi.map (A.φ w)) := (q_tri' A ε hσ q).map _
  have h3 := t1.sub_mul t2
  rw [hmul, Matrix.submatrix_one _ emb_inj, e] at h3
  refine Matrix.mem_unitaryGroup_iff.2 ?_
  exact h3.symm

theorem j_K (m : A.U ε ↥sᶜ) (hm : m ∈ A.uK ε ↥sᶜ) : (jQ (s := s) A ε m : A.U ε ι) ∈ A.uK ε ι := by
  have h := Subgroup.mem_subgroupOf.1 hm
  refine Subgroup.mem_subgroupOf.2 ⟨fun r c => ⟨?_, ?_⟩, fun w => ?_⟩
  · exact jM_mem _ _ (fun x y => (h.1 x y).1) r c
  · rw [jQ_val, jG_inv]
    exact jM_mem _ _ (fun x y => (h.1 x y).2) r c
  · have hU := Matrix.mem_unitaryGroup_iff.1 (h.2 w)
    refine Matrix.mem_unitaryGroup_iff.2 ?_
    rw [jQ_val, jG_val, jM_map, jM_star, ← jM_mul emb_inj, hU, jM_one emb_inj]

include hσ in
theorem pi_Γ (hi : Function.Injective A.i) (q : A.uQ ε s) (hq : (q : A.U ε ι) ∈ A.uΓ ε ι) :
    piQ A ε hσ q ∈ A.uΓ ε ↥sᶜ := by
  obtain ⟨g₀, hg⟩ := Subgroup.mem_subgroupOf.1 hq
  have e1 : ((g₀ : Matrix (ι ⊕ ι) (ι ⊕ ι) E)).map A.i = ((q : A.U ε ι).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
    congrArg Units.val hg
  have e2 : (((g₀⁻¹ : GL (ι ⊕ ι) E) : Matrix (ι ⊕ ι) (ι ⊕ ι) E)).map A.i =
      ((((q : A.U ε ι).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
    rw [← hg, ← map_inv]
    rfl
  have t1 : Tri s (g₀ : Matrix (ι ⊕ ι) (ι ⊕ ι) E) := Tri.of_map A.i hi (e1 ▸ q_tri A ε hσ q)
  have t2 : Tri s ((g₀⁻¹ : GL (ι ⊕ ι) E) : Matrix (ι ⊕ ι) (ι ⊕ ι) E) := Tri.of_map A.i hi (e2 ▸ q_tri' A ε hσ q)
  refine Subgroup.mem_subgroupOf.2 ⟨piG g₀ t1 t2, Units.ext ?_⟩
  change ((g₀ : Matrix (ι ⊕ ι) (ι ⊕ ι) E).submatrix (emb s) (emb s)).map A.i =
    ((q : A.U ε ι).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R).submatrix (emb s) (emb s)
  rw [← e1]
  rfl

theorem j_Γ (m : A.U ε ↥sᶜ) (hm : m ∈ A.uΓ ε ↥sᶜ) : (jQ (s := s) A ε m : A.U ε ι) ∈ A.uΓ ε ι := by
  obtain ⟨g₀, hg⟩ := Subgroup.mem_subgroupOf.1 hm
  refine Subgroup.mem_subgroupOf.2 ⟨jG E g₀, Units.ext ?_⟩
  have e1 : ((g₀ : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) E)).map A.i = (m.1 : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) R) :=
    congrArg Units.val hg
  rw [jQ_val, jG_val, ← e1, ← jM_map]
  rfl

include hσ in
theorem pull_mem (g : A.U ε ι) : g ∈ A.uQ ε s ⊓ A.uQ ε Set.univ ↔
    ∃ hg : g ∈ A.uQ ε s, piQ A ε hσ ⟨g, hg⟩ ∈ A.uQ ε (Set.univ : Set ↥sᶜ) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, Subgroup.mem_subgroupOf.2 fun r hr c hc => ?_⟩
    have h2' := Subgroup.mem_subgroupOf.1 h2
    obtain ⟨j, -, rfl⟩ := hc
    rcases r with i | i
    · exact absurd ⟨i, trivial, rfl⟩ hr
    · exact h2' (Sum.inr i.1) (by rintro ⟨_, _, h⟩; cases h) (Sum.inl j.1) ⟨j.1, trivial, rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, Subgroup.mem_subgroupOf.2 fun r hr c hc => ?_⟩
    have h2' := Subgroup.mem_subgroupOf.1 h2
    obtain ⟨j, -, rfl⟩ := hc
    rcases r with i | i
    · exact absurd ⟨i, trivial, rfl⟩ hr
    have t1 := q_tri A ε hσ ⟨g, h1⟩
    have t2 := q_tri' A ε hσ ⟨g, h1⟩
    by_cases hj : j ∈ s
    · have : (Sum.inr i : ι ⊕ ι) ∉ (Sum.inl '' s : Set (ι ⊕ ι)) := by rintro ⟨_, _, h⟩; cases h
      exact ⟨t1.col _ this j hj, t2.col _ this j hj⟩
    by_cases hi : i ∈ s
    · have : (Sum.inl j : ι ⊕ ι) ∉ (Sum.inr '' s : Set (ι ⊕ ι)) := by rintro ⟨_, _, h⟩; cases h
      exact ⟨t1.row i hi _ this, t2.row i hi _ this⟩
    · exact h2' (Sum.inr ⟨i, hi⟩) (by rintro ⟨_, _, h⟩; cases h) (Sum.inl ⟨j, hj⟩) ⟨⟨j, hj⟩, trivial, rfl⟩

include hσ in
theorem bdet_split (p : A.uQ ε s) (hp : (p : A.U ε ι) ∈ A.uQ ε Set.univ) :
    bdet (Sum.inl '' (Set.univ : Set ι)) (p : A.U ε ι).1 =
      bdet (Sum.inl '' s) (p : A.U ε ι).1 *
        bdet (Sum.inl '' (Set.univ : Set ↥sᶜ)) (piQ A ε hσ p).1 := by
  classical
  have hπ := ((pull_mem A ε hσ (p : A.U ε ι)).1 ⟨p.2, hp⟩).2
  refine Units.ext ?_
  rw [Units.val_mul, bdet_val _ _ (Subgroup.mem_subgroupOf.1 hp), bdet_val _ _ (q_stab A ε p),
    bdet_val _ _ (Subgroup.mem_subgroupOf.1 hπ)]
  set g := ((p : A.U ε ι).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) with hg
  rw [det_range (Sum.inl : ι → ι ⊕ ι) Sum.inl_injective _ (by simp),
    det_range (fun i : {i // i ∈ s} => (Sum.inl i.1 : ι ⊕ ι)) (fun a b h => Subtype.ext (Sum.inl_injective h)) _
      (by ext x; simp),
    det_range (fun i : {i // ¬ i ∈ s} => (Sum.inl ⟨i.1, i.2⟩ : ↥sᶜ ⊕ ↥sᶜ))
      (fun a b h => Subtype.ext (congrArg Subtype.val (Sum.inl_injective h))) _ (by
        ext x
        constructor
        · rintro ⟨y, -, rfl⟩
          exact ⟨⟨y.1, y.2⟩, rfl⟩
        · rintro ⟨y, rfl⟩
          exact ⟨_, trivial, rfl⟩)]
  have hz : ∀ i, ¬ i ∈ s → ∀ j, j ∈ s → (g.submatrix Sum.inl Sum.inl : Matrix ι ι R) i j = 0 := fun i hi j hj =>
    ((q_stab A ε p) (Sum.inl i) (by
      rintro ⟨k, hk, h⟩
      exact hi (Sum.inl_injective h ▸ hk)) (Sum.inl j) ⟨j, hj, rfl⟩).1
  have := Matrix.twoBlockTriangular_det (g.submatrix Sum.inl Sum.inl : Matrix ι ι R) (fun i => i ∈ s) hz
  rw [this]
  congr! 1
  congr! 1

end Parts

section Main

variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

section Cont

variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} [Fintype ↥sᶜ] [DecidableEq ↥sᶜ] (A : Ad E R) (ε : ℤˣ)

theorem jM_cont : Continuous (jM (emb s) : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) R → Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
  unfold jM
  exact ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).add continuous_const

theorem pi_cont (hσ : ∀ x, A.σ (A.σ x) = x) : Continuous (piQ (s := s) A ε hσ) := by
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_submatrix _ _
  · exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_submatrix _ _

theorem j_cont : Continuous (jQ (s := s) A ε) := by
  refine continuous_induced_rng.2 (continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩))
  · exact jM_cont.comp (Units.continuous_val.comp continuous_subtype_val)
  · have : (fun m : A.U ε ↥sᶜ => (((jQ (s := s) A ε m : A.U ε ι).1)⁻¹ : GL (ι ⊕ ι) R).val) =
        fun m => jM (emb s) ((m.1)⁻¹ : GL (↥sᶜ ⊕ ↥sᶜ) R).val := by
      funext m
      exact jG_inv m.1
    exact this ▸ jM_cont.comp (Units.continuous_coe_inv.comp continuous_subtype_val)

end Cont

variable [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] (A : Ad E R) (ε : ℤˣ)

theorem uQ_closed {κ : Type} [Fintype κ] [DecidableEq κ] (S : Set κ) (hB : BdetLaw) (hL : A.GoodL) :
    IsClosed (A.uQ ε S : Set (A.U ε κ)) :=
  (hB E R A hL (κ ⊕ κ) (Sum.inl '' S)).1.preimage continuous_subtype_val

theorem bdet_mulQ {κ : Type} [Fintype κ] [DecidableEq κ] (S : Set κ) (hB : BdetLaw) (hL : A.GoodL)
    (p q : A.U ε κ) (hp : p ∈ A.uQ ε S) (hq : q ∈ A.uQ ε S) :
    bdet (Sum.inl '' S) (p * q).1 = bdet (Sum.inl '' S) p.1 * bdet (Sum.inl '' S) q.1 :=
  (hB E R A hL (κ ⊕ κ) (Sum.inl '' S)).2.1 _ (Subgroup.mem_subgroupOf.1 hp) _ (Subgroup.mem_subgroupOf.1 hq)

theorem bdet_contQ {κ : Type} [Fintype κ] [DecidableEq κ] (S : Set κ) (hB : BdetLaw) (hL : A.GoodL) :
    ContinuousOn (fun p : A.U ε κ => bdet (Sum.inl '' S) p.1) (A.uQ ε S : Set (A.U ε κ)) :=
  (hB E R A hL (κ ⊕ κ) (Sum.inl '' S)).2.2.1.comp continuous_subtype_val.continuousOn
    fun _ hp => Subgroup.mem_subgroupOf.1 hp

theorem bdet_ratQ {κ : Type} [Fintype κ] [DecidableEq κ] (S : Set κ) (hB : BdetLaw) (hL : A.GoodL)
    (p : A.U ε κ) (hp : p ∈ A.uQ ε S) (hr : p ∈ A.uΓ ε κ) :
    ∃ x, bdet (Sum.inl '' S) p.1 = Units.map A.i.toMonoidHom x :=
  (hB E R A hL (κ ⊕ κ) (Sum.inl '' S)).2.2.2.1 _ (Subgroup.mem_subgroupOf.1 hp) (Subgroup.mem_subgroupOf.1 hr)

theorem uH_pk {κ : Type} [Fintype κ] [DecidableEq κ] (S : Set κ) (hB : BdetLaw) (hE : ExtLaw) (hL : A.GoodL)
    [T2Space (A.U ε κ)] (hK : IsCompact (A.uK ε κ : Set (A.U ε κ))) (hI : Iwa (A.uQ ε S) (A.uK ε κ))
    (p : A.U ε κ) (hp : p ∈ A.uQ ε S) (k : A.U ε κ) (hk : k ∈ A.uK ε κ) :
    A.uH ε S (p * k) = A.lg (bdet (Sum.inl '' S) p.1) := by
  refine (hE (A.U ε κ) (A.uΓ ε κ) (A.uK ε κ) (A.uQ ε S) (fun p => A.lg (bdet (Sum.inl '' S) p.1)) hK
    (uQ_closed A ε S hB hL) hI ?_ ?_ ?_ ?_).2 p hp k hk
  · intro a ha b hb
    change A.lg (bdet (Sum.inl '' S) (a * b).1) = _
    rw [bdet_mulQ A ε S hB hL a b ha hb, hL.lgmul]
  · exact hL.lgcont.comp_continuousOn (bdet_contQ A ε S hB hL)
  · intro a ha hk
    exact (hB E R A hL (κ ⊕ κ) (Sum.inl '' S)).2.2.2.2.1 _ (Subgroup.mem_subgroupOf.1 ha)
      (Subgroup.mem_subgroupOf.1 hk)
  · intro a ha hr
    obtain ⟨x, hx⟩ := bdet_ratQ A ε S hB hL a ha hr
    change A.lg (bdet (Sum.inl '' S) a.1) = 0
    rw [hx]
    exact hL.lgi x

variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} {_fF : Fintype ↥sᶜ} {_fD : DecidableEq ↥sᶜ}

def c₀ (A : Ad E R) (ε : ℤˣ) (s : Set ι) : A.U ε ι → ℂ := fun g => (A.χ (bdet (Sum.inl '' s) g.1) : ℂ)

theorem c₀_par (hB : BdetLaw) (hA : A.Good) (hI : Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι)) :
    IsPar (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε s) (c₀ A ε s) := by
  have hL := hA.toGoodL
  refine ⟨uQ_closed A ε s hB hL, fun g => ?_, ⟨fun p hp q hq => ?_, fun p _ => ?_, fun γ hγ hq => ?_, ?_⟩⟩
  · obtain ⟨p, hp, k, hk, rfl⟩ := hI g
    exact ⟨p, hp.1, k, hk, rfl⟩
  · simp only [c₀]
    rw [bdet_mulQ A ε s hB hL p q hp hq, map_mul, Circle.coe_mul]
  · exact Circle.norm_coe _
  · obtain ⟨x, hx⟩ := bdet_ratQ A ε s hB hL γ hq hγ
    simp only [c₀]
    rw [hx, hL.χi]
    rfl
  · have hc : Continuous (fun z : Circle => (z : ℂ)) := by
      first | fun_prop | exact continuous_subtype_val | exact continuous_induced_dom
    exact hc.comp_continuousOn (hL.χcont.comp_continuousOn (bdet_contQ A ε s hB hL))

theorem bdet_j (m : A.U ε ↥sᶜ) : bdet (Sum.inl '' s) (jQ (s := s) A ε m : A.U ε ι).1 = 1 := by
  classical
  refine Units.ext ?_
  rw [bdet_val _ _ (show ((jQ (s := s) A ε m : A.U ε ι).1 : GL (ι ⊕ ι) R) ∈ stab R (Sum.inl '' s : Set (ι ⊕ ι)) from
    jG_stab m.1), Units.val_one]
  refine det_sub_one _ fun a b => ?_
  have hb : b.1 ∉ Set.range (emb s) := fun hh => by
    obtain ⟨i, hi, h⟩ := b.2
    rw [← h] at hh
    exact (inl_mem_range i).1 hh hi
  rw [jQ_val, jG_val, jM_off_right _ _ _ _ hb, Matrix.one_apply]
  simp [Subtype.ext_iff]

theorem levi_pullback_iwasawa_unitary (hB : BdetLaw) (hE : ExtLaw) (hT : GrpTop) (hA : A.Good)
    (hI : Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι)) :
    ∃ (π : A.uQ ε s →* A.U ε ↥sᶜ) (j : A.U ε ↥sᶜ →* A.uQ ε s) (c : A.U ε ι → ℂ),
      IsLevi (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε s) (A.uΓ ε _) (A.uK ε _) π j c ∧
      IsPull (A.uQ ε s) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uQ ε Set.univ) π c (A.uC ε ι) (A.uC ε _) ∧
      Iwa (A.uQ ε (Set.univ : Set ↥sᶜ)) (A.uK ε _) ∧
      PullHt (A.uK ε ι) (A.uQ ε s) π (fun g => A.uH ε Set.univ g - A.uH ε s g) (A.uH ε Set.univ) := by
  have hL := hA.toGoodL
  have hσ := hA.σσ
  obtain ⟨-, -, -, t1, -, -, hK⟩ := hT E R A hA ι ε
  obtain ⟨-, -, -, t2, -, -, hK'⟩ := hT E R A hA ↥sᶜ ε
  haveI := t1
  haveI := t2
  have hIs : Iwa (A.uQ ε s) (A.uK ε ι) := fun g => by
    obtain ⟨p, hp, k, hk, h⟩ := hI g
    exact ⟨p, hp.1, k, hk, h⟩
  have hIu : Iwa (A.uQ ε (Set.univ : Set ι)) (A.uK ε ι) := fun g => by
    obtain ⟨p, hp, k, hk, h⟩ := hI g
    exact ⟨p, hp.2, k, hk, h⟩

  have hdec : ∀ q : A.uQ ε s, ∃ (P K₁ : A.uQ ε s), q = P * K₁ ∧ (P : A.U ε ι) ∈ A.uQ ε Set.univ ∧
      (K₁ : A.U ε ι) ∈ A.uK ε ι := fun q => by
    obtain ⟨p, hp, k, hk, h⟩ := hI q.1
    have hk' : k ∈ A.uQ ε s := by
      have : k = p⁻¹ * q.1 := by rw [h, inv_mul_cancel_left]
      rw [this]
      exact mul_mem (inv_mem hp.1) q.2
    exact ⟨⟨p, hp.1⟩, ⟨k, hk'⟩, Subtype.ext h, hp.2, hk⟩
  have hI' : Iwa (A.uQ ε (Set.univ : Set ↥sᶜ)) (A.uK ε ↥sᶜ) := fun m => by
    obtain ⟨P, K₁, h, hP, hK₁⟩ := hdec (jQ A ε m)
    refine ⟨piQ A ε hσ P, ((pull_mem A ε hσ P.1).1 ⟨P.2, hP⟩).2, piQ A ε hσ K₁, pi_K A ε hσ K₁ hK₁, ?_⟩
    rw [← map_mul, ← h, pi_j]
  refine ⟨piQ A ε hσ, jQ A ε, c₀ A ε s, ⟨pi_cont A ε hσ, j_cont A ε, pi_j A ε hσ, c₀_par A ε hB hA hI, fun m => ?_,
    pi_K A ε hσ, j_K A ε, pi_Γ A ε hσ hL.iinj, j_Γ A ε⟩, ⟨pull_mem A ε hσ, fun q hq => ?_⟩, hI', fun q k hk => ?_⟩
  · simp only [c₀]
    rw [bdet_j, map_one]
    rfl
  · have hp : (q : A.U ε ι) ∈ A.uQ ε Set.univ := ((pull_mem A ε hσ q.1).2 ⟨q.2, hq⟩).2
    change (A.χ (bdet (Sum.inl '' (Set.univ : Set ι)) (q : A.U ε ι).1) : ℂ) =
      (A.χ (bdet (Sum.inl '' s) (q : A.U ε ι).1) : ℂ) *
        (A.χ (bdet (Sum.inl '' (Set.univ : Set ↥sᶜ)) (piQ A ε hσ q).1) : ℂ)
    rw [bdet_split A ε hσ q hp, map_mul, Circle.coe_mul]
  · obtain ⟨P, K₁, h, hP, hK₁⟩ := hdec q
    have e1 : (q : A.U ε ι) * k = (P : A.U ε ι) * ((K₁ : A.U ε ι) * k) := by
      rw [h, Subgroup.coe_mul, mul_assoc]
    have hkk : (K₁ : A.U ε ι) * k ∈ A.uK ε ι := mul_mem hK₁ hk
    change A.uH ε Set.univ ((q : A.U ε ι) * k) - A.uH ε s ((q : A.U ε ι) * k) = _
    rw [e1, uH_pk A ε Set.univ hB hE hL hK hIu _ hP _ hkk, uH_pk A ε s hB hE hL hK hIs _ P.2 _ hkk, h, map_mul,
      uH_pk A ε Set.univ hB hE hL hK' hI' _ ((pull_mem A ε hσ P.1).1 ⟨P.2, hP⟩).2 _ (pi_K A ε hσ K₁ hK₁),
      bdet_split A ε hσ P hP, hL.lgmul]
    ring

end Main

theorem leviQ : BdetLaw → ExtLaw → GrpTop → LeviQ := by
  intro hB hE hT E R _ _ _ _ _ _ _ A hA ι _ _ ε s hI
  exact levi_pullback_iwasawa_unitary A ε hB hE hT hA hI

end GlobalTheory.CompanionTheory.RgEisLeviQUnit

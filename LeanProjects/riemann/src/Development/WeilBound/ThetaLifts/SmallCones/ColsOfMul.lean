import Mathlib

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKCT.Fr

open Matrix

variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]

def fr (ι : Matrix d e R) (x y : d → R) : Matrix d (e ⊕ Fin 2) R := fromCols ι (of fun i j => ![x i, y i] j)

def gr (ε : R) (J₁ : Matrix e e R) : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R := fromBlocks J₁ 0 0 !![0, 1; ε, 0]

structure IsFr (c : R →+* R) (ε : R) (J : Matrix d d R) (J₁ : Matrix e e R) (ι : Matrix d e R) (x y : d → R)
    (A' : Matrix (e ⊕ Fin 2) d R) : Prop where
  eps : ε * ε = 1
  gram : (fr ι x y)ᵀ * J * (fr ι x y).map c = gr ε J₁
  inv1 : fr ι x y * A' = 1
  inv2 : A' * fr ι x y = 1

def dg (g : Matrix e e R) (t t' : R) : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R := fromBlocks g 0 0 !![t, 0; 0, t']

variable {ε : R} {A' : Matrix (e ⊕ Fin 2) d R} {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}

omit [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e] in
theorem fr_map (f : R →+* S) : fr (ι.map f) (fun i => f (x i)) (fun i => f (y i)) = (fr ι x y).map f := by
  ext i j
  rcases j with j | j
  · simp [fr]
  · fin_cases j <;> simp [fr]

omit [Fintype e] [DecidableEq e] in
theorem gr_map (f : R →+* S) : gr (f ε) (J₁.map f) = (gr ε J₁).map f := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [gr]
  · simp [gr]
  · simp [gr]
  · fin_cases i <;> fin_cases j <;> simp [gr]

theorem IsFr.map (h : IsFr c ε J J₁ ι x y A') (f : R →+* S) {c' : S →+* S} (hc : ∀ a, f (c a) = c' (f a)) :
    IsFr c' (f ε) (J.map f) (J₁.map f) (ι.map f) (fun i => f (x i)) (fun i => f (y i)) (A'.map f) := by
  have hfr : fr (ι.map f) (fun i => f (x i)) (fun i => f (y i)) = (fr ι x y).map f := fr_map f
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_mul, h.eps, map_one]
  · have hcm : ((fr ι x y).map f).map c' = ((fr ι x y).map c).map f := by
      ext i j
      simp [hc]
    rw [hfr, gr_map, ← h.gram, hcm, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  · rw [hfr, ← Matrix.map_mul, h.inv1, Matrix.map_one _ f.map_zero f.map_one]
  · rw [hfr, ← Matrix.map_mul, h.inv2, Matrix.map_one _ f.map_zero f.map_one]

theorem IsFr.isUnit_det (h : IsFr c ε J J₁ ι x y A') (hJ : IsUnit J.det) : IsUnit J₁.det := by
  have e1 : (fr ι x y).map c * A'.map c = 1 := by
    rw [← Matrix.map_mul, h.inv1, Matrix.map_one _ c.map_zero c.map_one]
  have e2 : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJ
  have e3 : (fr ι x y)ᵀ * A'ᵀ = 1 := by
    rw [← Matrix.transpose_mul, h.inv2, Matrix.transpose_one]
  have hinv : gr ε J₁ * (A'.map c * J⁻¹ * A'ᵀ) = 1 := by
    rw [← h.gram]
    calc (fr ι x y)ᵀ * J * (fr ι x y).map c * (A'.map c * J⁻¹ * A'ᵀ)
        = (fr ι x y)ᵀ * (J * (((fr ι x y).map c * A'.map c) * J⁻¹)) * A'ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e1, Matrix.one_mul, e2, Matrix.mul_one, e3]
  have hu : IsUnit (gr ε J₁).det := Matrix.isUnit_det_of_right_inverse hinv
  unfold gr at hu
  rw [Matrix.det_fromBlocks_zero₂₁] at hu
  exact isUnit_of_mul_isUnit_left hu

omit [DecidableEq d] [DecidableEq e] in
theorem cols_of_mul {m : Matrix d d R} {g : Matrix e e R} {b : Matrix e (Fin 2) R} {a : Matrix (Fin 2) e R}
    {s : Matrix (Fin 2) (Fin 2) R} (h : m * fr ι x y = fr ι x y * fromBlocks g b a s) :
    m * ι = ι * g + of (fun i j => ![x i, y i] j) * a ∧
      m *ᵥ x = ι *ᵥ (fun j => b j 0) + s 0 0 • x + s 1 0 • y ∧ m *ᵥ y = ι *ᵥ (fun j => b j 1) + s 0 1 • x + s 1 1 • y := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have := congrFun (congrFun h i) (Sum.inl j)
    simp [fr, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at this ⊢ <;>
      linear_combination this
  · ext i
    have := congrFun (congrFun h i) (Sum.inr 0)
    simp [fr, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] at this ⊢ <;>
      linear_combination this
  · ext i
    have := congrFun (congrFun h i) (Sum.inr 1)
    simp [fr, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] at this ⊢ <;>
      linear_combination this

theorem IsFr.levi (h : IsFr c ε J J₁ ι x y A') (hcc : ∀ a, c (c a) = a) {t t' : R} (ht : t * t' = 1) {g g' : Matrix e e R}
    (hg' : g * g' = 1) (hg : gᵀ * J₁ * g.map c = J₁) :
    ∃ m m' : Matrix d d R, m = fr ι x y * dg g t (c t') * A' ∧ m * m' = 1 ∧ mᵀ * J * m.map c = J ∧ m *ᵥ x = t • x ∧ m *ᵥ y = c t' • y ∧ m * ι = ι * g := by
  have hct : c t * c t' = 1 := by rw [← map_mul, ht, map_one]
  have hct' : c t' * c t = 1 := by rw [mul_comm]; exact hct
  have hdd : dg g t (c t') * dg g' t' (c t) = 1 := by
    unfold dg
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hg']
    rw [← Matrix.fromBlocks_one]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ht, hct']
  have hdgT : (dg g t (c t'))ᵀ * gr ε J₁ * (dg g t (c t')).map c = gr ε J₁ := by
    unfold dg gr
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_zero, Matrix.map_zero _ c.map_zero, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add]
    rw [hg]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hcc, ht] <;>
      linear_combination ε * hct'
  have hmfr : fr ι x y * dg g t (c t') * A' * fr ι x y = fr ι x y * dg g t (c t') := by
    rw [Matrix.mul_assoc, h.inv2, Matrix.mul_one]
  obtain ⟨c1, c2, c3⟩ := cols_of_mul (g := g) (b := 0) (a := 0) (s := !![t, 0; 0, c t']) hmfr
  refine ⟨fr ι x y * dg g t (c t') * A', fr ι x y * dg g' t' (c t) * A', rfl, ?_, ?_, ?_, ?_, ?_⟩
  · calc fr ι x y * dg g t (c t') * A' * (fr ι x y * dg g' t' (c t) * A')
        = fr ι x y * (dg g t (c t') * (A' * fr ι x y) * dg g' t' (c t)) * A' := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h.inv2, Matrix.mul_one, hdd, Matrix.mul_one, h.inv1]
  · calc (fr ι x y * dg g t (c t') * A')ᵀ * J * (fr ι x y * dg g t (c t') * A').map c
        = A'ᵀ * ((dg g t (c t'))ᵀ * ((fr ι x y)ᵀ * J * (fr ι x y).map c) * (dg g t (c t')).map c) *
            A'.map c := by
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = A'ᵀ * ((fr ι x y)ᵀ * J * (fr ι x y).map c) * A'.map c := by rw [h.gram, hdgT]
      _ = (fr ι x y * A')ᵀ * J * (fr ι x y * A').map c := by
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = J := by
          rw [h.inv1, Matrix.transpose_one, Matrix.map_one _ c.map_zero c.map_one, Matrix.one_mul,
            Matrix.mul_one]
  · rw [c2]
    ext i
    simp [Matrix.mulVec, dotProduct]
  · rw [c3]
    ext i
    simp [Matrix.mulVec, dotProduct]
  · rw [c1]
    simp

private theorem fr_mulVec_sum_elim (u : e → R) (s t : R) :
    fr ι x y *ᵥ Sum.elim u ![s, t] = ι *ᵥ u + s • x + t • y := by
  ext i
  simp [fr, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] <;> ring

private theorem eq_of_iota_mulVec_add_smul_eq (h : IsFr c ε J J₁ ι x y A') {u u' : e → R} {s t s' t' : R}
    (e1 : ι *ᵥ u + s • x + t • y = ι *ᵥ u' + s' • x + t' • y) : u = u' ∧ s = s' ∧ t = t' := by
  rw [← fr_mulVec_sum_elim, ← fr_mulVec_sum_elim] at e1
  have h2 := congrArg (fun v => A' *ᵥ v) e1
  simp only [Matrix.mulVec_mulVec, h.inv2, Matrix.one_mulVec] at h2
  exact ⟨funext fun j => by simpa using congrFun h2 (Sum.inl j), by simpa using congrFun h2 (Sum.inr 0),
    by simpa using congrFun h2 (Sum.inr 1)⟩

private theorem mul_fr_eq_fr_mul_fromBlocks_and_preserves_gr (h : IsFr c ε J J₁ ι x y A') {p : Matrix d d R} (hp : pᵀ * J * p.map c = J) :
    p * fr ι x y = fr ι x y * Matrix.fromBlocks (A' * p * fr ι x y).toBlocks₁₁ (A' * p * fr ι x y).toBlocks₁₂
      (A' * p * fr ι x y).toBlocks₂₁ (A' * p * fr ι x y).toBlocks₂₂ ∧
    (A' * p * fr ι x y)ᵀ * gr ε J₁ * (A' * p * fr ι x y).map c = gr ε J₁ := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.fromBlocks_toBlocks, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.inv1, Matrix.one_mul]
  · calc (A' * p * fr ι x y)ᵀ * gr ε J₁ * (A' * p * fr ι x y).map c
        = (fr ι x y)ᵀ * (pᵀ * ((fr ι x y * A')ᵀ * J * (fr ι x y * A').map c) * p.map c) *
            (fr ι x y).map c := by
          rw [← h.gram]
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = gr ε J₁ := by
          rw [h.inv1, Matrix.transpose_one, Matrix.map_one _ c.map_zero c.map_one, Matrix.one_mul,
            Matrix.mul_one, hp, h.gram]

theorem IsFr.stab (h : IsFr c ε J J₁ ι x y A') {t t' : R} (ht : t * t' = 1) {p : Matrix d d R}
    (hp : pᵀ * J * p.map c = J) (hx : p *ᵥ x = t • x) :
    ∃ (g : Matrix e e R) (α : e → R), g = (A' * p * fr ι x y).toBlocks₁₁ ∧ gᵀ * J₁ * g.map c = J₁ ∧ ∀ z, p *ᵥ (ι *ᵥ z) = ι *ᵥ (g *ᵥ z) + (α ⬝ᵥ z) • x := by
  have hct : c t * c t' = 1 := by rw [← map_mul, ht, map_one]
  obtain ⟨hpf, hQ⟩ := mul_fr_eq_fr_mul_fromBlocks_and_preserves_gr h hp
  have hQ' := hQ
  rw [← Matrix.fromBlocks_toBlocks (A' * p * fr ι x y)] at hQ'
  generalize (A' * p * fr ι x y).toBlocks₁₁ = g0 at hpf hQ' ⊢
  generalize (A' * p * fr ι x y).toBlocks₁₂ = b0 at hpf hQ' ⊢
  generalize (A' * p * fr ι x y).toBlocks₂₁ = a0 at hpf hQ' ⊢
  generalize (A' * p * fr ι x y).toBlocks₂₂ = s0 at hpf hQ' ⊢
  obtain ⟨c1, c2, c3⟩ := cols_of_mul hpf
  obtain ⟨hb0, hs00, hs10⟩ := eq_of_iota_mulVec_add_smul_eq h (u := 0) (s := t) (t := 0) (u' := fun j => b0 j 0)
    (s' := s0 0 0) (t' := s0 1 0) (by rw [← c2, hx]; simp)
  have hb0' : ∀ j, b0 j 0 = 0 := fun j => (congrFun hb0 j).symm
  unfold gr at hQ'
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hQ'
  obtain ⟨e11, e12, -, -⟩ := hQ'
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e11 e12
  have ha1 : ∀ i, a0 1 i = 0 := by
    intro i
    have h12 := congrFun (congrFun e12 i) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, hb0', ← hs00, ← hs10] at h12
    linear_combination (ε * c t') * h12 - a0 1 i * h.eps - a0 1 i * ε * ε * hct
  have haK : a0ᵀ * !![0, 1; ε, 0] * a0.map c = 0 := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha1]
  rw [haK, add_zero] at e11
  refine ⟨g0, fun j => a0 0 j, rfl, e11, fun z => ?_⟩
  rw [Matrix.mulVec_mulVec, c1, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha1] <;> ring

theorem IsFr.ext (h : IsFr c ε J J₁ ι x y A') {m m' : Matrix d d R} (h1 : m *ᵥ x = m' *ᵥ x) (h2 : m *ᵥ y = m' *ᵥ y)
    (h3 : m * ι = m' * ι) : m = m' := by
  have hf : m * fr ι x y = m' * fr ι x y := by
    ext i j
    rcases j with j | j
    · have := congrFun (congrFun h3 i) j
      simpa [fr, Matrix.mul_apply] using this
    · fin_cases j
      · have := congrFun h1 i
        simpa [fr, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
      · have := congrFun h2 i
        simpa [fr, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  calc m = m * (fr ι x y * A') := by rw [h.inv1, Matrix.mul_one]
    _ = m' * (fr ι x y * A') := by rw [← Matrix.mul_assoc, hf, Matrix.mul_assoc]
    _ = m' := by rw [h.inv1, Matrix.mul_one]

omit [DecidableEq d] [DecidableEq e] in
theorem fr_mulVec (u : e → R) (s t : R) : fr ι x y *ᵥ Sum.elim u ![s, t] = ι *ᵥ u + s • x + t • y := by
  ext i
  simp [fr, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] <;> ring

theorem IsFr.span (h : IsFr c ε J J₁ ι x y A') (z : d → R) : ∃ (u : e → R) (s t : R), z = ι *ᵥ u + s • x + t • y := by
  refine ⟨fun j => (A' *ᵥ z) (Sum.inl j), (A' *ᵥ z) (Sum.inr 0), (A' *ᵥ z) (Sum.inr 1), ?_⟩
  rw [← fr_mulVec]
  have hw : Sum.elim (fun j => (A' *ᵥ z) (Sum.inl j)) ![(A' *ᵥ z) (Sum.inr 0), (A' *ᵥ z) (Sum.inr 1)] =
      A' *ᵥ z := by
    ext k
    rcases k with k | k
    · rfl
    · fin_cases k <;> rfl
  rw [hw, Matrix.mulVec_mulVec, h.inv1, Matrix.one_mulVec]

theorem IsFr.indep (h : IsFr c ε J J₁ ι x y A') {u u' : e → R} {s t s' t' : R}
    (e1 : ι *ᵥ u + s • x + t • y = ι *ᵥ u' + s' • x + t' • y) : u = u' ∧ s = s' ∧ t = t' := by
  rw [← fr_mulVec, ← fr_mulVec] at e1
  have := congrArg (A' *ᵥ ·) e1
  simp only [mulVec_mulVec, h.inv2, one_mulVec] at this
  exact ⟨funext fun j => congrFun this (Sum.inl j), congrFun this (Sum.inr 0), congrFun this (Sum.inr 1)⟩

theorem IsFr.fix_y (h : IsFr c ε J J₁ ι x y A') (hcc : ∀ a, c (c a) = a) {p : Matrix d d R}
    (hp : pᵀ * J * p.map c = J) (hx : p *ᵥ x = x) : ∃ (u : e → R) (s : R), p *ᵥ y = y + ι *ᵥ u + s • x := by
  obtain ⟨hpf, hQ⟩ := mul_fr_eq_fr_mul_fromBlocks_and_preserves_gr h hp
  have hQ' := hQ
  rw [← Matrix.fromBlocks_toBlocks (A' * p * fr ι x y)] at hQ'
  generalize (A' * p * fr ι x y).toBlocks₁₁ = g0 at hpf hQ'
  generalize (A' * p * fr ι x y).toBlocks₁₂ = b0 at hpf hQ'
  generalize (A' * p * fr ι x y).toBlocks₂₁ = a0 at hpf hQ'
  generalize (A' * p * fr ι x y).toBlocks₂₂ = s0 at hpf hQ'
  obtain ⟨c1, c2, c3⟩ := cols_of_mul hpf
  obtain ⟨hb0, hs00, hs10⟩ := eq_of_iota_mulVec_add_smul_eq h (u := 0) (s := 1) (t := 0) (u' := fun j => b0 j 0)
    (s' := s0 0 0) (t' := s0 1 0) (by rw [← c2, hx]; simp)
  have hb0' : ∀ j, b0 j 0 = 0 := fun j => (congrFun hb0 j).symm
  unfold gr at hQ'
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hQ'
  obtain ⟨-, -, -, e22⟩ := hQ'
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e22
  have h22 := congrFun (congrFun e22 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, hb0', ← hs00, ← hs10] at h22
  have hs11 : s0 1 1 = 1 := by rw [← hcc (s0 1 1), h22, map_one]
  refine ⟨fun j => b0 j 1, s0 0 1, ?_⟩
  rw [c3, hs11, one_smul]
  abel

end PositivityTheory.ThKCT.Fr

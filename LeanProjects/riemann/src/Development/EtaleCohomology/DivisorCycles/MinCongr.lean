import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.RepPf

variable {C : Type} [Field C] {N n : ℕ}

section
variable (p : Fin n → Mat C N) (E : Fin n → Fin n → Mat C N)

noncomputable def coef (a : Mat C N) (i j : Fin n) : C := by
  classical
  exact if h : ∃ c : C, E i j ≠ 0 ∧ p i * a * p j = c • E i j then h.choose else 0

lemma coef_zero {a : Mat C N} {i j : Fin n} (h : E i j = 0) : coef p E a i j = 0 := by
  unfold coef
  rw [dif_neg]
  rintro ⟨c, hc, -⟩
  exact hc h

variable {p E}

lemma coef_spec {R : Subalgebra C (Mat C N)} (hM : MUnits R p E) {a : Mat C N} (ha : a ∈ R)
    (i j : Fin n) : p i * a * p j = coef p E a i j • E i j := by
  obtain ⟨c, hc⟩ := hM.2.2.2.2.2 a ha i j
  by_cases hE : E i j = 0
  · rw [hc, hE, smul_zero, smul_zero]
  · have h : ∃ c : C, E i j ≠ 0 ∧ p i * a * p j = c • E i j := ⟨c, hE, hc⟩
    unfold coef
    rw [dif_pos h]
    exact h.choose_spec.2

lemma E_left {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) (i j : Fin n) :
    p i * E i j = E i j := by
  calc p i * E i j = p i * (p i * E i j * p j) := by rw [hM.2.2.1 i j]
    _ = (p i * p i) * E i j * p j := by simp only [mul_assoc]
    _ = E i j := by rw [(hp.1.idem i).eq, hM.2.2.1 i j]

lemma E_right {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) (i j : Fin n) :
    E i j * p j = E i j := by
  calc E i j * p j = (p i * E i j * p j) * p j := by rw [hM.2.2.1 i j]
    _ = p i * E i j * (p j * p j) := by simp only [mul_assoc]
    _ = E i j := by rw [(hp.1.idem j).eq, hM.2.2.1 i j]

lemma expand (hp : Sys p) (a b : Mat C N) (i k : Fin n) :
    p i * (a * b) * p k = ∑ j, (p i * a * p j) * (p j * b * p k) := by
  have h : ∀ j, (p i * a * p j) * (p j * b * p k) = p i * a * p j * b * p k := by
    intro j
    calc (p i * a * p j) * (p j * b * p k) = p i * a * (p j * p j) * b * p k := by
          simp only [mul_assoc]
      _ = _ := by rw [(hp.1.idem j).eq]
  simp only [h]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, hp.1.complete, mul_one]
  simp only [mul_assoc]

lemma coef_mul {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) {a b : Mat C N}
    (ha : a ∈ R) (hb : b ∈ R) (i k : Fin n) :
    coef p E (a * b) i k = ∑ j, coef p E a i j * coef p E b j k := by
  by_cases hik : E i k = 0
  · rw [coef_zero p E hik]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hij : E i j = 0
    · rw [coef_zero p E hij, zero_mul]
    by_cases hjk : E j k = 0
    · rw [coef_zero p E hjk, mul_zero]
    exact absurd hik (hM.2.2.2.2.1 i j k hij hjk).2
  · apply smul_left_injective C hik
    simp only
    rw [← coef_spec hM (R.mul_mem ha hb), expand hp, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coef_spec hM ha, coef_spec hM hb, smul_mul_smul_comm]
    by_cases hij : E i j = 0
    · simp [hij, coef_zero p E hij]
    by_cases hjk : E j k = 0
    · simp [hjk, coef_zero p E hjk]
    rw [(hM.2.2.2.2.1 i j k hij hjk).1]

lemma coef_one {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) (i j : Fin n) :
    coef p E 1 i j = (1 : Matrix (Fin n) (Fin n) C) i j := by
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq]
    have hE : E i i ≠ 0 := by rw [hM.2.1 i]; exact hp.2 i
    apply smul_left_injective C hE
    simp only
    rw [← coef_spec hM R.one_mem, one_smul, mul_one, (hp.1.idem i).eq, hM.2.1 i]
  · rw [Matrix.one_apply_ne hij]
    by_cases hE : E i j = 0
    · exact coef_zero p E hE
    apply smul_left_injective C hE
    simp only
    rw [← coef_spec hM R.one_mem, zero_smul, mul_one, hp.1.ortho hij]

end

section
variable {p : Fin n → Mat C N} {E : Fin n → Fin n → Mat C N}

variable (E) in

noncomputable def blk (j : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => E i j ≠ 0

variable (E) in

noncomputable def bb (j : Fin n) : Fin n :=
  if h : (blk E j).Nonempty then (blk E j).min' h else j

lemma mem_blk {i j : Fin n} : i ∈ blk E j ↔ E i j ≠ 0 := by
  classical
  unfold blk
  simp

lemma min'_congr {s t : Finset (Fin n)} (h : s.Nonempty) (h' : t.Nonempty) (e : s = t) :
    s.min' h = t.min' h' := by
  subst e; rfl

lemma bb_spec {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) (j : Fin n) :
    (blk E j).Nonempty ∧ E (bb E j) j ≠ 0 := by
  have hne : (blk E j).Nonempty := ⟨j, mem_blk.2 (by rw [hM.2.1 j]; exact hp.2 j)⟩
  refine ⟨hne, ?_⟩
  unfold bb
  rw [dif_pos hne]
  exact mem_blk.1 (Finset.min'_mem _ hne)

lemma bb_ne {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) (j : Fin n) :
    E j (bb E j) ≠ 0 := hM.2.2.2.1 _ _ (bb_spec hp hM j).2

lemma bb_congr {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) {i j : Fin n}
    (hij : E i j ≠ 0) : bb E i = bb E j := by
  have e : blk E i = blk E j := by
    ext k
    rw [mem_blk, mem_blk]
    constructor
    · intro hki; exact (hM.2.2.2.2.1 k i j hki hij).2
    · intro hkj; exact (hM.2.2.2.2.1 k j i hkj (hM.2.2.2.1 i j hij)).2
  unfold bb
  rw [dif_pos (bb_spec hp hM i).1, dif_pos (bb_spec hp hM j).1]
  exact min'_congr _ _ e

lemma mul_E {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) {a : Mat C N}
    (ha : a ∈ R) (j : Fin n) : a * E j (bb E j) = ∑ i, coef p E a i j • E i (bb E i) := by
  have h1 : a * E j (bb E j) = ∑ i, (p i * a * p j) * E j (bb E j) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, hp.1.complete, one_mul, mul_assoc,
      E_left hp hM]
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coef_spec hM ha, smul_mul_assoc]
  by_cases hij : E i j = 0
  · simp [hij, coef_zero p E hij]
  rw [(hM.2.2.2.2.1 i j (bb E j) hij (bb_ne hp hM j)).1, bb_congr hp hM hij]

variable (E) in

noncomputable def T (w : Fin N → C) : Matrix (Fin N) (Fin n) C := Matrix.of fun x j => (E j (bb E j) *ᵥ w) x

lemma mul_T (M : Mat C N) (w : Fin N → C) (x : Fin N) (j : Fin n) :
    (M * T E w) x j = ((M * E j (bb E j)) *ᵥ w) x := by
  rw [← Matrix.mulVec_mulVec]
  simp [T, Matrix.mul_apply, Matrix.mulVec, dotProduct]

variable (p E) in

noncomputable def rmat (a : Mat C N) : Matrix (Fin n) (Fin n) C := Matrix.of fun i j => coef p E a i j

lemma T_mul (w : Fin N → C) (a : Mat C N) (x : Fin N) (j : Fin n) :
    (T E w * rmat p E a) x j = ((∑ i, coef p E a i j • E i (bb E i)) *ᵥ w) x := by
  simp [T, rmat, Matrix.mul_apply, Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply, mul_comm]

lemma intertw {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) {a : Mat C N}
    (ha : a ∈ R) (w : Fin N → C) : a * T E w = T E w * rmat p E a := by
  ext x j
  rw [mul_T, T_mul, mul_E hp hM ha]

end

theorem Rep_of : Rep := by
  classical
  intro Γ C _ _ N n ρ R p E hp hM hρ
  let f : Γ →* Matrix (Fin n) (Fin n) C :=
    { toFun := fun g => rmat p E (ρ g : Mat C N)
      map_one' := by
        ext i j
        simp only [map_one, Units.val_one]
        exact coef_one hp hM i j
      map_mul' := by
        intro g h
        ext i k
        simp only [map_mul, Units.val_mul]
        rw [Matrix.mul_apply]
        exact coef_mul hp hM (hρ g) (hρ h) i k }
  let r : Γ →* GL (Fin n) C := f.toHomUnits
  have hcol : ∀ k, ∃ v : Fin N → C, p k *ᵥ v = v ∧ v ≠ 0 := by
    intro k
    by_contra hcon
    push_neg at hcon
    apply hp.2 k
    ext x c
    have h1 := hcon (p k *ᵥ Pi.single c 1) (by rw [Matrix.mulVec_mulVec, (hp.1.idem k).eq])
    have h2 := congrFun h1 x
    simpa [Matrix.mulVec_single_one] using h2
  choose v hv using hcol
  let w0 := ∑ k, v k
  have hw : ∀ k, p k *ᵥ w0 = v k := by
    intro k
    simp only [w0, Matrix.mulVec_sum]
    rw [Finset.sum_eq_single k]
    · exact (hv k).1
    · intro m _ hmk
      rw [← (hv m).1, Matrix.mulVec_mulVec, hp.1.ortho (Ne.symm hmk), Matrix.zero_mulVec]
    · simp
  have hu : ∀ k, ∃ u : Fin N → C, u ⬝ᵥ v k = 1 := by
    intro k
    obtain ⟨x, hx⟩ := Function.ne_iff.1 (hv k).2
    have hx' : v k x ≠ 0 := hx
    exact ⟨Pi.single x (v k x)⁻¹, by simp [hx']⟩
  choose u hu using hu
  let A := T E w0
  let B : Matrix (Fin n) (Fin N) C := Matrix.of fun j x => (u (bb E j) ᵥ* E (bb E j) j) x
  refine ⟨r, A, B, ?_, ?_, ?_⟩
  · ext j k
    have hprod : E (bb E j) j * E k (bb E k) = if j = k then p (bb E j) else 0 := by
      split_ifs with h
      · subst h
        rw [(hM.2.2.2.2.1 _ j _ (bb_spec hp hM j).2 (bb_ne hp hM j)).1, hM.2.1]
      · rw [← E_right hp hM (bb E j) j, ← E_left hp hM k (bb E k)]
        calc E (bb E j) j * p j * (p k * E k (bb E k))
            = E (bb E j) j * (p j * p k) * E k (bb E k) := by simp only [mul_assoc]
          _ = 0 := by rw [hp.1.ortho h, mul_zero, zero_mul]
    have hBA : (B * A) j k = (u (bb E j) ᵥ* E (bb E j) j) ⬝ᵥ (E k (bb E k) *ᵥ w0) := rfl
    rw [hBA, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hprod]
    split_ifs with h
    · rw [hw, hu, h, Matrix.one_apply_eq]
    · rw [Matrix.zero_mulVec, dotProduct_zero, Matrix.one_apply_ne h]
  · intro g
    exact intertw hp hM (hρ g) w0
  · intro Z hZ
    have hZE : ∀ j, Z * E j (bb E j) = 0 := by
      intro j
      rw [Matrix.ext_iff_mulVec]
      intro w
      have h1 := hZ (T E w) (fun g => intertw hp hM (hρ g) w)
      ext x
      have h2 := congrFun (congrFun h1 x) j
      rw [mul_T] at h2
      simpa using h2
    have hZp : ∀ j, Z * p j = 0 := by
      intro j
      have h3 : E j (bb E j) * E (bb E j) j = p j := by
        rw [(hM.2.2.2.2.1 j (bb E j) j (bb_ne hp hM j) (bb_spec hp hM j).2).1, hM.2.1 j]
      rw [← h3, ← mul_assoc, hZE j, zero_mul]
    calc Z = Z * ∑ j, p j := by rw [hp.1.complete, mul_one]
      _ = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun j _ => hZp j

end LateralTheory.DivDb.RepPf

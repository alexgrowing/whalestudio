import Mathlib

namespace GroundTheory.Automorphic

open Matrix DoubleCoset

variable {n : ℕ} {k : Type*} [Field k]

variable (n k) in

def borel : Subgroup (GL (Fin n) k) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) k).IsUpperTriangular}
  mul_mem' {a b} ha hb := by
    show ((a * b : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).IsUpperTriangular
    rw [Units.val_mul]
    exact BlockTriangular.mul ha hb
  one_mem' := by
    show ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).IsUpperTriangular
    rw [Units.val_one]
    exact blockTriangular_one
  inv_mem' {a} ha := by
    show ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).IsUpperTriangular
    rw [Matrix.coe_units_inv]
    let _ := (Units.isUnit a).invertible
    exact blockTriangular_inv_of_blockTriangular ha

lemma mem_borel_iff (g : GL (Fin n) k) :
    g ∈ borel n k ↔ ∀ i j : Fin n, j < i → (g : Matrix (Fin n) (Fin n) k) i j = 0 :=
  Iff.rfl

variable (k) in

noncomputable def permGL : Equiv.Perm (Fin n) →* GL (Fin n) k :=
  (Matrix.permMatrixHom (n := Fin n) (R := k)).toHomUnits

lemma permGL_apply (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (permGL k σ : Matrix (Fin n) (Fin n) k) i j = if i = σ j then 1 else 0 := by
  simp only [permGL, MonoidHom.coe_toHomUnits, permMatrixHom_apply, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Equiv.Perm.inv_eq_iff_eq]

lemma mul_permGL_apply (M : Matrix (Fin n) (Fin n) k) (σ : Equiv.Perm (Fin n)) (r c : Fin n) :
    (M * (permGL k σ : Matrix (Fin n) (Fin n) k)) r c = M r (σ c) := by
  simp [mul_apply, permGL_apply]

lemma permGL_mul_apply (M : Matrix (Fin n) (Fin n) k) (σ : Equiv.Perm (Fin n)) (r c : Fin n) :
    ((permGL k σ : Matrix (Fin n) (Fin n) k) * M) r c = M (σ⁻¹ r) c := by
  rw [mul_apply, Fintype.sum_eq_single (σ⁻¹ r)]
  · simp [permGL_apply]
  · intro a ha
    rw [permGL_apply, if_neg, zero_mul]
    rintro rfl
    exact ha (by simp)

lemma borel_diag_ne_zero {b : GL (Fin n) k} (hb : b ∈ borel n k) (i : Fin n) :
    (b : Matrix (Fin n) (Fin n) k) i i ≠ 0 := by
  have hdet : (b : Matrix (Fin n) (Fin n) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
  rw [det_of_isUpperTriangular hb] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)

lemma exists_borel_of_isUpperTriangular (M : Matrix (Fin n) (Fin n) k)
    (hM : M.IsUpperTriangular) (hd : ∀ i, M i i ≠ 0) :
    ∃ b ∈ borel n k, (b : Matrix (Fin n) (Fin n) k) = M := by
  have hdet : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, det_of_isUpperTriangular hM, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i
  obtain ⟨u, hu⟩ := hdet
  refine ⟨u, ?_, hu⟩
  show (u : Matrix (Fin n) (Fin n) k).IsUpperTriangular
  rw [hu]
  exact hM

lemma mul_one_add_vecMulVec_apply (M : Matrix (Fin n) (Fin n) k) (j : Fin n) (v : Fin n → k)
    (r c : Fin n) :
    (M * (1 + vecMulVec (Pi.single j 1) v)) r c = M r c + M r j * v c := by
  simp [Matrix.mul_add, mul_vecMulVec, vecMulVec_apply]

lemma one_add_vecMulVec_mul_apply (M : Matrix (Fin n) (Fin n) k) (i : Fin n) (u : Fin n → k)
    (r c : Fin n) :
    ((1 + vecMulVec u (Pi.single i 1)) * M) r c = M r c + u r * M i c := by
  simp [Matrix.add_mul, vecMulVec_mul, vecMulVec_apply]

lemma perm_eq_one_of_forall_le (π : Equiv.Perm (Fin n)) (h : ∀ x, π x ≤ x) : π = 1 := by
  have hsum : ∑ x, ((π x : Fin n) : ℕ) = ∑ x : Fin n, (x : ℕ) :=
    Equiv.sum_comp π (fun x : Fin n => (x : ℕ))
  have heq := (Finset.sum_eq_sum_iff_of_le
    (fun x _ => Fin.le_iff_val_le_val.mp (h x))).mp hsum
  exact Equiv.ext fun x => by simpa using Fin.ext (heq x (Finset.mem_univ _))

def RowsReduced (M : Matrix (Fin n) (Fin n) k) (t : ℕ) : Prop :=
  ∃ p : Fin n → Fin n, ∀ i : Fin n, t ≤ i.val →
    M i (p i) ≠ 0 ∧ (∀ c, c ≠ p i → M i c = 0) ∧ (∀ r, r ≠ i → M r (p i) = 0)

lemma rowsReduced_step (h : GL (Fin n) k) (t : ℕ) (ht : t < n)
    (hred : RowsReduced (h : Matrix (Fin n) (Fin n) k) (t + 1)) :
    ∃ b₁ ∈ borel n k, ∃ b₂ ∈ borel n k,
      RowsReduced ((b₁ * h * b₂ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) t := by
  classical
  obtain ⟨p, hp⟩ := hred
  set H : Matrix (Fin n) (Fin n) k := (h : Matrix (Fin n) (Fin n) k) with hH
  set i₀ : Fin n := ⟨t, ht⟩ with hi₀
  have hne : ∀ i : Fin n, t + 1 ≤ i.val → i₀ ≠ i := by
    intro i hi e
    have := congrArg Fin.val e
    simp [i₀] at this
    omega

  have hrow : ∃ c, H i₀ c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit).ne_zero
      (Matrix.det_eq_zero_of_row_eq_zero i₀ hcon)

  set s := Finset.univ.filter (fun c => H i₀ c ≠ 0) with hs_def
  have hs : s.Nonempty := let ⟨c, hc⟩ := hrow; ⟨c, by simp [s, hc]⟩
  set j := s.min' hs with hj_def
  have hj : H i₀ j ≠ 0 := (Finset.mem_filter.mp (s.min'_mem hs)).2
  have hjmin : ∀ c, c < j → H i₀ c = 0 := fun c hc => by
    by_contra hc0
    exact absurd (s.min'_le c (by simp [s, hc0])) (not_le.mpr hc)
  have hpS : ∀ i : Fin n, t + 1 ≤ i.val → H i₀ (p i) = 0 :=
    fun i hi => (hp i hi).2.2 i₀ (hne i hi)
  have hjp : ∀ i : Fin n, t + 1 ≤ i.val → p i ≠ j := fun i hi e => hj (e ▸ hpS i hi)
  have hHj : ∀ r : Fin n, t + 1 ≤ r.val → H r j = 0 :=
    fun r hr => (hp r hr).2.1 j (hjp r hr).symm

  set v : Fin n → k := fun c => if j < c then -(H i₀ c / H i₀ j) else 0 with hv
  set E₂ : Matrix (Fin n) (Fin n) k := 1 + vecMulVec (Pi.single j 1) v with hE₂
  have hE₂up : E₂.IsUpperTriangular := by
    intro a c hca
    replace hca : c < a := hca
    simp only [E₂, Matrix.add_apply, one_apply, vecMulVec_apply, Pi.single_apply]
    rw [if_neg (ne_of_lt hca).symm]
    by_cases haj : a = j
    · subst haj
      simp [v, not_lt.mpr hca.le]
    · simp [haj]
  have hE₂d : ∀ a, E₂ a a ≠ 0 := by
    intro a
    simp only [E₂, Matrix.add_apply, one_apply_eq, vecMulVec_apply, Pi.single_apply]
    by_cases haj : a = j
    · subst haj; simp [v]
    · simp [haj]
  obtain ⟨b₂, hb₂, hb₂E⟩ := exists_borel_of_isUpperTriangular E₂ hE₂up hE₂d
  set M₁ : Matrix (Fin n) (Fin n) k := H * E₂ with hM₁_def
  have hM₁ : ∀ r c, M₁ r c = H r c + H r j * v c := fun r c =>
    mul_one_add_vecMulVec_apply H j v r c
  have hM₁i₀ : ∀ c, M₁ i₀ c = if c = j then H i₀ j else 0 := by
    intro c
    rw [hM₁]
    rcases lt_trichotomy c j with hc | rfl | hc
    · simp [v, hjmin c hc, not_lt.mpr hc.le, (ne_of_lt hc)]
    · simp [v]
    · simp only [v, if_pos hc, if_neg (ne_of_lt hc).symm]
      field_simp
      ring
  have hM₁S : ∀ r : Fin n, t + 1 ≤ r.val → ∀ c, M₁ r c = H r c := by
    intro r hr c
    rw [hM₁, hHj r hr, zero_mul, add_zero]
  have hvp : ∀ i : Fin n, t + 1 ≤ i.val → v (p i) = 0 := by
    intro i hi
    simp [v, hpS i hi]

  set u : Fin n → k := fun r => if r < i₀ then -(M₁ r j / H i₀ j) else 0 with hu_def
  set E₁ : Matrix (Fin n) (Fin n) k := 1 + vecMulVec u (Pi.single i₀ 1) with hE₁
  have hE₁up : E₁.IsUpperTriangular := by
    intro a c hca
    replace hca : c < a := hca
    simp only [E₁, Matrix.add_apply, one_apply, vecMulVec_apply, Pi.single_apply]
    rw [if_neg (ne_of_lt hca).symm]
    by_cases hci : c = i₀
    · subst hci
      simp [u, not_lt.mpr hca.le]
    · simp [hci]
  have hE₁d : ∀ a, E₁ a a ≠ 0 := by
    intro a
    simp only [E₁, Matrix.add_apply, one_apply_eq, vecMulVec_apply, Pi.single_apply]
    by_cases hai : a = i₀
    · subst hai; simp [u]
    · simp [hai]
  obtain ⟨b₁, hb₁, hb₁E⟩ := exists_borel_of_isUpperTriangular E₁ hE₁up hE₁d
  set M₂ : Matrix (Fin n) (Fin n) k := E₁ * M₁ with hM₂_def
  have hM₂ : ∀ r c, M₂ r c = M₁ r c + u r * M₁ i₀ c := fun r c =>
    one_add_vecMulVec_mul_apply M₁ i₀ u r c
  have hu0 : ∀ r : Fin n, t ≤ r.val → u r = 0 := by
    intro r hr
    have : ¬ r < i₀ := by
      rw [Fin.lt_def]
      simp [i₀]
      omega
    simp [u, this]
  have hM₂j : ∀ r : Fin n, r.val < t → M₂ r j = 0 := by
    intro r hr
    have hlt : r < i₀ := by
      rw [Fin.lt_def]
      simpa [i₀] using hr
    rw [hM₂, hM₁i₀ j, if_pos rfl]
    simp only [u, if_pos hlt]
    field_simp
    ring
  have hval : ((b₁ * h * b₂ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = M₂ := by
    rw [Units.val_mul, Units.val_mul, hb₁E, hb₂E, mul_assoc]
  refine ⟨b₁, hb₁, b₂, hb₂, ?_⟩
  rw [hval]
  refine ⟨Function.update p i₀ j, fun i hi => ?_⟩
  rcases Nat.eq_or_lt_of_le hi with hti | hti
  ·
    have hii : i = i₀ := Fin.ext (by simp [i₀, hti])
    subst hii
    rw [Function.update_self]
    refine ⟨?_, ?_, ?_⟩
    · rw [hM₂, hu0 _ le_rfl, zero_mul, add_zero, hM₁i₀, if_pos rfl]
      exact hj
    · intro c hc
      rw [hM₂, hu0 _ le_rfl, zero_mul, add_zero, hM₁i₀, if_neg hc]
    · intro r hr
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hr) with hlt | hgt
      · exact hM₂j r (by simpa [i₀] using hlt)
      · have hr' : t + 1 ≤ r.val := by simp [i₀] at hgt; omega
        rw [hM₂, hu0 r (by omega), zero_mul, add_zero, hM₁S r hr', hHj r hr']
  ·
    have hi' : t + 1 ≤ i.val := hti
    rw [Function.update_of_ne (hne i hi').symm]
    obtain ⟨h1, h2, h3⟩ := hp i hi'
    refine ⟨?_, ?_, ?_⟩
    · rw [hM₂, hu0 i hi, zero_mul, add_zero, hM₁S i hi']
      exact h1
    · intro c hc
      rw [hM₂, hu0 i hi, zero_mul, add_zero, hM₁S i hi']
      exact h2 c hc
    · intro r hr
      rw [hM₂, hM₁i₀, if_neg (hjp i hi'), mul_zero, add_zero, hM₁, hvp i hi', mul_zero,
        add_zero]
      exact h3 r hr

lemma exists_eq_mul_permGL_of_rowsReduced (g : GL (Fin n) k)
    (hred : RowsReduced (g : Matrix (Fin n) (Fin n) k) 0) :
    ∃ σ : Equiv.Perm (Fin n), ∃ b ∈ borel n k, g = b * permGL k σ := by
  classical
  obtain ⟨p, hp⟩ := hred
  have hinj : Function.Injective p := by
    intro i i' e
    by_contra hii
    exact (hp i' (Nat.zero_le _)).1 (e ▸ (hp i (Nat.zero_le _)).2.2 i' (Ne.symm hii))
  set τ : Equiv.Perm (Fin n) := Equiv.ofBijective p (Finite.injective_iff_bijective.mp hinj)
  have hτ : ∀ i, τ i = p i := fun i => rfl
  set d : Fin n → k := fun i => (g : Matrix (Fin n) (Fin n) k) i (p i)
  obtain ⟨b, hb, hbD⟩ := exists_borel_of_isUpperTriangular (diagonal d)
    (blockTriangular_diagonal d) (fun i => by simpa [d] using (hp i (Nat.zero_le _)).1)
  refine ⟨τ⁻¹, b, hb, ?_⟩
  ext r c
  rw [Units.val_mul, mul_permGL_apply, hbD, diagonal_apply]
  by_cases hc : c = p r
  · subst hc
    rw [if_pos (by rw [← hτ]; simp)]
  · rw [(hp r (Nat.zero_le _)).2.1 c hc, if_neg]
    intro e
    apply hc
    rw [← hτ, e]
    simp

theorem exists_mem_doubleCoset_permGL (g : GL (Fin n) k) :
    ∃ σ : Equiv.Perm (Fin n), g ∈ doubleCoset (permGL k σ) (borel n k) (borel n k) := by
  have key : ∀ d, d ≤ n → ∃ b₁ ∈ borel n k, ∃ b₂ ∈ borel n k,
      RowsReduced ((b₁ * g * b₂ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (n - d) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨1, (borel n k).one_mem, 1, (borel n k).one_mem, id, fun i hi => ?_⟩
      have := i.isLt
      omega
    | succ d ih =>
      intro hd
      obtain ⟨b₁, hb₁, b₂, hb₂, hred⟩ := ih (by omega)
      have ht : n - (d + 1) + 1 = n - d := by omega
      rw [← ht] at hred
      obtain ⟨c₁, hc₁, c₂, hc₂, hred'⟩ := rowsReduced_step _ (n - (d + 1)) (by omega) hred
      refine ⟨c₁ * b₁, (borel n k).mul_mem hc₁ hb₁, b₂ * c₂, (borel n k).mul_mem hb₂ hc₂, ?_⟩
      simpa only [mul_assoc] using hred'
  obtain ⟨b₁, hb₁, b₂, hb₂, hred⟩ := key n le_rfl
  rw [Nat.sub_self] at hred
  obtain ⟨σ, b, hb, hgb⟩ := exists_eq_mul_permGL_of_rowsReduced _ hred
  refine ⟨σ, mem_doubleCoset.mpr ⟨b₁⁻¹ * b, (borel n k).mul_mem ((borel n k).inv_mem hb₁) hb,
    b₂⁻¹, (borel n k).inv_mem hb₂, ?_⟩⟩
  rw [mul_assoc b₁⁻¹, ← hgb]
  group

theorem eq_of_permGL_mem_doubleCoset {σ τ : Equiv.Perm (Fin n)}
    (h : permGL k τ ∈ doubleCoset (permGL k σ) (borel n k) (borel n k)) : σ = τ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_doubleCoset.mp h
  have hy' : y⁻¹ ∈ borel n k := (borel n k).inv_mem hy
  have hmat : (x : Matrix (Fin n) (Fin n) k) * (permGL k σ : Matrix (Fin n) (Fin n) k) =
      (permGL k τ : Matrix (Fin n) (Fin n) k) * ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    rw [← Units.val_mul, ← Units.val_mul, hxy]
    congr 1
    group
  have hle : ∀ a, τ a ≤ σ a := by
    intro a
    have hent := congrFun (congrFun hmat (τ a)) a
    rw [mul_permGL_apply, permGL_mul_apply] at hent
    by_contra hlt
    push Not at hlt
    have h0 := (mem_borel_iff x).mp hx (τ a) (σ a) hlt
    rw [hent, show τ⁻¹ (τ a) = a from τ.symm_apply_apply a] at h0
    exact borel_diag_ne_zero hy' a h0
  have hπ := perm_eq_one_of_forall_le (τ * σ⁻¹) (fun x => by
    simpa using hle (σ⁻¹ x))
  have := congrArg (· * σ) hπ
  simpa using this.symm

theorem doubleCoset_permGL_injective {σ τ : Equiv.Perm (Fin n)} {g : GL (Fin n) k}
    (hσ : g ∈ doubleCoset (permGL k σ) (borel n k) (borel n k))
    (hτ : g ∈ doubleCoset (permGL k τ) (borel n k) (borel n k)) : σ = τ := by
  have e : doubleCoset (permGL k σ) (borel n k) (borel n k) =
      doubleCoset (permGL k τ) (borel n k) (borel n k) :=
    (doubleCoset_eq_of_mem hσ).symm.trans (doubleCoset_eq_of_mem hτ)
  have hmem := mem_doubleCoset_self (borel n k) (borel n k) (permGL k τ)
  rw [← e] at hmem
  exact eq_of_permGL_mem_doubleCoset hmem

theorem bruhat_decomposition (g : GL (Fin n) k) :
    ∃! σ : Equiv.Perm (Fin n), g ∈ doubleCoset (permGL k σ) (borel n k) (borel n k) := by
  obtain ⟨σ, hσ⟩ := exists_mem_doubleCoset_permGL g
  exact ⟨σ, hσ, fun τ hτ => (doubleCoset_permGL_injective hσ hτ).symm⟩

theorem iUnion_doubleCoset_permGL :
    ⋃ σ : Equiv.Perm (Fin n), doubleCoset (permGL k σ) (borel n k) (borel n k) = Set.univ :=
  Set.eq_univ_of_forall fun g => Set.mem_iUnion.mpr (exists_mem_doubleCoset_permGL g)

theorem pairwise_disjoint_doubleCoset_permGL :
    Pairwise (Function.onFun Disjoint fun σ : Equiv.Perm (Fin n) =>
      doubleCoset (permGL k σ) (borel n k) (borel n k)) := by
  intro σ τ hστ
  rw [Function.onFun, Set.disjoint_left]
  intro g hσ hτ
  exact hστ (doubleCoset_permGL_injective hσ hτ)

theorem bijective_mk_permGL :
    Function.Bijective fun σ : Equiv.Perm (Fin n) =>
      DoubleCoset.mk (borel n k) (borel n k) (permGL k σ) := by
  constructor
  · intro σ τ hστ
    obtain ⟨x, hx, y, hy, hxy⟩ := (DoubleCoset.eq _ _ _ _).mp hστ
    exact eq_of_permGL_mem_doubleCoset (mem_doubleCoset.mpr ⟨x, hx, y, hy, hxy⟩)
  · intro q
    obtain ⟨σ, hσ⟩ := exists_mem_doubleCoset_permGL (k := k) q.out
    refine ⟨σ, ?_⟩
    simp only
    rw [← mk_eq_of_doubleCoset_eq (doubleCoset_eq_of_mem hσ), out_eq']

theorem permGL_injective : Function.Injective (permGL k : Equiv.Perm (Fin n) → GL (Fin n) k) := by
  intro σ τ h
  apply eq_of_permGL_mem_doubleCoset (k := k)
  rw [← h]
  exact mem_doubleCoset_self _ _ _

end GroundTheory.Automorphic

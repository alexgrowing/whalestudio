import Mathlib

open scoped Classical

noncomputable def UpperTheory.Reformulated.B.Qf33.blk :
    {α n : Type} → {m : α → Type} → (a : α) × m a ≃ n → n → α :=
    fun {α n : Type} {m : α → Type} (e : (a : α) × m a ≃ n) (i : n) ↦ ((e.symm : n → (a : α) × m a) i).fst

theorem UpperTheory.Reformulated.B.Qf33.aux2 :
    ∀ (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
      [inst_3 : DecidableEq n] (e : (a : α) × m a ≃ n) {x y : GL n R},
      x ∈ {g : GL n R | (↑g : Matrix n n R).BlockTriangular (UpperTheory.Reformulated.B.Qf33.blk e)} →
        y ∈ {g : GL n R | (↑g : Matrix n n R).BlockTriangular (UpperTheory.Reformulated.B.Qf33.blk e)} →
          x * y ∈ {g : GL n R | (↑g : Matrix n n R).BlockTriangular (UpperTheory.Reformulated.B.Qf33.blk e)} := by
  intro R _ α n m _ _ _ e x y hx hy
  exact Matrix.BlockTriangular.mul hx hy

theorem UpperTheory.Reformulated.B.Qf33.aux3 :
    ∀ (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
      [inst_3 : DecidableEq n] (e : (a : α) × m a ≃ n),
      (1 : GL n R) ∈ {g : GL n R | (↑g : Matrix n n R).BlockTriangular (UpperTheory.Reformulated.B.Qf33.blk e)} := by
  intro R _ α n m _ _ _ e
  exact Matrix.blockTriangular_one

theorem UpperTheory.Reformulated.B.Qf33.aux4 :
    ∀ (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
      [inst_3 : DecidableEq n] (e : (a : α) × m a ≃ n) {x : GL n R},
      x ∈ {g : GL n R | (↑g : Matrix n n R).BlockTriangular (UpperTheory.Reformulated.B.Qf33.blk e)} →
        x⁻¹ ∈ {g : GL n R | (↑g : Matrix n n R).BlockTriangular (UpperTheory.Reformulated.B.Qf33.blk e)} := by
  intro R _ α n m _ _ _ e x hx
  have h : ((x⁻¹ : GL n R) : Matrix n n R) = (x : Matrix n n R)⁻¹ := Matrix.coe_units_inv x
  change ((x⁻¹ : GL n R) : Matrix n n R).BlockTriangular _
  rw [h]
  letI : Invertible (x : Matrix n n R) := x.invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular hx

noncomputable def UpperTheory.Reformulated.B.Qf33.parab :
    (R : Type) →
      [inst : CommRing R] →
        {α n : Type} →
          {m : α → Type} →
            [LinearOrder α] → [inst_2 : Fintype n] → [inst_3 : DecidableEq n] → (a : α) × m a ≃ n → Subgroup (GL n R) :=
    fun (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
        [inst_3 : DecidableEq n] (e : (a : α) × m a ≃ n) ↦
      { carrier := {g : GL n R | (↑g : Matrix n n R).BlockTriangular (UpperTheory.Reformulated.B.Qf33.blk e)},
        mul_mem' := @UpperTheory.Reformulated.B.Qf33.aux2 R inst α n m inst_1 inst_2 inst_3 e, one_mem' := UpperTheory.Reformulated.B.Qf33.aux3 R e,
        inv_mem' := @UpperTheory.Reformulated.B.Qf33.aux4 R inst α n m inst_1 inst_2 inst_3 e : Subgroup (GL n R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qf33.Levi :
    (R : Type) →
      [CommRing R] → {α : Type} → (m : α → Type) → [(a : α) → Fintype (m a)] → [(a : α) → DecidableEq (m a)] → Type :=
    fun (R : Type) [CommRing R] {α : Type} (m : α → Type) [(a : α) → Fintype (m a)] [(a : α) → DecidableEq (m a)] ↦
      (a : α) → GL (m a) R

theorem UpperTheory.Reformulated.B.Qf33.aux7 :
    ∀ (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : (a : α) → Fintype (m a)]
      [inst_3 : (a : α) → DecidableEq (m a)] [inst_4 : Fintype n] [inst_5 : DecidableEq n] (e : (a : α) × m a ≃ n) (a : α),
      ((↑(↑(1 : ↥(UpperTheory.Reformulated.B.Qf33.parab R e)) : GL n R) : Matrix n n R).submatrix
          (fun (i : m a) ↦ (e : (a : α) × m a → n) (⟨a, i⟩ : (a : α) × m a)) fun (i : m a) ↦
          (e : (a : α) × m a → n) (⟨a, i⟩ : (a : α) × m a)) =
        (1 : Matrix (m a) (m a) R) := by
  intro R _ α n m _ _ _ _ _ e a
  refine Matrix.submatrix_one _ ?_
  intro i j h
  exact sigma_mk_injective (e.injective h)

theorem UpperTheory.Reformulated.B.Qf33.aux8 :
    ∀ (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [Fintype α] [inst_2 : LinearOrder α]
      [inst_3 : (a : α) → Fintype (m a)] [inst_4 : (a : α) → DecidableEq (m a)] [inst_5 : Fintype n]
      [inst_6 : DecidableEq n] (e : (a : α) × m a ≃ n) (a : α) (x y : ↥(UpperTheory.Reformulated.B.Qf33.parab R e)),
      ((↑(↑(x * y) : GL n R) : Matrix n n R).submatrix (fun (i : m a) ↦ (e : (a : α) × m a → n) (⟨a, i⟩ : (a : α) × m a))
          fun (i : m a) ↦ (e : (a : α) × m a → n) (⟨a, i⟩ : (a : α) × m a)) =
        ((↑(↑x : GL n R) : Matrix n n R).submatrix (fun (i : m a) ↦ (e : (a : α) × m a → n) (⟨a, i⟩ : (a : α) × m a))
            fun (i : m a) ↦ (e : (a : α) × m a → n) (⟨a, i⟩ : (a : α) × m a)) *
          (↑(↑y : GL n R) : Matrix n n R).submatrix (fun (i : m a) ↦ (e : (a : α) × m a → n) (⟨a, i⟩ : (a : α) × m a))
            fun (i : m a) ↦ (e : (a : α) × m a → n) (⟨a, i⟩ : (a : α) × m a) := by
  intro R _ α n m _ _ _ _ _ _ e a x y
  ext i j
  have hx : (↑(↑x : GL n R) : Matrix n n R).BlockTriangular (UpperTheory.Reformulated.B.Qf33.blk e) := x.2
  have hy : (↑(↑y : GL n R) : Matrix n n R).BlockTriangular (UpperTheory.Reformulated.B.Qf33.blk e) := y.2
  simp only [Subgroup.coe_mul, Units.val_mul, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← e.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single a]
  · intro b _ hb
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rcases lt_or_gt_of_ne hb with h | h
    · rw [hx (by simpa [UpperTheory.Reformulated.B.Qf33.blk] using h), zero_mul]
    · rw [hy (i := e ⟨b, k⟩) (by simpa [UpperTheory.Reformulated.B.Qf33.blk] using h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

noncomputable def UpperTheory.Reformulated.B.Qf33.diagBlock :
    (R : Type) →
      [inst : CommRing R] →
        {α n : Type} →
          {m : α → Type} →
            [Fintype α] →
              [inst_2 : LinearOrder α] →
                [inst_3 : (a : α) → Fintype (m a)] →
                  [inst_4 : (a : α) → DecidableEq (m a)] →
                    [inst_5 : Fintype n] →
                      [inst_6 : DecidableEq n] →
                        (e : (a : α) × m a ≃ n) → (a : α) → ↥(UpperTheory.Reformulated.B.Qf33.parab R e) →* Matrix (m a) (m a) R :=
    fun (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [(a : α) → Fintype (m a)]
        [(a : α) → DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (a : α) × m a ≃ n) (a : α) ↦
      {
        toFun := fun (p : ↥(UpperTheory.Reformulated.B.Qf33.parab R e)) ↦
          (↑(↑p : GL n R) : Matrix n n R).submatrix (fun (i : m a) ↦ (e : (a : α) × m a → n) (⟨a, i⟩ : (a : α) × m a))
            fun (i : m a) ↦ (e : (a : α) × m a → n) (⟨a, i⟩ : (a : α) × m a),
        map_one' := UpperTheory.Reformulated.B.Qf33.aux7 R e a, map_mul' := UpperTheory.Reformulated.B.Qf33.aux8 R e a :
        ↥(UpperTheory.Reformulated.B.Qf33.parab R e) →* Matrix (m a) (m a) R }

noncomputable def UpperTheory.Reformulated.B.Qf33.leviProj :
    (R : Type) →
      [inst : CommRing R] →
        {α n : Type} →
          {m : α → Type} →
            [Fintype α] →
              [inst_2 : LinearOrder α] →
                [inst_3 : (a : α) → Fintype (m a)] →
                  [inst_4 : (a : α) → DecidableEq (m a)] →
                    [inst_5 : Fintype n] →
                      [inst_6 : DecidableEq n] →
                        (e : (a : α) × m a ≃ n) → ↥(UpperTheory.Reformulated.B.Qf33.parab R e) →* UpperTheory.Reformulated.B.Qf33.Levi R m :=
    fun (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [(a : α) → Fintype (m a)]
        [(a : α) → DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (a : α) × m a ≃ n) ↦
      MonoidHom.pi fun (a : α) ↦ (UpperTheory.Reformulated.B.Qf33.diagBlock R e a).toHomUnits

noncomputable def UpperTheory.Reformulated.B.Qf33.unipRad :
    (R : Type) →
      [inst : CommRing R] →
        {α n : Type} →
          {m : α → Type} →
            [Fintype α] →
              [LinearOrder α] →
                [(a : α) → Fintype (m a)] →
                  [(a : α) → DecidableEq (m a)] →
                    [inst_5 : Fintype n] → [inst_6 : DecidableEq n] → (a : α) × m a ≃ n → Subgroup (GL n R) :=
    fun (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [(a : α) → Fintype (m a)]
        [(a : α) → DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (a : α) × m a ≃ n) ↦
      Subgroup.map (UpperTheory.Reformulated.B.Qf33.parab R e).subtype (UpperTheory.Reformulated.B.Qf33.leviProj R e).ker

noncomputable def UpperTheory.Reformulated.B.Qf33.opp :
    {α n : Type} → {m : α → Type} → (a : α) × m a ≃ n → (a : αᵒᵈ) × m ((OrderDual.ofDual : αᵒᵈ → α) a) ≃ n :=
    fun {α n : Type} {m : α → Type} (e : (a : α) × m a ≃ n) ↦ e

noncomputable def UpperTheory.Reformulated.B.Qf33.unipRadLower :
    (R : Type) →
      [inst : CommRing R] →
        {α n : Type} →
          {m : α → Type} →
            [Fintype α] →
              [LinearOrder α] →
                [(a : α) → Fintype (m a)] →
                  [(a : α) → DecidableEq (m a)] →
                    [inst_5 : Fintype n] → [inst_6 : DecidableEq n] → (a : α) × m a ≃ n → Subgroup (GL n R) :=
    fun (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [(a : α) → Fintype (m a)]
        [(a : α) → DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (a : α) × m a ≃ n) ↦
      UpperTheory.Reformulated.B.Qf33.unipRad R (UpperTheory.Reformulated.B.Qf33.opp e)

theorem UpperTheory.Reformulated.B.Qf33.zero_contDiffOn_supported :
    ∀ (R : Type) [inst : CommRing R] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] {α : Type} {m : α → Type}
      [inst_3 : (a : α) → Fintype (m a)] [inst_4 : (a : α) → DecidableEq (m a)] (e : (a : α) × m a ≃ n),
      (Matrix.reindex e e : Matrix ((a : α) × m a) ((a : α) × m a) R → Matrix n n R)
          (Matrix.blockDiagonal' fun (a : α) ↦ (↑((1 : UpperTheory.Reformulated.B.Qf33.Levi R m) a) : Matrix (m a) (m a) R)) =
        (1 : Matrix n n R) := by
  intro R _ n _ _ α m _ _ e
  have h : (fun (a : α) ↦ (↑((1 : UpperTheory.Reformulated.B.Qf33.Levi R m) a) : Matrix (m a) (m a) R)) = 1 := rfl
  rw [h, Matrix.blockDiagonal'_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem UpperTheory.Reformulated.B.Qf33.sign_action_map_comm :
    ∀ (R : Type) [inst : CommRing R] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] {α : Type} {m : α → Type}
      [Fintype α] [inst_4 : (a : α) → Fintype (m a)] [inst_5 : (a : α) → DecidableEq (m a)] (e : (a : α) × m a ≃ n)
      (g h : UpperTheory.Reformulated.B.Qf33.Levi R m),
      (Matrix.reindex e e : Matrix ((a : α) × m a) ((a : α) × m a) R → Matrix n n R)
          (Matrix.blockDiagonal' fun (a : α) ↦ (↑((g * h) a) : Matrix (m a) (m a) R)) =
        (Matrix.reindex e e : Matrix ((a : α) × m a) ((a : α) × m a) R → Matrix n n R)
            (Matrix.blockDiagonal' fun (a : α) ↦ (↑(g a) : Matrix (m a) (m a) R)) *
          (Matrix.reindex e e : Matrix ((a : α) × m a) ((a : α) × m a) R → Matrix n n R)
            (Matrix.blockDiagonal' fun (a : α) ↦ (↑(h a) : Matrix (m a) (m a) R)) := by
  intro R _ n _ _ α m _ _ _ e g h
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Pi.mul_apply, Units.val_mul]
  rw [← Matrix.blockDiagonal'_mul]

noncomputable def UpperTheory.Reformulated.B.Qf33.leviEmb :
    (R : Type) →
      [inst : CommRing R] →
        {n : Type} →
          [inst_1 : Fintype n] →
            [inst_2 : DecidableEq n] →
              {α : Type} →
                {m : α → Type} →
                  [Fintype α] →
                    [inst_4 : (a : α) → Fintype (m a)] →
                      [inst_5 : (a : α) → DecidableEq (m a)] → (a : α) × m a ≃ n → UpperTheory.Reformulated.B.Qf33.Levi R m →* GL n R :=
    fun (R : Type) [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {α : Type} {m : α → Type} [Fintype α]
        [(a : α) → Fintype (m a)] [(a : α) → DecidableEq (m a)] (e : (a : α) × m a ≃ n) ↦
      {
          toFun := fun (g : UpperTheory.Reformulated.B.Qf33.Levi R m) ↦
            (Matrix.reindex e e : Matrix ((a : α) × m a) ((a : α) × m a) R → Matrix n n R)
              (Matrix.blockDiagonal' fun (a : α) ↦ (↑(g a) : Matrix (m a) (m a) R)),
          map_one' := UpperTheory.Reformulated.B.Qf33.zero_contDiffOn_supported R e, map_mul' := UpperTheory.Reformulated.B.Qf33.sign_action_map_comm R e :
          UpperTheory.Reformulated.B.Qf33.Levi R m →* Matrix n n R }.toHomUnits

private theorem rad_spec {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [(a : α) → Fintype (m a)] [(a : α) → DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (a : α) × m a ≃ n) {g : GL n R} (hg : g ∈ UpperTheory.Reformulated.B.Qf33.unipRad R e) :
    (g : Matrix n n R).BlockTriangular (UpperTheory.Reformulated.B.Qf33.blk e) ∧
      ∀ (a : α) (i j : m a), (g : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) R) i j := by
  obtain ⟨p, hp, rfl⟩ := hg
  refine ⟨p.2, fun a i j ↦ ?_⟩
  have h1 : UpperTheory.Reformulated.B.Qf33.leviProj R e p = 1 := hp
  have h2 := congrArg Units.val (congrFun h1 a)
  exact congrFun (congrFun h2 i) j

private theorem levi_off {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α]
    [(a : α) → Fintype (m a)] [(a : α) → DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (a : α) × m a ≃ n) {g : GL n R} (hg : g ∈ (UpperTheory.Reformulated.B.Qf33.leviEmb R e).range) {i j : n}
    (hij : UpperTheory.Reformulated.B.Qf33.blk e i ≠ UpperTheory.Reformulated.B.Qf33.blk e j) : (g : Matrix n n R) i j = 0 := by
  obtain ⟨l, rfl⟩ := hg
  exact Matrix.blockDiagonal'_apply_ne (fun (a : α) ↦ (↑(l a) : Matrix (m a) (m a) R))
    (e.symm i).2 (e.symm j).2 hij

private theorem eq_one_of_blocks {R : Type} [CommRing R] {α n : Type} {m : α → Type}
    [(a : α) → DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (a : α) × m a ≃ n) {g : GL n R}
    (h0 : ∀ i j, UpperTheory.Reformulated.B.Qf33.blk e i ≠ UpperTheory.Reformulated.B.Qf33.blk e j → (g : Matrix n n R) i j = 0)
    (h1 : ∀ (a : α) (i j : m a), (g : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) R) i j) :
    g = 1 := by
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  by_cases hab : a = b
  · subst hab
    rw [h1]
    simp [Matrix.one_apply]
  · rw [h0 _ _ (by simpa [UpperTheory.Reformulated.B.Qf33.blk] using hab)]
    simp [Matrix.one_apply, hab]

theorem UpperTheory.Reformulated.B.Qf33.uniq :
    ∀ {R : Type} [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : Fintype α] [inst_2 : LinearOrder α]
      [inst_3 : (a : α) → Fintype (m a)] [inst_4 : (a : α) → DecidableEq (m a)] [inst_5 : Fintype n]
      [inst_6 : DecidableEq n] {e : (a : α) × m a ≃ n},
      ∀ a ∈ UpperTheory.Reformulated.B.Qf33.unipRadLower R e,
        ∀ a' ∈ UpperTheory.Reformulated.B.Qf33.unipRadLower R e,
          ∀ b ∈ (UpperTheory.Reformulated.B.Qf33.leviEmb R e).range,
            ∀ b' ∈ (UpperTheory.Reformulated.B.Qf33.leviEmb R e).range,
              ∀ c ∈ UpperTheory.Reformulated.B.Qf33.unipRad R e,
                ∀ c' ∈ UpperTheory.Reformulated.B.Qf33.unipRad R e, a * b * c = a' * b' * c' → a = a' ∧ b = b' ∧ c = c' := by
  intro R _ α n m _ _ _ _ _ _ e a ha a' ha' b hb b' hb' c hc c' hc' h
  have h1 : a'⁻¹ * a = b' * c' * (b * c)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, ← mul_assoc, ← mul_assoc, h]
  have hP : ∀ x ∈ (UpperTheory.Reformulated.B.Qf33.leviEmb R e).range, x ∈ UpperTheory.Reformulated.B.Qf33.parab R e :=
    fun x hx i j hij ↦ levi_off e hx hij.ne'
  have hU : ∀ x ∈ UpperTheory.Reformulated.B.Qf33.unipRad R e, x ∈ UpperTheory.Reformulated.B.Qf33.parab R e :=
    fun x hx ↦ (rad_spec e hx).1
  have h2 : a'⁻¹ * a ∈ UpperTheory.Reformulated.B.Qf33.parab R e := by
    rw [h1]
    exact mul_mem (mul_mem (hP _ hb') (hU _ hc')) (inv_mem (mul_mem (hP _ hb) (hU _ hc)))
  have h3 : a'⁻¹ * a ∈ UpperTheory.Reformulated.B.Qf33.unipRad R (UpperTheory.Reformulated.B.Qf33.opp e) := mul_mem (inv_mem ha') ha
  have h4 : a'⁻¹ * a = 1 := by
    obtain ⟨ht, hd⟩ := rad_spec _ h3
    refine eq_one_of_blocks e (fun i j hij ↦ ?_) hd
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact ht hlt
    · exact h2 hlt
  have haa : a = a' := (inv_mul_eq_one.mp h4).symm
  subst haa
  have h5 : b * c = b' * c' := by
    rw [mul_assoc, mul_assoc] at h
    exact mul_left_cancel h
  have h6 : b'⁻¹ * b = c' * c⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, h5]
  have h7 : b'⁻¹ * b = 1 := by
    refine eq_one_of_blocks e (fun i j hij ↦ levi_off e (mul_mem (inv_mem hb') hb) hij) ?_
    rw [h6]
    exact (rad_spec e (mul_mem hc' (inv_mem hc))).2
  have hbb : b = b' := (inv_mul_eq_one.mp h7).symm
  subst hbb
  exact ⟨rfl, rfl, mul_left_cancel h5⟩

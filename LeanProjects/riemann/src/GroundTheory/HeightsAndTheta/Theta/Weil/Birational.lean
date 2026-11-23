import Mathlib

namespace GroundTheory.Heights₂.Theta

open scoped Pointwise

structure IsWeilCell {G : Type*} [Group G] (Ω : Set G) : Prop where

  inv_mem : ∀ x ∈ Ω, x⁻¹ ∈ Ω

  exists_mul_mem_left : ∀ s : Finset G, ∃ z : G, ∀ v ∈ s, z * v ∈ Ω

def IsMulOn {G M : Type*} [Mul G] [Mul M] (Ω : Set G) (R : G → M) : Prop :=
  ∀ x ∈ Ω, ∀ y ∈ Ω, x * y ∈ Ω → R x * R y = R (x * y)

section Inhabitant

theorem GL_two_inv_one_zero {K : Type*} [Field K] (g : GL (Fin 2) K)
    (h : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  have hm : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  have h10 := congrFun (congrFun hm 1) 0
  have h11 := congrFun (congrFun hm 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, h, zero_mul, zero_add, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h10 h11
  have hne : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h11; exact zero_ne_one h11
  exact (mul_eq_zero.mp h10).resolve_left hne

theorem GL_two_col_ne_zero {K : Type*} [Field K] (g : GL (Fin 2) K)
    (h0 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 0) : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
  intro h1
  have hm : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  have h00 := congrFun (congrFun hm 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, h0, h1] at h00

def bigCellGL2 (K : Type*) [Field K] : Set (GL (Fin 2) K) :=
  {g | (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0}

theorem one_notMem_bigCellGL2 (K : Type*) [Field K] : (1 : GL (Fin 2) K) ∉ bigCellGL2 K := by
  simp [bigCellGL2]

theorem exists_mem_bigCellGL2 (K : Type*) [Field K] :
    ∃ g : GL (Fin 2) K, g ∈ bigCellGL2 K := by
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two]), ?_⟩
  simp [bigCellGL2]

theorem isWeilCell_GL_two (K : Type*) [Field K] [Infinite K] : IsWeilCell (bigCellGL2 K) where
  inv_mem x hx := fun h => hx (GL_two_inv_one_zero x h)
  exists_mul_mem_left s := by
    classical
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset
      (s.image fun v : GL (Fin 2) K =>
        -(v : Matrix (Fin 2) (Fin 2) K) 1 0 / (v : Matrix (Fin 2) (Fin 2) K) 0 0)
    let z : GL (Fin 2) K :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; t, 1] (by simp [Matrix.det_fin_two])
    have hz : (z : Matrix (Fin 2) (Fin 2) K) = !![1, 0; t, 1] := rfl
    refine ⟨z, fun v hv => ?_⟩
    show ((z * v : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0
    rw [Matrix.GeneralLinearGroup.coe_mul, hz]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val',
      one_mul]
    by_cases h0 : (v : Matrix (Fin 2) (Fin 2) K) 0 0 = 0
    · rw [h0, mul_zero, zero_add]; exact GL_two_col_ne_zero v h0
    · intro hz
      apply ht
      refine Finset.mem_image.mpr ⟨v, hv, ?_⟩
      field_simp
      linear_combination -hz

end Inhabitant

namespace IsWeilCell

variable {G : Type*} [Group G] {Ω : Set G}

theorem inv_mem_iff (hΩ : IsWeilCell Ω) {x : G} : x⁻¹ ∈ Ω ↔ x ∈ Ω :=
  ⟨fun h => by simpa using hΩ.inv_mem _ h, hΩ.inv_mem x⟩

theorem exists_mul_mem_right (hΩ : IsWeilCell Ω) (s : Finset G) :
    ∃ t : G, ∀ v ∈ s, v * t ∈ Ω := by
  classical
  obtain ⟨z, hz⟩ := hΩ.exists_mul_mem_left (s.image (·⁻¹))
  refine ⟨z⁻¹, fun v hv => ?_⟩
  have := hΩ.inv_mem _ (hz v⁻¹ (Finset.mem_image_of_mem _ hv))
  simpa using this

theorem nonempty (hΩ : IsWeilCell Ω) : Ω.Nonempty := by
  obtain ⟨z, hz⟩ := hΩ.exists_mul_mem_left {1}
  exact ⟨z * 1, hz 1 (Finset.mem_singleton_self 1)⟩

theorem mul_self_eq_univ (hΩ : IsWeilCell Ω) : Ω * Ω = Set.univ := by
  classical
  refine Set.eq_univ_of_forall fun g => ?_
  obtain ⟨t, ht⟩ := hΩ.exists_mul_mem_right {1, g}
  refine ⟨g * t, ht g (by simp), t⁻¹, hΩ.inv_mem _ (by simpa using ht 1 (by simp)), by group⟩

variable {M : Type*} [Semigroup M] {R : G → M}

theorem mul_eq_of_translate (hΩ : IsWeilCell Ω) (hR : IsMulOn Ω R) {x y t : G} (hx : x ∈ Ω)
    (hy : y ∈ Ω) (ht : t ∈ Ω) (hyt : y * t ∈ Ω) (hxyt : x * y * t ∈ Ω) :
    R x * R y = R (x * y * t) * R t⁻¹ := by
  have h1 : R (y * t) * R t⁻¹ = R y := by
    rw [hR _ hyt _ (hΩ.inv_mem _ ht) (by simpa using hy)]; simp
  rw [← h1, ← mul_assoc, hR _ hx _ hyt (by simpa [mul_assoc] using hxyt), mul_assoc]

theorem mul_eq_mul (hΩ : IsWeilCell Ω) (hR : IsMulOn Ω R) {x₁ y₁ x₂ y₂ : G} (hx₁ : x₁ ∈ Ω)
    (hy₁ : y₁ ∈ Ω) (hx₂ : x₂ ∈ Ω) (hy₂ : y₂ ∈ Ω) (h : x₁ * y₁ = x₂ * y₂) :
    R x₁ * R y₁ = R x₂ * R y₂ := by
  classical
  obtain ⟨t, ht⟩ := hΩ.exists_mul_mem_right {1, y₁, y₂, x₁ * y₁}
  have t1 : t ∈ Ω := by simpa using ht 1 (by simp)
  have t2 : y₁ * t ∈ Ω := ht y₁ (by simp)
  have t3 : y₂ * t ∈ Ω := ht y₂ (by simp)
  have t4 : x₁ * y₁ * t ∈ Ω := ht _ (by simp)
  rw [hΩ.mul_eq_of_translate hR hx₁ hy₁ t1 t2 t4,
    hΩ.mul_eq_of_translate hR hx₂ hy₂ t1 t3 (by rwa [← h]), h]

theorem exists_translate (hΩ : IsWeilCell Ω) (g : G) : ∃ t : G, t ∈ Ω ∧ g * t ∈ Ω := by
  classical
  obtain ⟨t, ht⟩ := hΩ.exists_mul_mem_right {1, g}
  exact ⟨t, by simpa using ht 1 (by simp), ht g (by simp)⟩

noncomputable def translate (hΩ : IsWeilCell Ω) (g : G) : G :=
  Classical.choose (hΩ.exists_translate g)

theorem translate_mem (hΩ : IsWeilCell Ω) (g : G) : hΩ.translate g ∈ Ω :=
  (Classical.choose_spec (hΩ.exists_translate g)).1

theorem mul_translate_mem (hΩ : IsWeilCell Ω) (g : G) : g * hΩ.translate g ∈ Ω :=
  (Classical.choose_spec (hΩ.exists_translate g)).2

noncomputable def extendFun (hΩ : IsWeilCell Ω) (R : G → M) (g : G) : M :=
  R (g * hΩ.translate g) * R (hΩ.translate g)⁻¹

theorem extendFun_mul_of_mem (hΩ : IsWeilCell Ω) (hR : IsMulOn Ω R) {x y : G} (hx : x ∈ Ω)
    (hy : y ∈ Ω) : hΩ.extendFun R (x * y) = R x * R y :=
  hΩ.mul_eq_mul hR (hΩ.mul_translate_mem _) (hΩ.inv_mem _ (hΩ.translate_mem _)) hx hy (by group)

theorem extendFun_of_mem (hΩ : IsWeilCell Ω) (hR : IsMulOn Ω R) {x : G} (hx : x ∈ Ω) :
    hΩ.extendFun R x = R x := by
  unfold extendFun
  rw [hR _ (hΩ.mul_translate_mem _) _ (hΩ.inv_mem _ (hΩ.translate_mem _)) (by simpa using hx)]
  simp

theorem extendFun_mul (hΩ : IsWeilCell Ω) (hR : IsMulOn Ω R) (g h : G) :
    hΩ.extendFun R (g * h) = hΩ.extendFun R g * hΩ.extendFun R h := by
  classical
  obtain ⟨s, hs⟩ := hΩ.exists_mul_mem_left {1, h, g⁻¹}
  have s1 : s ∈ Ω := by simpa using hs 1 (by simp)
  have s2 : s * h ∈ Ω := hs h (by simp)
  have s3 : g * s⁻¹ ∈ Ω := by simpa using hΩ.inv_mem _ (hs g⁻¹ (by simp))
  obtain ⟨t, ht⟩ := hΩ.exists_mul_mem_right {1, g, s}
  have t1 : t ∈ Ω := by simpa using ht 1 (by simp)
  have t2 : g * t ∈ Ω := ht g (by simp)
  have t3 : s * t ∈ Ω := ht s (by simp)
  have eg : hΩ.extendFun R g = R (g * t) * R t⁻¹ := by
    rw [← hΩ.extendFun_mul_of_mem hR t2 (hΩ.inv_mem _ t1)]; group
  have eh : hΩ.extendFun R h = R s⁻¹ * R (s * h) := by
    rw [← hΩ.extendFun_mul_of_mem hR (hΩ.inv_mem _ s1) s2]; group
  have e1 : R t⁻¹ * R s⁻¹ = R (t⁻¹ * s⁻¹) :=
    hR _ (hΩ.inv_mem _ t1) _ (hΩ.inv_mem _ s1) (by simpa using hΩ.inv_mem _ t3)
  have e2 : R (g * t) * R (t⁻¹ * s⁻¹) = R (g * s⁻¹) := by
    rw [hR _ t2 _ (by simpa using hΩ.inv_mem _ t3) (by simpa [mul_assoc] using s3)]
    congr 1; group
  rw [eg, eh, mul_assoc, ← mul_assoc (R t⁻¹), e1, ← mul_assoc, e2,
    ← hΩ.extendFun_mul_of_mem hR s3 s2]
  congr 1; group

noncomputable def extend (hΩ : IsWeilCell Ω) (hR : IsMulOn Ω R) : G →ₙ* M where
  toFun := hΩ.extendFun R
  map_mul' := hΩ.extendFun_mul hR

theorem extend_apply_of_mem (hΩ : IsWeilCell Ω) (hR : IsMulOn Ω R) {x : G} (hx : x ∈ Ω) :
    hΩ.extend hR x = R x :=
  hΩ.extendFun_of_mem hR hx

theorem extend_unique (hΩ : IsWeilCell Ω) (hR : IsMulOn Ω R) (Φ : G →ₙ* M)
    (hΦ : ∀ x ∈ Ω, Φ x = R x) : Φ = hΩ.extend hR := by
  ext g
  obtain ⟨x, hx, y, hy, rfl⟩ : g ∈ Ω * Ω := by rw [hΩ.mul_self_eq_univ]; trivial
  rw [map_mul, map_mul, hΦ x hx, hΦ y hy, hΩ.extend_apply_of_mem hR hx,
    hΩ.extend_apply_of_mem hR hy]

theorem mulHom_ext (hΩ : IsWeilCell Ω) {Φ Ψ : G →ₙ* M} (h : ∀ x ∈ Ω, Φ x = Ψ x) : Φ = Ψ := by
  ext g
  obtain ⟨x, hx, y, hy, rfl⟩ : g ∈ Ω * Ω := by rw [hΩ.mul_self_eq_univ]; trivial
  rw [map_mul, map_mul, h x hx, h y hy]

section Monoid

variable {N : Type*} [Monoid N] {S : G → N}

theorem extend_one (hΩ : IsWeilCell Ω) (hS : IsMulOn Ω S) {x₀ : G} (hx₀ : x₀ ∈ Ω)
    (hu : IsUnit (S x₀)) : hΩ.extend hS 1 = 1 := by
  have h : hΩ.extend hS 1 * S x₀ = S x₀ := by
    rw [← hΩ.extend_apply_of_mem hS hx₀, ← map_mul, one_mul]
  exact hu.mul_eq_right.mp h

noncomputable def extendMonoidHom (hΩ : IsWeilCell Ω) (hS : IsMulOn Ω S) {x₀ : G} (hx₀ : x₀ ∈ Ω)
    (hu : IsUnit (S x₀)) : G →* N where
  toFun := hΩ.extend hS
  map_one' := hΩ.extend_one hS hx₀ hu
  map_mul' := map_mul (hΩ.extend hS)

theorem extendMonoidHom_apply_of_mem (hΩ : IsWeilCell Ω) (hS : IsMulOn Ω S) {x₀ : G}
    (hx₀ : x₀ ∈ Ω) (hu : IsUnit (S x₀)) {x : G} (hx : x ∈ Ω) :
    hΩ.extendMonoidHom hS hx₀ hu x = S x :=
  hΩ.extend_apply_of_mem hS hx

theorem monoidHom_ext (hΩ : IsWeilCell Ω) {Φ Ψ : G →* N} (h : ∀ x ∈ Ω, Φ x = Ψ x) : Φ = Ψ := by
  ext g
  obtain ⟨x, hx, y, hy, rfl⟩ : g ∈ Ω * Ω := by rw [hΩ.mul_self_eq_univ]; trivial
  rw [map_mul, map_mul, h x hx, h y hy]

theorem extendMonoidHom_unique (hΩ : IsWeilCell Ω) (hS : IsMulOn Ω S) {x₀ : G} (hx₀ : x₀ ∈ Ω)
    (hu : IsUnit (S x₀)) (Φ : G →* N) (hΦ : ∀ x ∈ Ω, Φ x = S x) :
    Φ = hΩ.extendMonoidHom hS hx₀ hu :=
  hΩ.monoidHom_ext fun x hx => by rw [hΦ x hx, hΩ.extendMonoidHom_apply_of_mem hS hx₀ hu hx]

theorem not_exists_monoidHom_zero (G : Type*) [Group G] :
    IsWeilCell (Set.univ : Set G) ∧ IsMulOn (Set.univ : Set G) (fun _ => (0 : ℕ)) ∧
      ¬ ∃ Φ : G →* ℕ, ∀ x ∈ (Set.univ : Set G), Φ x = 0 := by
  refine ⟨⟨fun _ _ => trivial, fun _ => ⟨1, fun _ _ => trivial⟩⟩, fun _ _ _ _ _ => by simp, ?_⟩
  rintro ⟨Φ, hΦ⟩
  have := hΦ 1 trivial
  rw [map_one] at this
  exact one_ne_zero this

end Monoid

section Group

variable {H : Type*} [Group H] {T : G → H}

noncomputable def extendGroupHom (hΩ : IsWeilCell Ω) (hT : IsMulOn Ω T) : G →* H :=
  hΩ.extendMonoidHom hT (hΩ.nonempty.some_mem) (Group.isUnit _)

theorem extendGroupHom_apply_of_mem (hΩ : IsWeilCell Ω) (hT : IsMulOn Ω T) {x : G}
    (hx : x ∈ Ω) : hΩ.extendGroupHom hT x = T x :=
  hΩ.extend_apply_of_mem hT hx

end Group

end IsWeilCell

example : (isWeilCell_GL_two ℚ).extendGroupHom (T := id) (fun _ _ _ _ _ => rfl) =
    MonoidHom.id _ := by
  apply (isWeilCell_GL_two ℚ).monoidHom_ext
  intro x hx
  exact (isWeilCell_GL_two ℚ).extendGroupHom_apply_of_mem _ hx

example : (isWeilCell_GL_two ℚ).extendGroupHom (T := fun g => Matrix.GeneralLinearGroup.det g)
    (fun x _ y _ _ => (map_mul _ x y).symm) = Matrix.GeneralLinearGroup.det := by
  apply (isWeilCell_GL_two ℚ).monoidHom_ext
  intro x hx
  exact (isWeilCell_GL_two ℚ).extendGroupHom_apply_of_mem _ hx

end GroundTheory.Heights₂.Theta

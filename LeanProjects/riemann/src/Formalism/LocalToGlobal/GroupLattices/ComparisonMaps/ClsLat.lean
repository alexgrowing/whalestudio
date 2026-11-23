import Formalism.SharpRestriction.GrowthBounds.DataG

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Matrix

section One

variable (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ}

def gMap (g : GL (Fin k) Qq) (A : Submodule W (Fin k → Qq)) : Submodule W (Fin k → Qq) :=
  A.map ((Matrix.mulVecLin (g : Matrix (Fin k) (Fin k) Qq)).restrictScalars W)

theorem mem_gMap (g : GL (Fin k) Qq) (A : Submodule W (Fin k → Qq)) (x : Fin k → Qq) :
    x ∈ gMap W g A ↔ ∃ y ∈ A, (g : Matrix (Fin k) (Fin k) Qq) *ᵥ y = x := Submodule.mem_map

theorem gMap_one (A : Submodule W (Fin k → Qq)) : gMap W 1 A = A := by
  ext x
  rw [mem_gMap]
  simp

theorem gMap_mul (g h : GL (Fin k) Qq) (A : Submodule W (Fin k → Qq)) : gMap W (g * h) A = gMap W g (gMap W h A) := by
  ext x
  simp only [mem_gMap, Units.val_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(h : Matrix (Fin k) (Fin k) Qq) *ᵥ y, ⟨y, hy, rfl⟩, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by rw [Matrix.mulVec_mulVec]⟩

theorem gMap_inj (g : GL (Fin k) Qq) {A B : Submodule W (Fin k → Qq)} (h : gMap W g A = gMap W g B) : A = B := by
  have e := congrArg (gMap W g⁻¹) h
  rwa [← gMap_mul, ← gMap_mul, inv_mul_cancel, gMap_one, gMap_one] at e

def stdL : Submodule W (Fin k → Qq) := colSpan W (1 : Matrix (Fin k) (Fin k) Qq)

theorem colSpan_eq (g : GL (Fin k) Qq) : colSpan W (g : Matrix (Fin k) (Fin k) Qq) = gMap W g (stdL W) := by
  unfold gMap stdL colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1
  refine congrArg Set.range (funext fun c => funext fun i => ?_)
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

theorem isLattice_iff (L : Submodule W (Fin k → Qq)) : IsLattice W L ↔ ∃ g : GL (Fin k) Qq, L = gMap W g (stdL W) := by
  constructor
  · rintro ⟨g, hg, hL⟩
    let G : GL (Fin k) Qq := Units.mk g g⁻¹ (Matrix.mul_nonsing_inv g hg) (Matrix.nonsing_inv_mul g hg)
    have hG : (G : Matrix (Fin k) (Fin k) Qq) = g := rfl
    refine ⟨G, ?_⟩
    rw [hL, ← colSpan_eq, hG]
  · rintro ⟨g, hL⟩
    refine ⟨(g : Matrix (Fin k) (Fin k) Qq), (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit, ?_⟩
    rw [hL, colSpan_eq]

theorem mem_stdL (x : Fin k → Qq) : x ∈ stdL (k := k) (Qq := Qq) W ↔ ∀ a, x a ∈ (algebraMap W Qq).range := by
  show x ∈ Submodule.span W (Set.range fun c : Fin k => fun i => (1 : Matrix (Fin k) (Fin k) Qq) i c) ↔ _
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, rfl⟩ := hy
      intro a
      by_cases h : a = c
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Matrix.one_apply_ne h]⟩
    | zero => intro a; exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      intro a
      obtain ⟨u, hu⟩ := hy a
      obtain ⟨v, hv⟩ := hz a
      exact ⟨u + v, by simp [hu, hv]⟩
    | smul w y _ hy =>
      intro a
      obtain ⟨u, hu⟩ := hy a
      exact ⟨w * u, by simp [hu, Algebra.smul_def]⟩
  · intro h
    simp only [RingHom.mem_range] at h
    choose w hw using h
    have e : x = ∑ c, w c • (fun i => (1 : Matrix (Fin k) (Fin k) Qq) i c) := by
      ext i
      simp [Finset.sum_apply, Matrix.one_apply, Algebra.smul_def, hw]
    rw [e]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem gMap_std_le (g : GL (Fin k) Qq) :
    gMap W g (stdL W) ≤ stdL W ↔ ∀ a b, (g : Matrix (Fin k) (Fin k) Qq) a b ∈ (algebraMap W Qq).range := by
  rw [← colSpan_eq]
  constructor
  · intro h a b
    exact (mem_stdL W _).1 (h (Submodule.subset_span ⟨b, rfl⟩)) a
  · intro h
    rw [colSpan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact (mem_stdL W _).2 fun a => h a c

def stabStd : Subgroup (GL (Fin k) Qq) where
  carrier := {g | gMap W g (stdL W) = stdL W}
  one_mem' := gMap_one W _
  mul_mem' := by
    intro a b ha hb
    show gMap W (a * b) _ = _
    rw [gMap_mul, show gMap W b (stdL W) = stdL W from hb]
    exact ha
  inv_mem' := by
    intro a ha
    show gMap W a⁻¹ _ = _
    apply gMap_inj W a
    rw [← gMap_mul, mul_inv_cancel, gMap_one]
    exact (show gMap W a (stdL W) = stdL W from ha).symm

theorem mem_stabStd (g : GL (Fin k) Qq) : g ∈ stabStd (k := k) (Qq := Qq) W ↔ gMap W g (stdL W) = stdL W := Iff.rfl

theorem stabStd_iff (g : GL (Fin k) Qq) : g ∈ stabStd (k := k) (Qq := Qq) W ↔
    (∀ a b, (g : Matrix (Fin k) (Fin k) Qq) a b ∈ (algebraMap W Qq).range) ∧
      ∀ a b, ((g⁻¹ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq) a b ∈ (algebraMap W Qq).range := by
  rw [mem_stabStd]
  constructor
  · intro h
    have h' : g⁻¹ ∈ stabStd (k := k) (Qq := Qq) W := inv_mem ((mem_stabStd W g).2 h)
    rw [mem_stabStd] at h'
    exact ⟨(gMap_std_le W g).1 h.le, (gMap_std_le W g⁻¹).1 h'.le⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm ((gMap_std_le W g).2 h1) ?_
    have mono : ∀ {A B : Submodule W (Fin k → Qq)}, A ≤ B → gMap W g A ≤ gMap W g B :=
      fun hAB => Submodule.map_mono hAB
    have h3 := mono ((gMap_std_le W g⁻¹).2 h2)
    rwa [← gMap_mul, mul_inv_cancel, gMap_one] at h3

theorem gMap_std_eq_iff (g h : GL (Fin k) Qq) :
    gMap W g (stdL W) = gMap W h (stdL W) ↔ h⁻¹ * g ∈ stabStd (k := k) (Qq := Qq) W := by
  rw [mem_stabStd, gMap_mul]
  constructor
  · intro e
    rw [e, ← gMap_mul, inv_mul_cancel, gMap_one]
  · intro e
    apply gMap_inj W h⁻¹
    rw [e, ← gMap_mul, inv_mul_cancel, gMap_one]

end One

section Tuples

variable (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k nV : ℕ}

def tupOf (g : Fin nV → GL (Fin k) Qq) : Fin nV → Submodule W (Fin k → Qq) := fun v => gMap W (g v) (stdL W)

def stabTup : Subgroup (Fin nV → GL (Fin k) Qq) := Subgroup.pi Set.univ fun _ => stabStd W

theorem mem_stabTup (g : Fin nV → GL (Fin k) Qq) : g ∈ stabTup (nV := nV) (k := k) (Qq := Qq) W ↔ ∀ v, g v ∈ stabStd W := by
  show g ∈ Subgroup.pi Set.univ _ ↔ _
  simp [Subgroup.mem_pi]

theorem tupOf_eq_iff (g h : Fin nV → GL (Fin k) Qq) :
    tupOf W g = tupOf W h ↔ h⁻¹ * g ∈ stabTup (nV := nV) (k := k) (Qq := Qq) W := by
  rw [mem_stabTup]
  constructor
  · intro H v
    exact (gMap_std_eq_iff W (g v) (h v)).1 (congrFun H v)
  · intro H
    funext v
    exact (gMap_std_eq_iff W (g v) (h v)).2 (H v)

theorem exists_tupOf (L : Fin nV → Submodule W (Fin k → Qq)) (hL : ∀ v, IsLattice W (L v)) : ∃ g, L = tupOf W g := by
  choose g hg using fun v => (isLattice_iff W (L v)).1 (hL v)
  exact ⟨g, funext hg⟩

theorem tupOf_lat (g : Fin nV → GL (Fin k) Qq) (v : Fin nV) : IsLattice W (tupOf W g v) := (isLattice_iff W _).2 ⟨g v, rfl⟩

end Tuples

end Formalism.L2.G.Cmp

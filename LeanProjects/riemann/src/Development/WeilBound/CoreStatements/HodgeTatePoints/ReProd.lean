import Development.WeilBound.CoreStatements.HodgeTatePoints.ReBase
import ReciprocityTheory.DualLattices.CharTableIsUnit

noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix Kronecker

namespace PositivityTheory.HtPt.Re

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

def tn {X Y : Type} (M : Submodule R (X → C)) (M' : Submodule R (Y → C)) :
    Submodule R (X × Y → C) :=
  Submodule.span R {F | ∃ g ∈ M, ∃ h ∈ M', F = fun z => g z.1 * h z.2}

theorem mem_tn {X Y : Type} {M : Submodule R (X → C)} {M' : Submodule R (Y → C)} {g : X → C}
    {h : Y → C} (hg : g ∈ M) (hh : h ∈ M') : (fun z : X × Y => g z.1 * h z.2) ∈ tn M M' :=
  Submodule.subset_span ⟨g, hg, h, hh, rfl⟩

def bil {X Y Z : Type} (a : Z → X) (b : Z → Y) : (X → C) →ₗ[R] (Y → C) →ₗ[R] (Z → C) :=
  (LinearMap.mul R (Z → C)).compl₁₂ (LinearMap.funLeft R C a) (LinearMap.funLeft R C b)

theorem bil_span {X Y Z : Type} (a : Z → X) (b : Z → Y) {s : Set (X → C)} {t : Set (Y → C)}
    {P : Submodule R (Z → C)} (H : ∀ g ∈ s, ∀ h ∈ t, (fun z => g (a z) * h (b z)) ∈ P)
    {g : X → C} {h : Y → C} (hg : g ∈ Submodule.span R s) (hh : h ∈ Submodule.span R t) :
    (fun z => g (a z) * h (b z)) ∈ P := by
  have h1 : Submodule.map₂ (bil (R := R) (C := C) a b) (Submodule.span R s) (Submodule.span R t)
      ≤ P := by
    rw [Submodule.map₂_span_span, Submodule.span_le]
    rintro _ ⟨g, hg, h, hh, rfl⟩
    exact H g hg h hh
  exact h1 (Submodule.apply_mem_map₂ _ hg hh)

theorem tn_cols {X Y : Type} (B : Matrix X X C) (B' : Matrix Y Y C) :
    tn (Submodule.span R (Set.range fun j x => B x j))
      (Submodule.span R (Set.range fun j x => B' x j)) =
    Submodule.span R (Set.range fun j x => (B ⊗ₖ B') x j) := by
  apply le_antisymm
  · rw [tn, Submodule.span_le]
    rintro _ ⟨g, hg, h, hh, rfl⟩
    refine bil_span Prod.fst Prod.snd ?_ hg hh
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨(i, j), rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact mem_tn (g := fun x => B x i) (h := fun x => B' x j) (Submodule.subset_span ⟨i, rfl⟩)
      (Submodule.subset_span ⟨j, rfl⟩)

theorem hasColen_tn {v : Valuation C NNReal} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] {M : Submodule R (X → C)} {M' : Submodule R (Y → C)} {c c' : NNReal}
    (h : HasColen R v M c) (h' : HasColen R v M' c') :
    HasColen R v (tn M M') (c ^ Fintype.card Y * c' ^ Fintype.card X) := by
  obtain ⟨B, rfl, rfl⟩ := h
  obtain ⟨B', rfl, rfl⟩ := h'
  exact ⟨B ⊗ₖ B', tn_cols B B', by rw [Matrix.det_kronecker, map_mul, map_pow, map_pow]⟩

variable {N₁ : Type} [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁]
  {N₂ : Type} [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂]

def hopfProd (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂) :
    HopfOrder (C := C) R (N₁ × N₂) :=
  HopfOrder.ofSpan {F | ∃ g ∈ A₁.carrier, ∃ h ∈ A₂.carrier, F = fun z => g z.1 * h z.2}
    (by
      obtain ⟨B, hB, h⟩ := A₁.lat
      obtain ⟨B', hB', h'⟩ := A₂.lat
      refine ⟨B ⊗ₖ B', ?_, ?_⟩
      · rw [Matrix.det_kronecker]; exact (hB.pow _).mul (hB'.pow _)
      · rw [← tn_cols, ← h, ← h']; rfl)
    (by
      rintro _ ⟨g, hg, h, hh, rfl⟩ z
      obtain ⟨r, hr⟩ := A₁.le_int hg z.1
      obtain ⟨s, hs⟩ := A₂.le_int hh z.2
      exact ⟨r * s, by rw [map_mul, hr, hs]⟩)
    (Submodule.subset_span ⟨1, A₁.one_mem, 1, A₂.one_mem, by funext z; simp⟩)
    (by
      rintro _ ⟨g, hg, h, hh, rfl⟩ _ ⟨g', hg', h', hh', rfl⟩
      refine Submodule.subset_span ⟨_, A₁.mul_mem _ _ hg hg', _, A₂.mul_mem _ _ hh hh', ?_⟩
      funext z
      simp only [Pi.mul_apply]; ring)
    (by
      rintro _ ⟨g, hg, h, hh, rfl⟩
      refine bil_span (fun z : (N₁ × N₂) × (N₁ × N₂) => (z.1.1, z.2.1))
        (fun z : (N₁ × N₂) × (N₁ × N₂) => (z.1.2, z.2.2)) ?_ (A₁.comul g hg) (A₂.comul h hh)
      rintro _ ⟨u, hu, u', hu', rfl⟩ _ ⟨w, hw, w', hw', rfl⟩
      refine Submodule.subset_span ⟨_, mem_tn hu hw, _, mem_tn hu' hw', ?_⟩
      funext z
      ring)
    (by
      rintro _ ⟨g, hg, h, hh, rfl⟩
      exact mem_tn (A₁.antipode g hg) (A₂.antipode h hh))

theorem hopfProd_carrier (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂) :
    (hopfProd A₁ A₂).carrier = tn A₁.carrier A₂.carrier := rfl

theorem tn_inl (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂) :
    (tn A₁.carrier A₂.carrier).map
      (LinearMap.funLeft R C (AddMonoidHom.inl N₁ N₂ : N₁ → N₁ × N₂)) = A₁.carrier := by
  apply le_antisymm
  · rw [tn, Submodule.map_span_le]
    rintro _ ⟨g, hg, h, hh, rfl⟩
    obtain ⟨r, hr⟩ := A₂.le_int hh 0
    convert A₁.carrier.smul_mem r hg using 1
    funext x
    simp [Algebra.smul_def, hr, mul_comm]
  · intro g hg
    exact ⟨_, mem_tn hg A₂.one_mem, by funext x; simp⟩

theorem tn_inr (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂) :
    (tn A₁.carrier A₂.carrier).map
      (LinearMap.funLeft R C (AddMonoidHom.inr N₁ N₂ : N₂ → N₁ × N₂)) = A₂.carrier := by
  apply le_antisymm
  · rw [tn, Submodule.map_span_le]
    rintro _ ⟨g, hg, h, hh, rfl⟩
    obtain ⟨r, hr⟩ := A₁.le_int hg 0
    convert A₂.carrier.smul_mem r hh using 1
    funext x
    simp [Algebra.smul_def, hr]
  · intro g hg
    exact ⟨_, mem_tn A₁.one_mem hg, by funext x; simp⟩

theorem tn_stab₁ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂) :
    ∀ g ∈ tn A₁.carrier A₂.carrier,
      (fun z : N₁ × N₂ => g (z.1, 0)) ∈ tn A₁.carrier A₂.carrier := by
  intro g hg
  have h := Submodule.mem_map_of_mem
    (f := LinearMap.funLeft R C (AddMonoidHom.inl N₁ N₂ : N₁ → N₁ × N₂)) hg
  rw [tn_inl] at h
  convert mem_tn h A₂.one_mem using 1
  funext z
  simp

theorem tn_stab₂ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂) :
    ∀ g ∈ tn A₁.carrier A₂.carrier,
      (fun z : N₁ × N₂ => g (0, z.2)) ∈ tn A₁.carrier A₂.carrier := by
  intro g hg
  have h := Submodule.mem_map_of_mem
    (f := LinearMap.funLeft R C (AddMonoidHom.inr N₁ N₂ : N₂ → N₁ × N₂)) hg
  rw [tn_inr] at h
  convert mem_tn A₁.one_mem h using 1
  funext z
  simp

theorem tn_char {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {N₁ N₂ : Type} [AddCommGroup N₁] [AddCommGroup N₂]
    (e : N₁ × N₂ ≃+ N)
    (hs : ∀ g ∈ AA.carrier, (fun x => g (e ((e.symm x).1, 0))) ∈ AA.carrier) :
    AA.carrier.map (LinearMap.funLeft R C (e : N₁ × N₂ → N)) =
      tn (AA.carrier.map (LinearMap.funLeft R C fun y : N₁ => e (y, 0)))
        (AA.carrier.map (LinearMap.funLeft R C fun y : N₂ => e (0, y))) := by
  have hadd : ∀ z : N₁ × N₂, e (z.1, 0) + e (0, z.2) = e z := fun z => by
    rw [← map_add]; simp
  have hs₂ : ∀ g ∈ AA.carrier, (fun x => g (e (0, (e.symm x).2))) ∈ AA.carrier := by
    intro g hg
    have := (stabadd C R N N AA AA (AddMonoidHom.id N)
      (e.toAddMonoidHom.comp ((AddMonoidHom.inl N₁ N₂).comp
        ((AddMonoidHom.fst N₁ N₂).comp e.symm.toAddMonoidHom))) (fun g hg => hg) hs).2 g hg
    convert this using 3 with x
    have h := hadd (e.symm x)
    rw [e.apply_symm_apply] at h
    exact eq_sub_of_add_eq' h
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    have h : (tensorSpan R AA.carrier).map
        (LinearMap.funLeft R C (fun z : N₁ × N₂ => (e (z.1, 0), e (0, z.2)))) ≤
        tn (AA.carrier.map (LinearMap.funLeft R C fun y : N₁ => e (y, 0)))
        (AA.carrier.map (LinearMap.funLeft R C fun y : N₂ => e (0, y))) := by
      rw [tensorSpan, Submodule.map_span_le]
      rintro F ⟨u, hu, w, hw, rfl⟩
      exact mem_tn (Submodule.mem_map_of_mem hu) (Submodule.mem_map_of_mem hw)
    convert h (Submodule.mem_map_of_mem (AA.comul g hg)) using 1
    funext z
    show g (e z) = g (e (z.1, 0) + e (0, z.2))
    rw [hadd]
  · rw [tn, Submodule.span_le]
    rintro _ ⟨_, ⟨u, hu, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨_, AA.mul_mem _ _ (hs u hu) (hs₂ w hw), ?_⟩
    funext z
    simp [LinearMap.funLeft_apply]

end PositivityTheory.HtPt.Re

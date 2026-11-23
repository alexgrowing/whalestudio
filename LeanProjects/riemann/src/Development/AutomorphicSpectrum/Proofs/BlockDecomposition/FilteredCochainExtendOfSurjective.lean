import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeRepExact

universe v u

section Gen

variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D] {A : D ⥤ CommAlgCat.{0} R} (a b : IdF A)

def Rp {j : ℕ} (y : CH.Cn (sq a b) j) (z : CH.Cn (CH.modF A) j) : Prop :=
  ∀ s, (show sqM a b _ from y s).1 = Ideal.Quotient.mk (b.S _) (show A.obj _ from z s)

variable {a b}

theorem sqMap_val {T T' : D} (φ : T ⟶ T') (w : sqM a b T) (x : A.obj T) (h : w.1 = Ideal.Quotient.mk (b.S T) x) :
    (sqMap a b φ w).1 = Ideal.Quotient.mk (b.S T') ((A.map φ).hom x) := by
  obtain ⟨w, hw⟩ := w
  obtain rfl : w = _ := h
  rfl

theorem Rp.d {j : ℕ} {y : CH.Cn (sq a b) j} {z : CH.Cn (CH.modF A) j} (h : Rp a b y z) :
    Rp a b (CH.d _ j y) (CH.d _ j z) := by
  intro s
  change (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • sqMap a b (toLast i s) (y (face i s)) : sqM a b _).1 =
    Ideal.Quotient.mk _ (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (A.map (toLast i s)).hom (z (face i s)))
  rw [map_sum, AddSubmonoidClass.coe_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  change (-1 : ℤ) ^ (i : ℕ) • (sqMap a b (toLast i s) (y (face i s))).1 = _
  rw [sqMap_val _ _ _ (h (face i s))]

theorem Rp.sub {j : ℕ} {y y' : CH.Cn (sq a b) j} {z z' : CH.Cn (CH.modF A) j} (h : Rp a b y z) (h' : Rp a b y' z') :
    Rp a b (y - y') (z - z') := by
  intro s
  change (show sqM a b _ from y s).1 - (show sqM a b _ from y' s).1 =
    Ideal.Quotient.mk _ ((show A.obj _ from z s) - (show A.obj _ from z' s))
  rw [map_sub, h s, h' s]

theorem Rp.unique {j : ℕ} {y y' : CH.Cn (sq a b) j} {z : CH.Cn (CH.modF A) j} (h : Rp a b y z) (h' : Rp a b y' z) :
    y = y' :=
  funext fun s => Subtype.ext ((h s).trans (h' s).symm)

theorem Rp.mem {j : ℕ} {z : CH.Cn (CH.modF A) j} (h : Rp a b 0 z) (s) : z s ∈ b.S _ :=
  (Ideal.Quotient.eq_zero_iff_mem (a := (show A.obj _ from z s)) (I := b.S _)).1 (h s).symm

theorem Rp.zero {j : ℕ} {z : CH.Cn (CH.modF A) j} (h : ∀ s, z s ∈ b.S _) : Rp a b 0 z := fun s =>
  ((Ideal.Quotient.eq_zero_iff_mem (a := (show A.obj _ from z s)) (I := b.S _)).2 (h s)).symm

theorem exists_rp {j : ℕ} (z : CH.Cn (CH.modF A) j) (hz : ∀ s, z s ∈ a.S _) : ∃ y, Rp a b y z :=
  ⟨fun s => sqMk a b (show A.obj _ from z s) (hz s), fun _ => rfl⟩

theorem exists_lift {j : ℕ} (y : CH.Cn (sq a b) j) : ∃ z : CH.Cn (CH.modF A) j, (∀ s, z s ∈ a.S _) ∧ Rp a b y z := by
  have key : ∀ s : ComposableArrows D j, ∃ x : A.obj (s.obj (Fin.last j)), x ∈ a.S _ ∧
      (show sqM a b _ from y s).1 = Ideal.Quotient.mk (b.S _) x := fun s => by
    obtain ⟨x, hx, e⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (show sqM a b _ from y s).2
    exact ⟨x, hx, e.symm⟩
  choose z hz hr using key
  exact ⟨z, hz, hr⟩

theorem exists_of_mem_B {n : ℕ} {w : CH.Cn (sq a b) n} {z : CH.Cn (CH.modF A) n} (hr : Rp a b w z)
    (hw : w ∈ (CH.cx (sq a b)).B n) : ∃ e : CH.Cn (CH.modF A) n, (∀ s, e s ∈ b.S _) ∧ CH.d _ n z = CH.d _ n e := by
  cases n with
  | zero =>
    have h0 : w = 0 := hw
    subst h0
    exact ⟨z, hr.mem, rfl⟩
  | succ n =>
    obtain ⟨t, rfl⟩ := hw
    obtain ⟨g, -, hg⟩ := exists_lift t
    have h0 : Rp a b 0 (z - CH.d _ n g) := by
      have := hr.sub hg.d
      rwa [sub_self] at this
    refine ⟨_, h0.mem, ?_⟩
    rw [map_sub, CH.d_d, sub_zero]

end Gen

section Cls

variable {R : Type} [CommRing R]

theorem sub_mem_B (K : Cx.{u} R) {n : ℕ} {x y : K.X n} (hx : K.d n x = 0) (hy : K.d n y = 0) (e : K.cls x hx = K.cls y hy) :
    x - y ∈ K.B n :=
  (Submodule.Quotient.eq ((K.B n).submoduleOf (K.Z n))).1 e

theorem cls_eq_of_sub_mem (K : Cx.{u} R) {n : ℕ} {x y : K.X n} (hx : K.d n x = 0) (hy : K.d n y = 0) (h : x - y ∈ K.B n) :
    K.cls x hx = K.cls y hy :=
  (Submodule.Quotient.eq ((K.B n).submoduleOf (K.Z n))).2 h

end Cls

section Res

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {A : C ⥤ CommAlgCat.{0} R}

theorem Rp.res (a b : IdF A) {U V : ObjectProperty C} (h : V ≤ U) {j : ℕ} {y : CH.Cn (sq (a.res U.ι) (b.res U.ι)) j}
    {z : CH.Cn (CH.modF (U.ι ⋙ A)) j} (hr : Rp _ _ y z) :
    Rp (a.res V.ι) (b.res V.ι) ((resU (sq a b) h).pullC j y) ((resU (CH.modF A) h).pullC j z) := fun s =>
  hr (s ⋙ ObjectProperty.ιOfLE h)

end Res

theorem exact_lift : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A),
    IsFil Φ Fil → ∀ {U V : ObjectProperty C} (h : V ≤ U) (n : ℕ),
    Function.Surjective ((resU (gr Fil n) h).pull n) →
    ∀ (f : CH.Cn (CH.modF (V.ι ⋙ Φ.A)) n), (∀ σ, f σ ∈ (Fil n).S _) → (∀ σ, CH.d _ n f σ ∈ (Fil ((n : ℤ) + 1)).S _) →
    ∃ f' : CH.Cn (CH.modF (U.ι ⋙ Φ.A)) n, (∀ σ, f' σ ∈ (Fil n).S _) ∧ (∀ σ, CH.d _ n f' σ ∈ (Fil ((n : ℤ) + 1)).S _) ∧
      ∀ (x : HU (gr Fil ((n : ℤ) + 1)) V (n + 1)) (x' : HU (gr Fil ((n : ℤ) + 1)) U (n + 1)),
        Rep ((Fil ((n : ℤ) + 1)).res V.ι) ((Fil ((n : ℤ) + 1 + 1)).res V.ι) (CH.d _ n f) x →
        Rep ((Fil ((n : ℤ) + 1)).res U.ι) ((Fil ((n : ℤ) + 1 + 1)).res U.ι) (CH.d _ n f') x' →
        x = (resU (gr Fil ((n : ℤ) + 1)) h).pull (n + 1) x' := by
  intro R _ C _ Φ Fil hF U V h n hs f hf hdf
  obtain ⟨y, hy⟩ := exists_rp (a := (Fil n).res V.ι) (b := (Fil ((n : ℤ) + 1)).res V.ι) f hf
  have hdy : CH.d _ n y = 0 := hy.d.unique (Rp.zero hdf)
  obtain ⟨c', hc'⟩ := hs ((CH.cx (sq ((Fil n).res V.ι) ((Fil ((n : ℤ) + 1)).res V.ι))).cls y hdy)
  obtain ⟨⟨y', hy'⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c'
  obtain ⟨f', hf'a, hf'⟩ := exists_lift (a := (Fil n).res U.ι) (b := (Fil ((n : ℤ) + 1)).res U.ι)
    (show CH.Cn (sq ((Fil n).res U.ι) ((Fil ((n : ℤ) + 1)).res U.ι)) n from y')
  have hdy' : CH.d (sq ((Fil n).res U.ι) ((Fil ((n : ℤ) + 1)).res U.ι)) n y' = 0 := hy'
  have hz : CH.d (sq ((Fil n).res V.ι) ((Fil ((n : ℤ) + 1)).res V.ι)) n ((resU (gr Fil n) h).pullC n y') = 0 :=
    ((resU (gr Fil n) h).hom.mapZ n ⟨y', hy'⟩).2
  have hB := sub_mem_B (CH.cx (sq ((Fil n).res V.ι) ((Fil ((n : ℤ) + 1)).res V.ι)))
    (x := (resU (gr Fil n) h).pullC n y') (y := y) hz hdy hc'
  refine ⟨f', hf'a, ?_, ?_⟩
  · have := hf'.d
    rw [hdy'] at this
    exact this.mem
  · rintro x x' ⟨u, hu, rfl, hur⟩ ⟨u', hu', rfl, hur'⟩
    have hur1 : Rp _ _ u (CH.d _ n f) := hur
    have hur2 : Rp _ _ u' (CH.d _ n f') := hur'
    have hw := (Rp.res (Fil n) (Fil ((n : ℤ) + 1)) h hf').sub hy
    obtain ⟨e, he, hde⟩ := exists_of_mem_B hw hB
    obtain ⟨t, ht⟩ := exists_rp (a := (Fil ((n : ℤ) + 1)).res V.ι) (b := (Fil ((n : ℤ) + 1 + 1)).res V.ι) e he
    have h1 := (Rp.res (Fil ((n : ℤ) + 1)) (Fil ((n : ℤ) + 1 + 1)) h hur2).sub hur1
    have e1 : (resU (CH.modF Φ.A) h).pullC (n + 1) (CH.d (CH.modF (U.ι ⋙ Φ.A)) n f') =
        CH.d (CH.modF (V.ι ⋙ Φ.A)) n ((resU (CH.modF Φ.A) h).pullC n f') :=
      ((resU (CH.modF Φ.A) h).d_pullC n f').symm
    rw [e1, ← map_sub, hde] at h1
    have h2 := h1.unique ht.d
    have hz' : CH.d (sq ((Fil ((n : ℤ) + 1)).res V.ι) ((Fil ((n : ℤ) + 1 + 1)).res V.ι)) (n + 1)
        ((resU (gr Fil ((n : ℤ) + 1)) h).pullC (n + 1) u') = 0 :=
      ((resU (gr Fil ((n : ℤ) + 1)) h).hom.mapZ (n + 1) ⟨u', hu'⟩).2
    exact (cls_eq_of_sub_mem (CH.cx (sq ((Fil ((n : ℤ) + 1)).res V.ι) ((Fil ((n : ℤ) + 1 + 1)).res V.ι)))
      (x := (resU (gr Fil ((n : ℤ) + 1)) h).pullC (n + 1) u') (y := u) hz' hu ⟨t, h2.symm⟩).symm

end GlobalTheory.CompanionTheory.ConeRepExact

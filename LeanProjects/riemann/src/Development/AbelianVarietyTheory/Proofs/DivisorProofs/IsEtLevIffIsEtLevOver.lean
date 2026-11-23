import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev.PullPt

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S T : Scheme.{0}} {s : S ⟶ Sp R} {t : T ⟶ S} {s₁ : T ⟶ Sp R} {o : Obj b N s} {o₁ : Obj b N s₁}

def ptOver (m : ObjMap o₁ o t) {U : Over T} (g : U ⟶ o₁.A) : Over.mk (U.hom ≫ t) ⟶ o.A :=
  Over.homMk (g.left ≫ m.φ) (by
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w g]
    rfl)

@[simp] theorem ptOver_left (m : ObjMap o₁ o t) {U : Over T} (g : U ⟶ o₁.A) :
    (ptOver m g).left = g.left ≫ m.φ := rfl

theorem ptOver_injective (m : ObjMap o₁ o t) {U : Over T} : Function.Injective (ptOver m (U := U)) := by
  intro g h e
  have e' : g.left ≫ m.φ = h.left ≫ m.φ := by
    rw [← ptOver_left m g, ← ptOver_left m h, e]
  ext
  exact m.cart.1.hom_ext e' (by rw [Over.w g, Over.w h])

theorem ptOver_surjective (m : ObjMap o₁ o t) {U : Over T} : Function.Surjective (ptOver m (U := U)) := by
  intro g₀
  refine ⟨Over.homMk (m.cart.1.lift g₀.left U.hom (by rw [Over.w g₀]; rfl)) (m.cart.1.lift_snd _ _ _), ?_⟩
  ext
  simp [ptOver, m.cart.1.lift_fst]

theorem ptOver_mul (m : ObjMap o₁ o t) {U : Over T} (g h : U ⟶ o₁.A) :
    ptOver m (g * h) = ptOver m g * ptOver m h := by
  ext
  exact (m.cart.2 U g h (ptOver m g) (ptOver m h) rfl rfl).symm

theorem ptOver_one (m : ObjMap o₁ o t) {U : Over T} : ptOver m (1 : U ⟶ o₁.A) = 1 := by
  have h := ptOver_mul m (1 : U ⟶ o₁.A) 1
  rw [_root_.mul_one] at h
  exact (mul_eq_left.mp h.symm)

theorem ptOver_eq_one (m : ObjMap o₁ o t) {U : Over T} (g : U ⟶ o₁.A) : ptOver m g = 1 ↔ g = 1 := by
  rw [← ptOver_one m]
  exact (ptOver_injective m).eq_iff

theorem ptOver_act (m : ObjMap o₁ o t) {U : Over T} (g : U ⟶ o₁.A) (c : D.O) :
    ptOver m (g ≫ o₁.act.act c) = ptOver m g ≫ o.act.act c := by
  ext
  simp [ptOver, m.act]

theorem ptOf_eq (m : ObjMap o₁ o t) (g : 𝟙_ (Over T) ⟶ o₁.A) :
    (Over.homMk (𝟙 T) (by simp) : Over.mk ((𝟙_ (Over T)).hom ≫ t) ⟶ Over.mk t) ≫ ptOf m g = ptOver m g := by
  ext
  simp [ptOf, ptOver]

theorem ptOf_injective (m : ObjMap o₁ o t) : Function.Injective (ptOf m) := by
  intro g h e
  apply ptOver_injective m
  rw [← ptOf_eq, ← ptOf_eq, e]

theorem ptOf_mul (m : ObjMap o₁ o t) (g h : 𝟙_ (Over T) ⟶ o₁.A) :
    ptOf m (g * h) = ptOf m g * ptOf m h := by
  have e := ptOf_eq m (g * h)
  rw [ptOver_mul, ← ptOf_eq, ← ptOf_eq, ← comp_mul] at e
  ext
  have e' := congrArg CommaMorphism.left e
  simpa using e'

theorem ptOf_one (m : ObjMap o₁ o t) : ptOf m (1 : 𝟙_ (Over T) ⟶ o₁.A) = 1 := by
  have h := ptOf_mul m (1 : 𝟙_ (Over T) ⟶ o₁.A) 1
  rw [_root_.mul_one] at h
  exact (mul_eq_left.mp h.symm)

theorem ptOf_act (m : ObjMap o₁ o t) (g : 𝟙_ (Over T) ⟶ o₁.A) (c : D.O) :
    ptOf m (g ≫ o₁.act.act c) = ptOf m g ≫ o.act.act c := by
  ext
  simp [ptOf, m.act]

theorem homMk_ptOf (m : ObjMap o₁ o t) {k : Type} [Field k] (x : Sp k ⟶ T) (g : 𝟙_ (Over T) ⟶ o₁.A) :
    (Over.homMk x rfl : Over.mk (x ≫ (Over.mk t).hom) ⟶ Over.mk t) ≫ ptOf m g =
      ptOver m (toUnit (Over.mk x) ≫ g) := by
  ext
  simp [ptOf, ptOver]

end GlobalTheory.UPel.HT.EtLev.PullPt

namespace GlobalTheory.UPel.HT.EtLev

open PullPt

theorem isEtLev_iff_isEtLevOver : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N : ℕ) (S T : Scheme.{0}) (s : S ⟶ Sp R) (t : T ⟶ S) (s₁ : T ⟶ Sp R) (o : Obj b N s) (o₁ : Obj b N s₁)
    (m : ObjMap o₁ o t) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (l : D.La → (𝟙_ (Over T) ⟶ o₁.A)),
    IsEtLev o₁ w0 r l ↔ IsEtLevOver o w0 r (T := Over.mk t) (fun y => ptOf m (l y)) := by
  intro p _ D R _ b N S T s t s₁ o o₁ m w0 r l
  have hadd : (∀ x y, l (x + y) = l x * l y) ↔ (∀ x y, ptOf m (l (x + y)) = ptOf m (l x) * ptOf m (l y)) := by
    refine forall₂_congr fun x y => ?_
    rw [← ptOf_mul, (ptOf_injective m).eq_iff]
  have hlin : (∀ (c : D.O) x, l (c • x) = l x ≫ o₁.act.act c) ↔
      (∀ (c : D.O) x, ptOf m (l (c • x)) = ptOf m (l x) ≫ o.act.act c) := by
    refine forall₂_congr fun c x => ?_
    rw [← ptOf_act, (ptOf_injective m).eq_iff]
  have hker : (∀ x ∈ wSub D w0 r, l x = 1) ↔ (∀ x ∈ wSub D w0 r, ptOf m (l x) = 1) := by
    refine forall₂_congr fun x _ => ?_
    rw [← ptOf_one m, (ptOf_injective m).eq_iff]
  have hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T),
      ((∀ y, toUnit (Over.mk x) ≫ l y = 1 → y ∈ wSub D w0 r) ∧
        ∀ g : Over.mk x ⟶ o₁.A, (∀ c ∈ w0 ^ r, g ≫ o₁.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
          ∃ y, toUnit (Over.mk x) ≫ l y = g) ↔
      ((∀ y, (Over.homMk x rfl : Over.mk (x ≫ (Over.mk t).hom) ⟶ Over.mk t) ≫ ptOf m (l y) = 1 → y ∈ wSub D w0 r) ∧
        ∀ g : Over.mk (x ≫ (Over.mk t).hom) ⟶ o.A,
          (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
          ∃ y, (Over.homMk x rfl : Over.mk (x ≫ (Over.mk t).hom) ⟶ Over.mk t) ≫ ptOf m (l y) = g) := by
    intro k _ _ x
    simp only [homMk_ptOf]
    refine and_congr (forall_congr' fun y => by rw [ptOver_eq_one]) ?_
    constructor
    · intro h g₀ hg₀
      obtain ⟨g, rfl⟩ := ptOver_surjective m (U := Over.mk x) g₀
      obtain ⟨y, hy⟩ := h g (fun c hc => by rw [← ptOver_eq_one m, ptOver_act]; exact hg₀ c hc)
      exact ⟨y, by rw [hy]⟩
    · intro h g hg
      obtain ⟨y, hy⟩ := h (ptOver m g) (fun c hc => by rw [← ptOver_act, ptOver_eq_one]; exact hg c hc)
      exact ⟨y, ptOver_injective m hy⟩
  unfold IsEtLev IsEtLevOver
  rw [hadd, hlin, hker]
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    (forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun x => hgeom k x)))

end GlobalTheory.UPel.HT.EtLev

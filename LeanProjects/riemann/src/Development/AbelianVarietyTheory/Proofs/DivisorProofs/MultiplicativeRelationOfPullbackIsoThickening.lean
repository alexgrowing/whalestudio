import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBLift.IsoRel

section Rel

variable {X X₀ Y Y₀ : Scheme.{0}}

abbrev Quad (i : X₀ ⟶ X) (L : LB X₀) (φ₀ φ₁ φ₂ : Y ⟶ X) : Type :=
  {p : Y.affineOpens × Small i L × Small i L × Small i L //
    p.1.1 ≤ φ₀ ⁻¹ᵁ p.2.1.1.1.1 ∧ p.1.1 ≤ φ₁ ⁻¹ᵁ p.2.2.1.1.1.1 ∧ p.1.1 ≤ φ₂ ⁻¹ᵁ p.2.2.2.1.1.1}

variable {i : X₀ ⟶ X} {L : LB X₀} {φ₀ φ₁ φ₂ : Y ⟶ X}

theorem Quad.le_W {p q : Quad i L φ₀ φ₁ φ₂} (h : p ≤ q) : p.1.1 ≤ q.1.1 :=
  (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).1

theorem Quad.le_K₀ {p q : Quad i L φ₀ φ₁ φ₂} (h : p ≤ q) : p.1.2.1 ≤ q.1.2.1 :=
  (Prod.le_def.1 (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).2).1

theorem Quad.le_K₁ {p q : Quad i L φ₀ φ₁ φ₂} (h : p ≤ q) : p.1.2.2.1 ≤ q.1.2.2.1 :=
  (Prod.le_def.1 (Prod.le_def.1 (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).2).2).1

theorem Quad.le_K₂ {p q : Quad i L φ₀ φ₁ φ₂} (h : p ≤ q) : p.1.2.2.2 ≤ q.1.2.2.2 :=
  (Prod.le_def.1 (Prod.le_def.1 (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).2).2).2

theorem Quad.le_of {p q : Quad i L φ₀ φ₁ φ₂} (hW : p.1.1 ≤ q.1.1) (h₀ : p.1.2.1 ≤ q.1.2.1) (h₁ : p.1.2.2.1 ≤ q.1.2.2.1)
    (h₂ : p.1.2.2.2 ≤ q.1.2.2.2) : p ≤ q :=
  Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨hW, Prod.le_def.2 ⟨h₀, Prod.le_def.2 ⟨h₁, h₂⟩⟩⟩)

def quadW (i : X₀ ⟶ X) (L : LB X₀) (φ₀ φ₁ φ₂ : Y ⟶ X) : (Quad i L φ₀ φ₁ φ₂)ᵒᵖ ⥤ AffOp Y :=
  (Monotone.functor (f := fun p : Quad i L φ₀ φ₁ φ₂ ↦ p.1.1) fun _ _ h ↦ Quad.le_W h).op

def quadK₀ (i : X₀ ⟶ X) (L : LB X₀) (φ₀ φ₁ φ₂ : Y ⟶ X) : (Quad i L φ₀ φ₁ φ₂)ᵒᵖ ⥤ (Small i L)ᵒᵖ :=
  (Monotone.functor (f := fun p : Quad i L φ₀ φ₁ φ₂ ↦ p.1.2.1) fun _ _ h ↦ Quad.le_K₀ h).op

def quadK₁ (i : X₀ ⟶ X) (L : LB X₀) (φ₀ φ₁ φ₂ : Y ⟶ X) : (Quad i L φ₀ φ₁ φ₂)ᵒᵖ ⥤ (Small i L)ᵒᵖ :=
  (Monotone.functor (f := fun p : Quad i L φ₀ φ₁ φ₂ ↦ p.1.2.2.1) fun _ _ h ↦ Quad.le_K₁ h).op

def quadK₂ (i : X₀ ⟶ X) (L : LB X₀) (φ₀ φ₁ φ₂ : Y ⟶ X) : (Quad i L φ₀ φ₁ φ₂)ᵒᵖ ⥤ (Small i L)ᵒᵖ :=
  (Monotone.functor (f := fun p : Quad i L φ₀ φ₁ φ₂ ↦ p.1.2.2.2) fun _ _ h ↦ Quad.le_K₂ h).op

end Rel

section SlopeTestRemainingChoices

variable {X X₀ Y Y₀ : Scheme.{0}}

theorem appLE_eq_of_eq {f g : Y ⟶ X} (e : f = g) (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (h' : V ≤ g ⁻¹ᵁ U) : f.appLE U V h = g.appLE U V h' := by
  subst e; rfl

theorem app_appLE {i : X₀ ⟶ X} {i' : Y₀ ⟶ Y} {φ : Y ⟶ X} {ψ : Y₀ ⟶ X₀} (h : ψ ≫ i = i' ≫ φ) {U : X.Opens}
    {W : Y.Opens} (le : W ≤ φ ⁻¹ᵁ U) {V₀ : X₀.Opens} (hV : i ⁻¹ᵁ U ≤ V₀) (hle : i' ⁻¹ᵁ W ≤ ψ ⁻¹ᵁ V₀) (b : Γ(X, U))
    (c : Γ(X₀, V₀)) (hc : (i.app U).hom b = (X₀.presheaf.map (homOfLE hV).op).hom c) :
    (i'.app W).hom ((φ.appLE U W le).hom b) = (ψ.appLE V₀ (i' ⁻¹ᵁ W) hle).hom c := by
  have hle' : i' ⁻¹ᵁ W ≤ (ψ ≫ i) ⁻¹ᵁ U := fun y hy ↦ by
    show (ψ ≫ i) y ∈ U
    rw [h, Scheme.Hom.comp_apply]; exact le hy
  have e1 : φ.appLE U W le ≫ i'.app W = (ψ ≫ i).appLE U (i' ⁻¹ᵁ W) hle' := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_of_eq h.symm _ _ _ _
  have e2 := congrArg (fun q ↦ q.hom b) e1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [e2, Scheme.Hom.comp_appLE, CommRingCat.hom_comp, RingHom.comp_apply, hc]
  have e3 := congrArg (fun q ↦ q.hom c) (Scheme.Hom.map_appLE ψ (U := i ⁻¹ᵁ U) (U' := V₀) hle' (homOfLE hV).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e3
  exact e3

theorem map_res_val {U V V' : X.Opens} (h : V ≤ U) (h' : V' ≤ V) (a : Γ(X, U)ˣ) :
    (X.presheaf.map (homOfLE h').op).hom (res h a).val = (res (h'.trans h) a).val := by
  change (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a.val) =
    (X.presheaf.map (homOfLE (h'.trans h)).op).hom a.val
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem isUnit_of_sqZero {A A₀ : Type} [CommRing A] [CommRing A₀] (p : A →+* A₀) (hp : Function.Surjective p)
    (K : Ideal A) (hK : K ^ 2 = ⊥) (hker : ∀ a, p a = 0 → a ∈ K) (x : A) (hx : IsUnit (p x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := hp u
  have hn : x * y - 1 ∈ K := hker _ (by simp [hu])
  have hsq : (x * y - 1) * (x * y - 1) = 0 := by
    have : (x * y - 1) * (x * y - 1) ∈ K ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hn hn
    rw [hK] at this; simpa using this
  have hnil : IsNilpotent (x * y - 1) := ⟨2, by rw [pow_two, hsq]⟩
  have : IsUnit (x * y) := by simpa using hnil.isUnit_one_add
  exact isUnit_of_mul_isUnit_left this

theorem gm_one_res_pull (f : Y ⟶ X) (y : Y) {U : X.Opens} {V : Y.Opens} (hle : V ≤ f ⁻¹ᵁ U) (h : y ∈ V)
    (a : Γ(X, U)ˣ) : gm (𝟙 Y) y V (res hle (pullU f U a)) = gm f y U a := by
  rw [gm_res (𝟙 Y) y hle h, gm_pull (𝟙 Y) f y U (hle h), Category.id_comp]

theorem commGroup_mul_eq_mul_of_eq_mul_inv_mul {G : Type} [CommGroup G] (a b w w' : G) (h : w = a * b⁻¹ * w') : a * w' = b * w := by
  rw [h, mul_comm a b⁻¹, _root_.mul_assoc b⁻¹, mul_inv_cancel_left]

end SlopeTestRemainingChoices

theorem mulRel_of_iso : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (X X₀ Y Y₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : Y ⟶ Sp R) (i : X₀ ⟶ X) (i' : Y₀ ⟶ Y) (φ₀ φ₁ φ₂ : Y ⟶ X) (w₀ : φ₀ ≫ s = s' ≫ spMap (RingHom.id R)) (w₁ : φ₁ ≫ s = s' ≫ spMap (RingHom.id R)) (w₂ : φ₂ ≫ s = s' ≫ spMap (RingHom.id R)) (ψ₀ ψ₁ ψ₂ : Y₀ ⟶ X₀) (L : LB X₀) (hL : L.IsLB) (u : C1 (smallG i L ⋙ OAff s)), IsThick I s' i' → IsBasis (smallG i L) → IsLift s i L u → ψ₀ ≫ i = i' ≫ φ₀ → ψ₁ ≫ i = i' ≫ φ₁ → ψ₂ ≫ i = i' ≫ φ₂ → GlobalTheory.CechPic.pull ψ₀ (cls L hL) = GlobalTheory.CechPic.pull ψ₁ (cls L hL) + GlobalTheory.CechPic.pull ψ₂ (cls L hL) → ∃ (T : Type) (_ : Category.{0} T) (_ : Quiver.IsThin T) (H : T ⥤ AffOp Y) (K₀ K₁ K₂ : T ⥤ (Small i L)ᵒᵖ) (le₀ : ∀ t, (H.obj t).unop.1 ≤ φ₀ ⁻¹ᵁ ((smallG i L).obj (K₀.obj t)).unop.1) (le₁ : ∀ t, (H.obj t).unop.1 ≤ φ₁ ⁻¹ᵁ ((smallG i L).obj (K₁.obj t)).unop.1) (le₂ : ∀ t, (H.obj t).unop.1 ≤ φ₂ ⁻¹ᵁ ((smallG i L).obj (K₂.obj t)).unop.1) (v : C0 (H ⋙ OAff s')), IsBasis H ∧ (∀ t, IsUnit (v t)) ∧ MulRel I (pullMap w₀ _ H K₀ le₀) (pullMap w₁ _ H K₁ le₁) (pullMap w₂ _ H K₂ le₂) u v := by
  intro R _ I hI X X₀ Y Y₀ s s' i i' φ₀ φ₁ φ₂ w₀ w₁ w₂ ψ₀ ψ₁ ψ₂ L hL u hT hB hu h₀ h₁ h₂ hcls
  have hcls' : cls (tens (L.pull ψ₁) (L.pull ψ₂)) (isLB_tens (pull_isLB hL ψ₁) (pull_isLB hL ψ₂)) =
      cls (L.pull ψ₀) (pull_isLB hL ψ₀) := hcls.symm
  obtain ⟨w, hw⟩ := (cls_eq_iff _ _).1 hcls'
  have mem : ∀ (ψ : Y₀ ⟶ X₀) (φ : Y ⟶ X), ψ ≫ i = i' ≫ φ → ∀ (q : Small i L) (W : Y.Opens),
      W ≤ φ ⁻¹ᵁ q.1.1.1 → ∀ y, i' y ∈ W → ψ y ∈ L.U q.1.2 := fun ψ φ h q W hW y hy ↦
    q.2 (show i (ψ y) ∈ q.1.1.1 by rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]; exact hW hy)
  let c : (Quad i L φ₀ φ₁ φ₂)ᵒᵖ → (LB.div (L.pull ψ₀) (tens (L.pull ψ₁) (L.pull ψ₂))).ι := fun t ↦
    ((fun _ ↦ t.unop.1.2.1.1.2), ((fun _ ↦ t.unop.1.2.2.1.1.2), (fun _ ↦ t.unop.1.2.2.2.1.2)))
  have hc : ∀ t : (Quad i L φ₀ φ₁ φ₂)ᵒᵖ,
      i' ⁻¹ᵁ t.unop.1.1.1 ≤ (LB.div (L.pull ψ₀) (tens (L.pull ψ₁) (L.pull ψ₂))).U (c t) := fun t y hy ↦
    ⟨mem_pull.2 (mem ψ₀ φ₀ h₀ _ _ t.unop.2.1 y hy), mem_pull.2 (mem ψ₁ φ₁ h₁ _ _ t.unop.2.2.1 y hy),
      mem_pull.2 (mem ψ₂ φ₂ h₂ _ _ t.unop.2.2.2 y hy)⟩
  have surj := fun t : (Quad i L φ₀ φ₁ φ₂)ᵒᵖ ↦ hT.app_surj t.unop.1.1
  let v : C0 (quadW i L φ₀ φ₁ φ₂ ⋙ OAff s') := fun t ↦ Function.surjInv (surj t) (res (hc t) (w.s (c t))).val
  have hv : ∀ t : (Quad i L φ₀ φ₁ φ₂)ᵒᵖ, (i'.app t.unop.1.1.1).hom (v t) = (res (hc t) (w.s (c t))).val :=
    fun t ↦ Function.surjInv_eq (surj t) _
  refine ⟨(Quad i L φ₀ φ₁ φ₂)ᵒᵖ, inferInstance, inferInstance, quadW i L φ₀ φ₁ φ₂, quadK₀ i L φ₀ φ₁ φ₂,
    quadK₁ i L φ₀ φ₁ φ₂, quadK₂ i L φ₀ φ₁ φ₂, fun t ↦ t.unop.2.1, fun t ↦ t.unop.2.2.1, fun t ↦ t.unop.2.2.2, v,
    ?_, ?_, ?_⟩
  · constructor
    · intro y U hy
      obtain ⟨a₀, ha₀, -⟩ := hB.cover (φ₀ y) ⊤ trivial
      obtain ⟨a₁, ha₁, -⟩ := hB.cover (φ₁ y) ⊤ trivial
      obtain ⟨a₂, ha₂, -⟩ := hB.cover (φ₂ y) ⊤ trivial
      obtain ⟨W, hW, hyW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (show y ∈ U ⊓ (φ₀ ⁻¹ᵁ ((smallG i L).obj a₀).unop.1 ⊓ (φ₁ ⁻¹ᵁ ((smallG i L).obj a₁).unop.1 ⊓
          φ₂ ⁻¹ᵁ ((smallG i L).obj a₂).unop.1)) from ⟨hy, ha₀, ha₁, ha₂⟩)
      exact ⟨Opposite.op ⟨(⟨W, hW⟩, a₀.unop, a₁.unop, a₂.unop), fun z hz ↦ (hWU hz).2.1,
        fun z hz ↦ (hWU hz).2.2.1, fun z hz ↦ (hWU hz).2.2.2⟩, hyW, fun z hz ↦ (hWU hz).1⟩
    · intro t₁ t₂ y U hy hy₁ hy₂
      obtain ⟨b₀, ⟨f₀⟩, ⟨g₀⟩, hb₀, -⟩ := hB.dir ((quadK₀ i L φ₀ φ₁ φ₂).obj t₁) ((quadK₀ i L φ₀ φ₁ φ₂).obj t₂)
        (φ₀ y) ⊤ trivial (t₁.unop.2.1 hy₁) (t₂.unop.2.1 hy₂)
      obtain ⟨b₁, ⟨f₁⟩, ⟨g₁⟩, hb₁, -⟩ := hB.dir ((quadK₁ i L φ₀ φ₁ φ₂).obj t₁) ((quadK₁ i L φ₀ φ₁ φ₂).obj t₂)
        (φ₁ y) ⊤ trivial (t₁.unop.2.2.1 hy₁) (t₂.unop.2.2.1 hy₂)
      obtain ⟨b₂, ⟨f₂⟩, ⟨g₂⟩, hb₂, -⟩ := hB.dir ((quadK₂ i L φ₀ φ₁ φ₂).obj t₁) ((quadK₂ i L φ₀ φ₁ φ₂).obj t₂)
        (φ₂ y) ⊤ trivial (t₁.unop.2.2.2 hy₁) (t₂.unop.2.2.2 hy₂)
      obtain ⟨W, hW, hyW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (show y ∈ U ⊓ (t₁.unop.1.1.1 ⊓ t₂.unop.1.1.1) ⊓ (φ₀ ⁻¹ᵁ ((smallG i L).obj b₀).unop.1 ⊓
          (φ₁ ⁻¹ᵁ ((smallG i L).obj b₁).unop.1 ⊓ φ₂ ⁻¹ᵁ ((smallG i L).obj b₂).unop.1)) from
          ⟨⟨hy, hy₁, hy₂⟩, hb₀, hb₁, hb₂⟩)
      let t₃ : (Quad i L φ₀ φ₁ φ₂)ᵒᵖ := Opposite.op ⟨(⟨W, hW⟩, b₀.unop, b₁.unop, b₂.unop),
        fun z hz ↦ (hWU hz).2.1, fun z hz ↦ (hWU hz).2.2.1, fun z hz ↦ (hWU hz).2.2.2⟩
      refine ⟨t₃, ⟨(homOfLE (Quad.le_of (p := t₃.unop) (q := t₁.unop) (fun z hz ↦ (hWU hz).1.2.1) (leOfHom f₀.unop)
          (leOfHom f₁.unop) (leOfHom f₂.unop))).op⟩,
        ⟨(homOfLE (Quad.le_of (p := t₃.unop) (q := t₂.unop) (fun z hz ↦ (hWU hz).1.2.2) (leOfHom g₀.unop)
          (leOfHom g₁.unop) (leOfHom g₂.unop))).op⟩, hyW, fun z hz ↦ (hWU hz).1.1⟩
  · intro t
    refine isUnit_of_sqZero (i'.app t.unop.1.1.1).hom (surj t) (I.map (algebraMap R (Sec s' t.unop.1.1.1)))
      (by have e := Ideal.map_pow (algebraMap R (Sec s' t.unop.1.1.1)) I 2; rw [hI, Ideal.map_bot] at e; exact e.symm) (fun a ha ↦ (hT.ker t.unop.1.1 a).1 ha) (v t) ?_
    rw [hv t]; exact Units.isUnit _
  · intro t t' a
    have le : t'.unop ≤ t.unop := leOfHom a.unop
    have hWle : t'.unop.1.1.1 ≤ t.unop.1.1.1 := Quad.le_W le
    have hV : i' ⁻¹ᵁ t'.unop.1.1.1 ≤ i' ⁻¹ᵁ t.unop.1.1.1 := fun y hy ↦ hWle hy
    refine (hT.ker t'.unop.1.1 _).1 ?_
    have ek : ∀ (ψ : Y₀ ⟶ X₀) (φ : Y ⟶ X) (hψ : ψ ≫ i = i' ≫ φ) (p q : (Small i L)ᵒᵖ) (f : p ⟶ q)
        (le' : t'.unop.1.1.1 ≤ φ ⁻¹ᵁ q.unop.1.1.1)
        (hle : i' ⁻¹ᵁ t'.unop.1.1.1 ≤ ψ ⁻¹ᵁ (L.U p.unop.1.2 ⊓ L.U q.unop.1.2)),
        (i'.app t'.unop.1.1.1).hom ((φ.appLE _ t'.unop.1.1.1 le').hom (u p q f)) =
          (res hle (pullU ψ _ (L.g p.unop.1.2 q.unop.1.2))).val := fun ψ φ hψ p q f le' hle ↦
      (app_appLE hψ le' (Small.le_inf f) hle _ _ (hu p q f)).trans rfl
    have hle₀ : i' ⁻¹ᵁ t'.unop.1.1.1 ≤ ψ₀ ⁻¹ᵁ (L.U t.unop.1.2.1.1.2 ⊓ L.U t'.unop.1.2.1.1.2) := fun y hy ↦
      ⟨mem ψ₀ φ₀ h₀ _ _ t.unop.2.1 y (hV hy), mem ψ₀ φ₀ h₀ _ _ t'.unop.2.1 y hy⟩
    have hle₁ : i' ⁻¹ᵁ t'.unop.1.1.1 ≤ ψ₁ ⁻¹ᵁ (L.U t.unop.1.2.2.1.1.2 ⊓ L.U t'.unop.1.2.2.1.1.2) := fun y hy ↦
      ⟨mem ψ₁ φ₁ h₁ _ _ t.unop.2.2.1 y (hV hy), mem ψ₁ φ₁ h₁ _ _ t'.unop.2.2.1 y hy⟩
    have hle₂ : i' ⁻¹ᵁ t'.unop.1.1.1 ≤ ψ₂ ⁻¹ᵁ (L.U t.unop.1.2.2.2.1.2 ⊓ L.U t'.unop.1.2.2.2.1.2) := fun y hy ↦
      ⟨mem ψ₂ φ₂ h₂ _ _ t.unop.2.2.2 y (hV hy), mem ψ₂ φ₂ h₂ _ _ t'.unop.2.2.2 y hy⟩
    have e₀ := ek ψ₀ φ₀ h₀ _ _ ((quadK₀ i L φ₀ φ₁ φ₂).map a) (t'.unop.2.1) hle₀
    have e₁ := ek ψ₁ φ₁ h₁ _ _ ((quadK₁ i L φ₀ φ₁ φ₂).map a) (t'.unop.2.2.1) hle₁
    have e₂ := ek ψ₂ φ₂ h₂ _ _ ((quadK₂ i L φ₀ φ₁ φ₂).map a) (t'.unop.2.2.2) hle₂
    have emp : (i'.app t'.unop.1.1.1).hom (mp (quadW i L φ₀ φ₁ φ₂ ⋙ OAff s') a (v t)) =
        (res (hV.trans (hc t)) (w.s (c t))).val := by
      have n := congrArg (fun q ↦ q.hom (v t)) (i'.naturality (homOfLE hWle).op)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at n
      refine n.trans ?_
      show (Y₀.presheaf.map _).hom ((i'.app t.unop.1.1.1).hom (v t)) = _
      rw [hv t]
      exact map_res_val (hc t) hV _
    have key : res hle₀ (pullU ψ₀ _ (L.g t.unop.1.2.1.1.2 t'.unop.1.2.1.1.2)) * res (hc t') (w.s (c t')) =
        res hle₁ (pullU ψ₁ _ (L.g t.unop.1.2.2.1.1.2 t'.unop.1.2.2.1.1.2)) *
          res hle₂ (pullU ψ₂ _ (L.g t.unop.1.2.2.2.1.2 t'.unop.1.2.2.2.1.2)) * res (hV.trans (hc t)) (w.s (c t)) := by
      refine unit_ext fun y hy ↦ ?_
      have hp := hc t (hV hy)
      have hq := hc t' hy
      have g := (isGen_iff_germ w).1 hw y (c t) (c t') hp hq
      rw [gm_div' (L.pull ψ₀) (tens (L.pull ψ₁) (L.pull ψ₂)) (𝟙 Y₀) y (c t) (c t') hp hq,
        gm_pull_g L ψ₀ (𝟙 Y₀) y _ _ hp.1 hq.1,
        gm_tens (L.pull ψ₁) (L.pull ψ₂) (𝟙 Y₀) y _ _ hp.2 hq.2, gm_pull_g L ψ₁ (𝟙 Y₀) y _ _ hp.2.1 hq.2.1,
        gm_pull_g L ψ₂ (𝟙 Y₀) y _ _ hp.2.2 hq.2.2, Category.id_comp, Category.id_comp, Category.id_comp] at g
      simp only [map_mul, gm_one_res_pull _ y _ hy, gm_res (𝟙 Y₀) y _ hy]
      exact commGroup_mul_eq_mul_of_eq_mul_inv_mul _ _ _ _ g
    have kv := congrArg Units.val key
    simp only [Units.val_mul] at kv
    beta_reduce
    refine (map_sub (i'.app t'.unop.1.1.1).hom _ _).trans (sub_eq_zero.2 ?_)
    refine ((map_mul (i'.app t'.unop.1.1.1).hom _ _).trans ?_).trans (((map_mul (i'.app t'.unop.1.1.1).hom _ _).trans
      (congrArg (· * _) (map_mul (i'.app t'.unop.1.1.1).hom _ _))).symm)
    erw [emp, hv t', e₀, e₁, e₂]
    exact kv

end GlobalTheory.LBLift.IsoRel

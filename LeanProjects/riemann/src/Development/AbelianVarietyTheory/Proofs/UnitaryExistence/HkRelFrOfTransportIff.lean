import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HeckeFr
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.FibrePushforward
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

noncomputable section

namespace GlobalTheory.HeckeFrCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori

attribute [local instance] Over.cartesianMonoidalCategory

theorem ext_of_points {Ω : Type} [Field Ω] [IsAlgClosed Ω] {T Y Z : Scheme.{0}} (t : T ⟶ Sp Ω)
    [LocallyOfFiniteType t] [IsReduced T] (s : Y ⟶ Z) [IsSeparated s] {f g : T ⟶ Y} (H' : f ≫ s = g ≫ s)
    (Hq : ∀ q : Sp Ω ⟶ T, q ≫ t = 𝟙 _ → q ≫ f = q ≫ g) : f = g := by
  have : JacobsonSpace ↥T := LocallyOfFiniteType.jacobsonSpace t
  refine ext_of_fromSpecResidueField_eq f g s (closedPoints T) ?_ ?_ H'
  · rw [dense_iff_closure_eq, closure_closedPoints]
  · intro x hx
    rw [← cancel_epi (Spec.map (residueFieldIsoBase t x hx).hom)]
    have := Hq _ (pointOfClosedPoint_comp t x hx)
    simpa only [pointOfClosedPoint, Category.assoc] using this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

section Swap

variable {Ω : Type} [CommRing Ω]

def swap (x : Sp Ω ⟶ Xo.X) : Gx x ≅ pullback Xo.univ.t.G.hom x := pullbackSymmetry x Xo.univ.t.G.hom

@[reassoc] theorem swap_hom_fst (x : Sp Ω ⟶ Xo.X) :
    (swap x).hom ≫ pullback.fst _ _ = (snd (Over.mk x) Xo.univ.t.G).left := pullbackSymmetry_hom_comp_fst _ _

@[reassoc] theorem swap_hom_snd (x : Sp Ω ⟶ Xo.X) :
    (swap x).hom ≫ pullback.snd _ _ = (fst (Over.mk x) Xo.univ.t.G).left := pullbackSymmetry_hom_comp_snd _ _

@[reassoc] theorem swap_inv_fst (x : Sp Ω ⟶ Xo.X) :
    (swap x).inv ≫ (fst (Over.mk x) Xo.univ.t.G).left = pullback.snd _ _ := by
  rw [← swap_hom_snd, Iso.inv_hom_id_assoc]

@[reassoc] theorem swap_inv_snd (x : Sp Ω ⟶ Xo.X) :
    (swap x).inv ≫ (snd (Over.mk x) Xo.univ.t.G).left = pullback.fst _ _ := by
  rw [← swap_hom_fst, Iso.inv_hom_id_assoc]

def conj (x x' : Sp Ω ⟶ Xo.X) :
    (pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x') ≃ (Gx x ⟶ Gx x') where
  toFun ψ := (swap x).hom ≫ ψ ≫ (swap x').inv
  invFun ψ := (swap x).inv ≫ ψ ≫ (swap x').hom
  left_inv ψ := by simp
  right_inv ψ := by simp

theorem conj_apply {x x' : Sp Ω ⟶ Xo.X} (ψ : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x') :
    conj x x' ψ = (swap x).hom ≫ ψ ≫ (swap x').inv := rfl

theorem gx_ext {x : Sp Ω ⟶ Xo.X} {T : Scheme.{0}} {f g : T ⟶ Gx x}
    (h₁ : f ≫ (fst (Over.mk x) Xo.univ.t.G).left = g ≫ (fst (Over.mk x) Xo.univ.t.G).left)
    (h₂ : f ≫ (snd (Over.mk x) Xo.univ.t.G).left = g ≫ (snd (Over.mk x) Xo.univ.t.G).left) : f = g :=
  pullback.hom_ext h₁ h₂

@[reassoc] theorem lift_l_fst {S : Scheme.{0}} {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) :
    (lift a b).left ≫ (fst X Y).left = a.left := by rw [← Over.comp_left, lift_fst]

@[reassoc] theorem lift_l_snd {S : Scheme.{0}} {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) :
    (lift a b).left ≫ (snd X Y).left = b.left := by rw [← Over.comp_left, lift_snd]

@[reassoc] theorem toFib_fst (x : Sp Ω ⟶ Xo.X) {T : Scheme.{0}} (t : T ⟶ Sp Ω)
    (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) : toFib x t a ≫ (fst (Over.mk x) Xo.univ.t.G).left = t :=
  lift_l_fst _ _

@[reassoc] theorem toFib_snd (x : Sp Ω ⟶ Xo.X) {T : Scheme.{0}} (t : T ⟶ Sp Ω)
    (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) : toFib x t a ≫ (snd (Over.mk x) Xo.univ.t.G).left = a.left :=
  lift_l_snd _ _

@[reassoc] theorem snd_hom (x : Sp Ω ⟶ Xo.X) : (snd (Over.mk x) Xo.univ.t.G).left ≫ Xo.univ.t.G.hom =
    (fst (Over.mk x) Xo.univ.t.G).left ≫ x :=
  (Over.w (snd (Over.mk x) Xo.univ.t.G)).trans (Over.w (fst (Over.mk x) Xo.univ.t.G)).symm

theorem over_iff {x x' : Sp Ω ⟶ Xo.X} (ψ : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x') :
    conj x x' ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left ↔
      ψ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [conj_apply, Category.assoc, Category.assoc, swap_inv_fst, ← swap_hom_snd, cancel_epi]

theorem sends_unique {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'} {a : Over.mk x ⟶ Xo.univ.t.G}
    {b b' : Over.mk x' ⟶ Xo.univ.t.G} (h : Sends ψ a b) (h' : Sends ψ a b') : b = b' := by
  have e := congrArg (· ≫ (snd (Over.mk x') Xo.univ.t.G).left) (h.symm.trans h')
  simp only [lift_l_snd] at e
  exact Over.OverMorphism.ext e

theorem sends_iff {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'}
    (hψ : ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (a : Over.mk x ⟶ Xo.univ.t.G) (b : Over.mk x' ⟶ Xo.univ.t.G) :
    Sends ψ a b ↔ (lift (𝟙 (Over.mk x)) a).left ≫ ψ ≫ (snd (Over.mk x') Xo.univ.t.G).left = b.left := by
  refine ⟨fun h => ?_, fun h => gx_ext ?_ ?_⟩
  · rw [← Category.assoc, show _ ≫ ψ = _ from h, lift_l_snd]
  · rw [Category.assoc, hψ, lift_l_fst, lift_l_fst]; rfl
  · rw [Category.assoc, h, lift_l_snd]

theorem push_hom {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'}
    (hψ : ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    {T : Scheme.{0}} (t : T ⟶ Sp Ω) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    push ψ t a ≫ Xo.univ.t.G.hom = t ≫ x' := by
  simp only [push, Category.assoc]
  rw [snd_hom, reassoc_of% hψ, toFib_fst_assoc]

def res (x : Sp Ω ⟶ Xo.X) {T T' : Scheme.{0}} {t : T ⟶ Sp Ω} {t' : T' ⟶ Sp Ω} (q : T' ⟶ T) (hq : q ≫ t = t') :
    (Over.mk (t' ≫ x) : Over Xo.X) ⟶ Over.mk (t ≫ x) :=
  Over.homMk q (by simp [← hq])

theorem toFib_res (x : Sp Ω ⟶ Xo.X) {T T' : Scheme.{0}} {t : T ⟶ Sp Ω} {t' : T' ⟶ Sp Ω} (q : T' ⟶ T)
    (hq : q ≫ t = t') (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    toFib x t' (res x q hq ≫ a) = q ≫ toFib x t a := by
  refine gx_ext ?_ ?_
  · rw [toFib_fst, Category.assoc, toFib_fst, hq]
  · rw [toFib_snd, Category.assoc, toFib_snd]; rfl

theorem push_res {x x' : Sp Ω ⟶ Xo.X} (ψ : Gx x ⟶ Gx x') {T T' : Scheme.{0}} {t : T ⟶ Sp Ω} {t' : T' ⟶ Sp Ω}
    (q : T' ⟶ T) (hq : q ≫ t = t') (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    push ψ t' (res x q hq ≫ a) = q ≫ push ψ t a := by
  rw [push, push, toFib_res, Category.assoc]

def sec' (x : Sp Ω ⟶ Xo.X) {T : Scheme.{0}} {t : T ⟶ Sp Ω} (q : Sp Ω ⟶ T) (hq : q ≫ t = 𝟙 _) :
    (Over.mk x : Over Xo.X) ⟶ Over.mk (t ≫ x) :=
  Over.homMk q (by simp [reassoc_of% hq])

theorem lift_sec' (x : Sp Ω ⟶ Xo.X) {T : Scheme.{0}} {t : T ⟶ Sp Ω} (q : Sp Ω ⟶ T) (hq : q ≫ t = 𝟙 _)
    (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    (lift (𝟙 (Over.mk x)) (sec' x q hq ≫ a)).left = q ≫ toFib x t a := by
  refine gx_ext ?_ ?_
  · rw [lift_l_fst, Category.assoc, toFib_fst, hq]; rfl
  · rw [lift_l_snd, Category.assoc, toFib_snd]; rfl

theorem sends_sec'_iff {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'}
    (hψ : ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    {T : Scheme.{0}} {t : T ⟶ Sp Ω} (q : Sp Ω ⟶ T) (hq : q ≫ t = 𝟙 _)
    (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) (b : Over.mk x' ⟶ Xo.univ.t.G) :
    Sends ψ (sec' x q hq ≫ a) b ↔ q ≫ push ψ t a = b.left := by
  rw [sends_iff hψ, lift_sec', push, Category.assoc]

end Swap

theorem fibPt_swap {Ω : Type} [Field Ω] {x : Sp Ω ⟶ Xo.X} (a : Over.mk x ⟶ Xo.univ.t.G) :
    (lift (𝟙 (Over.mk x)) a).left ≫ (swap x).hom = fibPt _ a := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, swap_hom_fst, lift_l_snd, fibPt, pullback.lift_fst]
  · rw [Category.assoc, swap_hom_snd, lift_l_fst, fibPt, pullback.lift_snd]; rfl

theorem sends_conj_iff {Ω : Type} [Field Ω] {x x' : Sp Ω ⟶ Xo.X}
    (ψ : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x')
    (a : Over.mk x ⟶ Xo.univ.t.G) (b : Over.mk x' ⟶ Xo.univ.t.G) :
    Sends (conj x x' ψ) a b ↔ fibPt _ a ≫ ψ = fibPt _ b := by
  rw [Sends, conj_apply, ← fibPt_swap, ← fibPt_swap, ← Category.assoc, ← Category.assoc, Iso.comp_inv_eq]

section Hom

variable {Ω : Type} [CommRing Ω] {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'}

theorem lift_act (x : Sp Ω ⟶ Xo.X) (a : Over.mk x ⟶ Xo.univ.t.G) (f : Xo.univ.t.G ⟶ Xo.univ.t.G) :
    (lift (𝟙 (Over.mk x)) (a ≫ f)).left = (lift (𝟙 (Over.mk x)) a).left ≫ (Over.mk x ◁ f).left := by
  rw [← Over.comp_left, lift_whiskerLeft]

theorem exists_pointHom (h : IsLinHom ψ) :
    ∃ ψp : (Over.mk x ⟶ Xo.univ.t.G) →* (Over.mk x' ⟶ Xo.univ.t.G), (∀ a, Sends ψ a (ψp a)) ∧
      ∀ r a, ψp (a ≫ Xo.univ.t.act.act r) = ψp a ≫ Xo.univ.t.act.act r := by
  obtain ⟨h0, hm, ha⟩ := h
  let f : (Over.mk x ⟶ Xo.univ.t.G) → (Over.mk x' ⟶ Xo.univ.t.G) := fun a =>
    Over.homMk ((lift (𝟙 (Over.mk x)) a).left ≫ ψ ≫ (snd (Over.mk x') Xo.univ.t.G).left) (by
      simp only [Category.assoc]
      rw [snd_hom, reassoc_of% h0, lift_l_fst_assoc]
      exact Category.id_comp _)
  have hf : ∀ a, Sends ψ a (f a) := fun a => (sends_iff h0 _ _).2 rfl
  let k : ∀ z : Sp Ω ⟶ Xo.X, (Over.mk (𝟙 _ ≫ z) : Over Xo.X) ⟶ Over.mk z := fun z => Over.homMk (𝟙 _) rfl
  have hk : ∀ a : Over.mk x ⟶ Xo.univ.t.G, sec' x (𝟙 _) (Category.id_comp _) ≫ k x ≫ a = a := fun a =>
    Over.OverMorphism.ext ((Category.id_comp _).trans (Category.id_comp _))
  have hs : ∀ a b, Sends ψ a b ↔ (k x' ≫ b).left = push ψ (𝟙 _) (k x ≫ a) := fun a b => by
    have := sends_sec'_iff h0 (𝟙 _) (Category.id_comp (𝟙 _)) (k x ≫ a) b
    rw [hk, Category.id_comp] at this
    rw [this, eq_comm]
    exact Iff.of_eq (congrArg (· = _) (Category.id_comp _).symm)
  refine ⟨MonoidHom.mk' f fun a b => sends_unique (hf _) ?_, hf, fun r a => sends_unique (hf _) ?_⟩
  · rw [hs, MonObj.comp_mul, MonObj.comp_mul]
    exact hm _ _ _ _ _ _ ((hs _ _).1 (hf a)) ((hs _ _).1 (hf b))
  · show Sends ψ _ (f a ≫ _)
    rw [Sends, lift_act, lift_act, Category.assoc, ha, ← Category.assoc, show _ ≫ ψ = _ from hf a]

end Hom

section Geom

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'}

theorem isLinHom_of_pointHom
    (h0 : ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (ψp : (Over.mk x ⟶ Xo.univ.t.G) →* (Over.mk x' ⟶ Xo.univ.t.G)) (hf : ∀ a, Sends ψ a (ψp a))
    (ha : ∀ r a, ψp (a ≫ Xo.univ.t.act.act r) = ψp a ≫ Xo.univ.t.act.act r) : IsLinHom ψ := by
  have := Xo.univ.t.semi.smooth
  have := Xo.univ.t.semi.separated
  refine ⟨h0, fun T t a₁ a₂ b₁ b₂ h₁ h₂ => ?_, fun r => ?_⟩
  · let G := Xo.univ.t.G
    let t₀ : (Over.mk x ⊗ (G ⊗ G)).left ⟶ Sp Ω := (fst (Over.mk x) (G ⊗ G)).left
    have : Smooth (G ⊗ G).hom := by
      show Smooth (pullback.fst G.hom G.hom ≫ G.hom)
      infer_instance
    have : Smooth t₀ := by
      show Smooth (pullback.fst x (G ⊗ G).hom)
      infer_instance
    have : IsReduced (Over.mk x ⊗ (G ⊗ G)).left := GlobalTheory.isReduced_of_smooth_of_isReduced t₀
    let s₀ : (Over.mk (t₀ ≫ x) : Over Xo.X) ⟶ G ⊗ G :=
      Over.homMk (snd (Over.mk x) (G ⊗ G)).left
        ((Over.w (snd (Over.mk x) (G ⊗ G))).trans (Over.w (fst (Over.mk x) (G ⊗ G))).symm)
    let v : (Over.mk (t₀ ≫ x) ⟶ G) → (Over.mk (t₀ ≫ x') ⟶ G) := fun u =>
      Over.homMk (push ψ t₀ u) (push_hom h0 t₀ u)
    have key : ∀ u₁ u₂, (v u₁ * v u₂).left = push ψ t₀ (u₁ * u₂) := fun u₁ u₂ => by
      refine ext_of_points t₀ G.hom ((Over.w _).trans (push_hom h0 _ _).symm) fun q hq => ?_
      have e : ∀ u, sec' x' q hq ≫ v u = ψp (sec' x q hq ≫ u) := fun u =>
        sends_unique ((sends_sec'_iff h0 q hq u _).2 rfl) (hf _)
      rw [(sends_sec'_iff h0 q hq _ _).1 (hf _), MonObj.comp_mul, map_mul, ← e, ← e, ← MonObj.comp_mul]
      rfl
    let q : T ⟶ (Over.mk x ⊗ (G ⊗ G)).left :=
      (lift (Over.homMk t rfl : Over.mk (t ≫ x) ⟶ Over.mk x) (lift a₁ a₂)).left
    have hq : q ≫ t₀ = t := lift_l_fst _ _
    have hs : res x q hq ≫ s₀ = lift a₁ a₂ := Over.OverMorphism.ext (lift_l_snd _ _)
    have e₁ : a₁ = res x q hq ≫ s₀ ≫ fst G G := by rw [reassoc_of% hs, lift_fst]
    have e₂ : a₂ = res x q hq ≫ s₀ ≫ snd G G := by rw [reassoc_of% hs, lift_snd]
    have f₁ : b₁ = res x' q hq ≫ v (s₀ ≫ fst G G) :=
      Over.OverMorphism.ext (h₁.trans (by rw [e₁, push_res]; rfl))
    have f₂ : b₂ = res x' q hq ≫ v (s₀ ≫ snd G G) :=
      Over.OverMorphism.ext (h₂.trans (by rw [e₂, push_res]; rfl))
    rw [e₁, e₂, f₁, f₂, ← MonObj.comp_mul, ← MonObj.comp_mul, push_res, ← key]
    rfl
  · have : Smooth (fst (Over.mk x) Xo.univ.t.G).left := by
      show Smooth (pullback.fst x Xo.univ.t.G.hom)
      infer_instance
    have : IsSeparated (fst (Over.mk x') Xo.univ.t.G).left := by
      show IsSeparated (pullback.fst x' Xo.univ.t.G.hom)
      infer_instance
    have : IsReduced (Over.mk x).left := inferInstanceAs (IsReduced (Sp Ω))
    have : IsReduced (Gx x) := GlobalTheory.isReduced_of_smooth_of_isReduced (fst (Over.mk x) Xo.univ.t.G).left
    have hw : ∀ z : Sp Ω ⟶ Xo.X, (Over.mk z ◁ Xo.univ.t.act.act r).left ≫ (fst (Over.mk z) Xo.univ.t.G).left =
        (fst (Over.mk z) Xo.univ.t.G).left := fun z => by rw [← Over.comp_left, whiskerLeft_fst]
    refine ext_of_points (fst (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x') Xo.univ.t.G).left
      (by rw [Category.assoc, Category.assoc, h0, hw, hw, h0]) fun q hq => ?_
    let a : Over.mk x ⟶ Xo.univ.t.G := Over.homMk (q ≫ (snd (Over.mk x) Xo.univ.t.G).left) (by
      rw [Category.assoc, snd_hom, reassoc_of% hq]; rfl)
    have e : q = (lift (𝟙 (Over.mk x)) a).left := by
      refine gx_ext ?_ ?_
      · rw [hq, lift_l_fst]; rfl
      · rw [lift_l_snd]; rfl
    have s₁ := hf (a ≫ Xo.univ.t.act.act r)
    rw [ha, Sends, lift_act, lift_act, ← show _ ≫ ψ = _ from hf a] at s₁
    rw [e]
    simpa only [Category.assoc] using s₁

end Geom

section Level

theorem nsmul_congr {A M : Type} [AddCommGroup A] [Monoid M] (f : A → M) (hadd : ∀ a b, f (a + b) = f a * f b)
    (N : ℕ) (hN : ∀ a, f (N • a) = 1) {m n : ℕ} (h : m ≡ n [MOD N]) (a : A) : f (m • a) = f (n • a) := by
  have key : ∀ k : ℕ, f (k • a) = f ((k % N) • a) := fun k => by
    conv_lhs => rw [← Nat.mod_add_div k N, add_smul, hadd, mul_smul, hN, _root_.mul_one]
  rw [key m, key n, h]

theorem eta_level (a : Dw.La) : Xo.univ.eta (l.M' • a) = 1 := by
  obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  refine Xo.univ.eta_ker _ ?_
  have h : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]
    exact Ideal.mem_span_singleton_self _
  have hle : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb := by
    exact Ideal.mul_le.2 fun r hr s _ => Ideal.mul_mem_right _ _ hr
  have h' : (l.M : 𝓞 E) ∈ l.Mb := hle h
  have e : l.M' • a = (l.M : 𝓞 E) • (k • a) := by rw [hk, mul_smul, Nat.cast_smul_eq_nsmul]
  rw [e]
  exact Submodule.smul_mem_smul h' Submodule.mem_top

theorem etaA_level (a : Dw.La) : Xo.univ.etaA (l.M' • a) = 1 := by
  obtain ⟨k, hk⟩ : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
  rw [hk, mul_smul, Xo.univ.etaA_ker]

theorem level_iff {A M P P' : Type} [AddCommGroup A] [Monoid M] (f : A → M) (hadd : ∀ a b, f (a + b) = f a * f b)
    (N : ℕ) (hN : ∀ a, f (N • a) = 1) {p : ℕ} (hp : p.Coprime N) (hN0 : N ≠ 0) (i : M → P) (i' : M → P')
    (g : P → P') :
    (∀ p' : ℕ, p * p' ≡ 1 [MOD N] → ∀ a, g (i (f (p' • a))) = i' (f a)) ↔ ∀ a, g (i (f a)) = i' (f (p • a)) := by
  refine ⟨fun h a => ?_, fun h p' hp' a => ?_⟩
  · obtain ⟨p', hp'⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hp hN0
    have hp' : p * p' ≡ 1 [MOD N] := hp'.2
    rw [← h p' hp', smul_smul, nsmul_congr f hadd N hN (mul_comm p p' ▸ hp'), one_smul]
  · rw [h, smul_smul, nsmul_congr f hadd N hN hp', one_smul]

theorem level_ne_zero (l : Level H) : l.M' ≠ 0 :=
  Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'

end Level

theorem pointHom_unique {Ω : Type} [Field Ω] [IsAlgClosed Ω] {p : ℕ} {x x' : Sp Ω ⟶ Xo.X}
    {C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)} {ψ : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x'}
    {f g : (Over.mk x ⟶ Xo.univ.t.G) →* (Over.mk x' ⟶ Xo.univ.t.G)} (hf : IsHkIsog p x x' C ψ f)
    (hg : IsHkIsog p x x' C ψ g) : f = g :=
  MonoidHom.ext fun a =>
    sends_unique ((sends_conj_iff ψ _ _).2 (hf.2.2.1 a)) ((sends_conj_iff ψ _ _).2 (hg.2.2.1 a))

theorem isog_iff {Ω : Type} [Field Ω] [IsAlgClosed Ω] {p : ℕ} (hp : p.Coprime l.M') (x x' : Sp Ω ⟶ Xo.X)
    (C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)) (ψ : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x') :
    (∃ ψp, IsHkIsog p x x' C ψ ψp) ↔ IsHeckeIsog p C (conj x x' ψ) := by
  have lev := fun g : (Over.mk x ⟶ Xo.univ.t.G) → (Over.mk x' ⟶ Xo.univ.t.G) =>
    level_iff Xo.univ.eta Xo.univ.eta_add l.M' eta_level hp (level_ne_zero l) (fun e => toUnit _ ≫ e)
      (fun e => toUnit _ ≫ e) g
  have levA := fun g : (Over.mk x ⟶ Xo.univ.t.G) → (Over.mk x' ⟶ Xo.univ.t.G) =>
    level_iff Xo.univ.etaA Xo.univ.etaA_add l.M' etaA_level hp (level_ne_zero l) (fun e => toUnit _ ≫ e)
      (fun e => toUnit _ ≫ e) g
  constructor
  · rintro ⟨ψp, hs, h0, hf, ha, hsurj, hker, hW, hl⟩
    have h0' := (over_iff ψ).2 h0
    have hf' : ∀ a, Sends (conj x x' ψ) a (ψp a) := fun a => (sends_conj_iff ψ _ _).2 (hf a)
    have hiff : ∀ a b, Sends (conj x x' ψ) a b ↔ ψp a = b := fun a b =>
      ⟨fun h => sends_unique (hf' a) h, fun h => h ▸ hf' a⟩
    refine ⟨hs, isLinHom_of_pointHom h0' ψp hf' ha, fun b => ?_, fun a => ?_,
      fun n a₁ a₂ b₁ b₂ e hn h₁ h₂ hw => ?_, fun a => ?_, fun a => ?_⟩
    · obtain ⟨a, rfl⟩ := hsurj b
      exact ⟨a, hf' a⟩
    · rw [hiff, ← hker, MonoidHom.mem_ker]
    · rw [← (hiff _ _).1 h₁, ← (hiff _ _).1 h₂]
      exact hW n a₁ a₂ e hn hw
    · exact (hiff _ _).2 ((lev ψp).1 (fun p' h a => (hl p' h a).1) a)
    · exact (hiff _ _).2 ((levA ψp).1 (fun p' h a => (hl p' h a).2) a)
  · rintro ⟨hs, hlin, hsurj, hker, hW, hl, hlA⟩
    obtain ⟨ψp, hf', ha⟩ := exists_pointHom hlin
    have hiff : ∀ a b, Sends (conj x x' ψ) a b ↔ ψp a = b := fun a b =>
      ⟨fun h => sends_unique (hf' a) h, fun h => h ▸ hf' a⟩
    refine ⟨ψp, hs, (over_iff ψ).1 hlin.1, fun a => (sends_conj_iff ψ _ _).1 (hf' a), ha, fun b => ?_, ?_,
      fun n a₁ a₂ e hn hw => hW n _ _ _ _ e hn (hf' _) (hf' _) hw, fun p' h a => ⟨?_, ?_⟩⟩
    · obtain ⟨a, h⟩ := hsurj b
      exact ⟨a, (hiff _ _).1 h⟩
    · ext a
      rw [MonoidHom.mem_ker, ← hiff, hker]
    · exact (lev ψp).2 (fun a => (hiff _ _).1 (hl a)) p' h a
    · exact (levA ψp).2 (fun a => (hiff _ _).1 (hlA a)) p' h a

theorem eps_cancel {Ω : Type} [Field Ω] {a b : Ω} (h : a * b = 1) :
    spMap (epsMul a) ≫ spMap (epsMul b) = 𝟙 _ := by
  have : (epsMul a).comp (epsMul b) = RingHom.id _ := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [epsMul, ← _root_.mul_assoc, h]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, this]
  exact Spec.map_id _

theorem lie_iff {Ω : Type} [Field Ω] {p : ℕ} (hp : (p : Ω) ≠ 0) {x x' : Sp Ω ⟶ Xo.X}
    (ψ : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x')
    (v w : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left) :
    (IsTanAt x v ∧ IsTanAt x' w ∧ IsLieImageH p ψ v w) ↔ IsLieImg p (conj x x' ψ) v w := by
  refine and_congr_right fun hv => and_congr_right fun _ => ?_
  have hpush : ∀ a : tEps x ⟶ Xo.univ.t.G, push (conj x x' ψ) (spMap (algebraMap Ω (DualNumber Ω))) a =
      (toFib x _ a ≫ (swap x).hom) ≫ ψ ≫ pullback.fst _ _ := fun a => by
    simp only [push, conj_apply, Category.assoc, swap_inv_snd]
  constructor
  · rintro ⟨u, h₁, h₂, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a : tEps x ⟶ Xo.univ.t.G, a.left = v := ⟨Over.homMk v hv.1, rfl⟩
    refine ⟨a, ha, ?_⟩
    have : toFib x _ a ≫ (swap x).hom = u := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, swap_hom_fst, toFib_snd, h₁, ha]
      · rw [Category.assoc, swap_hom_snd, toFib_fst, h₂]
    rw [hpush, this, ← Category.assoc, eps_cancel (mul_inv_cancel₀ hp), Category.id_comp]
  · rintro ⟨a, rfl, h⟩
    refine ⟨toFib x _ a ≫ (swap x).hom, ?_, ?_, ?_⟩
    · rw [Category.assoc, swap_hom_fst, toFib_snd]
    · rw [Category.assoc, swap_hom_snd, toFib_fst]
    · rw [← hpush, ← h, ← Category.assoc, eps_cancel (inv_mul_cancel₀ hp), Category.id_comp]

variable {c : Coeff l} {𝔓 : Ideal (𝓞 E)} {p : ℕ}

theorem idx_eq (h : IsSplitOff l 𝔓 p) (i : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
    (y : FrPt Xo c Ω) : hkKer (Xo := Xo) 𝔓 p i Ω y = HeckeIdx Xo c h i Ω y := rfl

theorem hkPt_iff (h : IsSplitOff l 𝔓 p) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
    (sTr : ∀ (y z : FrPt Xo c Ω), (pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x) → Prop)
    (y : FrPt Xo c Ω) (C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G)) (z : FrPt Xo c Ω) :
    HkPt p sTr y C z ↔ ∃ ψ : Gx y.x ⟶ Gx z.x, IsHeckeIsog p C ψ ∧ (∀ τ j, IsLieImg p ψ (y.u τ j) (z.u τ j)) ∧
      sTr y z ((conj y.x z.x).symm ψ) := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap c.F Ω).injective
  have hp : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 h.2.2.1.ne_zero
  have hc : p.Coprime l.M' := (Nat.Prime.coprime_iff_not_dvd h.2.2.1).2 h.2.2.2.2
  rw [← (conj y.x z.x).exists_congr_right]
  refine exists_congr fun ψ => ?_
  rw [← isog_iff hc, Equiv.symm_apply_apply, exists_and_right]
  refine and_congr_right fun _ => and_congr_left fun _ => forall₂_congr fun τ j => ?_
  rw [← lie_iff hp]
  exact ⟨fun h => ⟨y.tan τ j, z.tan τ j, h⟩, fun h => h.2.2⟩

theorem hkRelFr_iff (h : IsSplitOff l 𝔓 p) (i : ℕ)
    (sTr : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y z : FrPt Xo c Ω),
      (pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x) → Prop)
    (tr : Transport Xo c) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω)
    (C : hkKer (Xo := Xo) 𝔓 p i Ω y) (z : FrPt Xo c Ω)
    (htr : ∀ ψ, sTr Ω y z ψ ↔ tr Ω y.x z.x (conj y.x z.x ψ) y.s z.s) :
    hkRelFr 𝔓 p i sTr Ω y C z ↔ IsHeckePt Xo c tr h i Ω y C z := by
  rw [hkRelFr, hkPt_iff h]
  simp only [htr, Equiv.apply_symm_apply]
  exact Iff.rfl

def ofTransport (tr : Transport Xo c) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y z : FrPt Xo c Ω)
    (ψ : pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x) : Prop :=
  tr Ω y.x z.x (conj y.x z.x ψ) y.s z.s

theorem hkRelFr_ofTransport_iff (h : IsSplitOff l 𝔓 p) (i : ℕ) (tr : Transport Xo c) (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) (C : hkKer (Xo := Xo) 𝔓 p i Ω y) (z : FrPt Xo c Ω) :
    hkRelFr 𝔓 p i (ofTransport tr) Ω y C z ↔ IsHeckePt Xo c tr h i Ω y C z :=
  hkRelFr_iff h i _ tr Ω y C z fun _ => Iff.rfl

end GlobalTheory.HeckeFrCompare

import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramedBaseChange

theorem spec_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  RingHom.ext fun x => by ext <;> simp [dualMap]

theorem spec_algHom_id (K : Type) [Field K] (T : Type) [CommRing T] [Algebra K T] :
    spMap (AlgHom.id K T).toRingHom = 𝟙 _ := by
  simp [spMap]

theorem dual_id (T : Type) [CommRing T] : dualMap (RingHom.id T) = RingHom.id _ :=
  RingHom.ext fun x => by
    show TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd = x
    exact TrivSqZeroExt.inl_fst_add_inr_snd_eq x

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) : f.appLE U V hf = g.appLE U V hg := by
  subst e
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem chart_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem pulledGroup_hom_ext {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {W : Scheme.{0}} (a b : W ⟶ Gx x)
    (hs : a ≫ (snd (Over.mk x) Xo.univ.t.G).left = b ≫ (snd (Over.mk x) Xo.univ.t.G).left)
    (hf : a ≫ (fst (Over.mk x) Xo.univ.t.G).left = b ≫ (fst (Over.mk x) Xo.univ.t.G).left) : a = b := by
  have hw : a ≫ (Over.mk x ⊗ Xo.univ.t.G).hom = b ≫ (Over.mk x ⊗ Xo.univ.t.G).hom := by
    have e1 := Over.w (snd (Over.mk x) Xo.univ.t.G)
    rw [← e1, ← Category.assoc, hs, Category.assoc]
  let a' : Over.mk (a ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk a rfl
  let b' : Over.mk (a ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk b hw.symm
  have e : a' = b' := by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.OverMorphism.ext hf
    · exact Over.OverMorphism.ext hs
  exact congrArg CommaMorphism.left e

theorem refl {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    FrMap (AlgHom.id c.F S) y y := by
  have eid := spec_algHom_id c.F S
  have did : spMap (dualMap (AlgHom.id c.F S).toRingHom) = 𝟙 _ := by
    show spMap (dualMap (RingHom.id S)) = _
    rw [dual_id]
    simp [spMap]
  refine ⟨by rw [eid, Category.id_comp], fun τ i => by rw [did, Category.id_comp], 𝟙 _,
    Category.id_comp _, by rw [eid]; exact (Category.id_comp _).trans (Category.comp_id _).symm, ?_⟩
  intro i h
  have e : Scheme.Hom.appLE (𝟙 (Gx y.x)) ((PPx y.x).U i) ((PPx y.x).U i) h = 𝟙 _ := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    refine (Category.id_comp _).trans ?_
    rw [← (Gx y.x).presheaf.map_id]
    rfl
  rw [e, CommRingCat.hom_id, RingHom.id_apply]

theorem trans {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) {y : FrPt Xo c S} {z : FrPt Xo c T} {w : FrPt Xo c U}
    (h₁ : FrMap φ y z) (h₂ : FrMap ψ z w) : FrMap (ψ.comp φ) y w := by
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  have esp : spMap (ψ.comp φ).toRingHom = spMap ψ.toRingHom ≫ spMap φ.toRingHom := by
    exact spec_comp φ.toRingHom ψ.toRingHom
  have edsp : spMap (dualMap (ψ.comp φ).toRingHom) =
      spMap (dualMap ψ.toRingHom) ≫ spMap (dualMap φ.toRingHom) := by
    show spMap (dualMap (ψ.toRingHom.comp φ.toRingHom)) = _
    rw [dual_comp, spec_comp]
  refine ⟨?_, ?_, pm2 ≫ pm1, ?_, ?_, ?_⟩
  · rw [hx2, hx1, esp, Category.assoc]
  · intro τ i
    rw [hu2 τ i, hu1 τ i, edsp, Category.assoc]
  · rw [Category.assoc, hs1, hs2]
  · rw [Category.assoc, hf1, ← Category.assoc, hf2, esp, Category.assoc]
  · intro i h
    have h1' := chart_le pm1 hs1 i
    have h2' := chart_le pm2 hs2 i
    have e : (pm2 ≫ pm1).appLE _ _ h = pm1.appLE _ _ h1' ≫ pm2.appLE _ _ h2' :=
      (Scheme.Hom.appLE_comp_appLE pm2 pm1 _ _ _ h1' h2').symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, ha1 i h1', ha2 i h2']

theorem cancel {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] (φ : S →ₐ[c.F] T) (κ : T →ₐ[c.F] U) {y0 : FrPt Xo c S} {y : FrPt Xo c T} {z : FrPt Xo c U}
    (h₁ : FrMap φ y0 y) (h₂ : FrMap (κ.comp φ) y0 z) : FrMap κ y z := by
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  have esp : spMap (κ.comp φ).toRingHom = spMap κ.toRingHom ≫ spMap φ.toRingHom :=
    spec_comp φ.toRingHom κ.toRingHom
  have edsp : spMap (dualMap (κ.comp φ).toRingHom) =
      spMap (dualMap κ.toRingHom) ≫ spMap (dualMap φ.toRingHom) := by
    show spMap (dualMap (κ.toRingHom.comp φ.toRingHom)) = _
    rw [dual_comp, spec_comp]
  have hx : spMap κ.toRingHom ≫ y.x = z.x := by rw [hx2, hx1, esp, Category.assoc]
  let pm : Gx z.x ⟶ Gx y.x :=
    ((Over.homMk (spMap κ.toRingHom) hx : Over.mk z.x ⟶ Over.mk y.x) ▷ Xo.univ.t.G).left
  have hs : pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have hf : pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left =
      (fst (Over.mk z.x) Xo.univ.t.G).left ≫ spMap κ.toRingHom := by
    rw [← Over.comp_left, whiskerRight_fst]
    rfl
  have hcomp : pm ≫ pm1 = pm2 := by
    apply pulledGroup_hom_ext
    · rw [Category.assoc, hs1, hs, hs2]
    · rw [Category.assoc, hf1, ← Category.assoc, hf, Category.assoc, ← esp, hf2]
  refine ⟨?_, ?_, pm, hs, hf, ?_⟩
  · rw [hx2, hx1, esp, Category.assoc]
  · intro τ i
    rw [hu2 τ i, hu1 τ i, edsp, Category.assoc]
  · intro i h
    have h1' := chart_le pm1 hs1 i
    have h2' := chart_le pm2 hs2 i
    rw [← ha1 i h1', ← ha2 i h2']
    have e : pm1.appLE _ _ h1' ≫ pm.appLE _ _ h = pm2.appLE ((PPx y0.x).U i) ((PPx z.x).U i) h2' := by
      rw [Scheme.Hom.appLE_comp_appLE]
      exact appLE_eq_of_eq hcomp _ _ _ _
    rw [← e, CommRingCat.hom_comp, RingHom.comp_apply]

theorem unique {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z z' : FrPt Xo c T} (h₁ : FrMap φ y z) (h₂ : FrMap φ y z') :
    z = z' := by
  obtain ⟨x1, o1, u1, tan1, eig1, basis1, s1, gen1⟩ := z
  obtain ⟨x2, o2, u2, tan2, eig2, basis2, s2, gen2⟩ := z'
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  dsimp only at hx1 hu1 pm1 hs1 hf1 ha1 hx2 hu2 pm2 hs2 hf2 ha2
  have hx : x1 = x2 := hx1.trans hx2.symm
  subst hx
  have hu : u1 = u2 := funext fun τ => funext fun i => (hu1 τ i).trans (hu2 τ i).symm
  subst hu
  have hpm : pm1 = pm2 := pulledGroup_hom_ext _ _ (hs1.trans hs2.symm) (hf1.trans hf2.symm)
  subst hpm
  have hsf : s1.f = s2.f := funext fun i =>
    (ha1 i (chart_le pm1 hs1 i)).symm.trans (ha2 i (chart_le pm1 hs1 i))
  obtain ⟨f1, c1⟩ := s1
  obtain ⟨f2, c2⟩ := s2
  dsimp only at hsf
  subst hsf
  rfl

theorem isPullSec {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap φ y z)
    (h : ptO Xo z.x ⟶ ptO Xo y.x) (hh : h.left = spMap φ.toRingHom) :
    IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) y.s z.s := by
  obtain ⟨hx, hu, pm, hs, hf, ha⟩ := hm
  have hpm : pm = (h ▷ Xo.univ.t.G).left := by
    apply pulledGroup_hom_ext
    · rw [hs, ← Over.comp_left, whiskerRight_snd]
    · rw [hf, ← Over.comp_left, whiskerRight_fst, Over.comp_left, hh]
  subst hpm
  intro j
  exact (ha j (chart_le _ hs j)).symm

end GlobalTheory.FramedBaseChange

namespace GlobalTheory

theorem framedPoint_baseChange_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), FrMap (AlgHom.id c.F S) y y) ∧ (∀ (S T U : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U] [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) (y : FrPt Xo c S) (z : FrPt Xo c T) (w : FrPt Xo c U), FrMap φ y z → (FrMap ψ z w ↔ FrMap (ψ.comp φ) y w)) ∧ (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z z' : FrPt Xo c T), FrMap φ y z → FrMap φ y z' → z = z') ∧ ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → ∀ h : ptO Xo z.x ⟶ ptO Xo y.x, h.left = spMap φ.toRingHom → IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) y.s z.s :=
  fun _ _ _ _ _ _ _ _ _ =>
    ⟨fun _ _ _ y => FramedBaseChange.refl y,
     fun _ _ _ _ _ _ _ _ _ φ ψ _ _ _ h₁ =>
       ⟨fun h₂ => FramedBaseChange.trans φ ψ h₁ h₂, fun h₂ => FramedBaseChange.cancel φ ψ h₁ h₂⟩,
     fun _ _ _ _ _ _ φ _ _ _ h₁ h₂ => FramedBaseChange.unique φ h₁ h₂,
     fun _ _ _ _ _ _ φ _ _ hm h hh => FramedBaseChange.isPullSec φ hm h hh⟩

end GlobalTheory

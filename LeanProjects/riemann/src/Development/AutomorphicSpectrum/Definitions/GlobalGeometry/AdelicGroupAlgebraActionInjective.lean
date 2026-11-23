import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ProIsoAt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure HostAut (H : Host E) where

  σ : E ≃+* E
  fix : σ (H.rt : E) = H.rt

namespace HostAut

def refl (H : Host E) : HostAut H := ⟨RingEquiv.refl E, rfl⟩

def symm (g : HostAut H) : HostAut H := ⟨g.σ.symm, by rw [RingEquiv.symm_apply_eq, g.fix]⟩

def s (g : HostAut H) : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv g.σ

theorem coe_integer_automorphism (g : HostAut H) (a : 𝓞 E) : ((g.s a : 𝓞 E) : E) = g.σ (a : E) := rfl

theorem s_rt (g : HostAut H) : g.s H.rt = H.rt := RingOfIntegers.ext (by rw [coe_integer_automorphism]; exact g.fix)

theorem integer_automorphism_fixes_weight (g : HostAut H) : g.s H.w0 = H.w0 := by
  have h := congrArg g.s H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, s_rt, map_ofNat, ← H.two_weight_eq_one_add_root] at h
  exact mul_left_cancel₀ two_ne_zero h

theorem s_bar (g : HostAut H) (a : 𝓞 E) : g.s (H.bar a) = H.bar (g.s a) := by
  apply RingOfIntegers.ext
  show g.σ ((H.bar a : 𝓞 E) : E) = ((H.bar (g.s a) : 𝓞 E) : E)
  rw [H.bar_eq, H.bar_eq, coe_integer_automorphism]
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj]
  exact IsCMField.complexEmbedding_complexConj E (φ.comp g.σ.toRingHom) (a : E)

end HostAut

def twistAct {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct O G) (s : O ≃+* O) :
    OAct O G where
  act a := act.act (s a)
  hom a := act.hom (s a)
  one := by rw [map_one, act.one]
  mul a b := by rw [map_mul, act.mul]
  add a b := by rw [map_add, act.add]

def twistSAB {S : Scheme.{0}} (t : SAB H S) (g : HostAut H) : SAB H S where
  G := t.G
  semi := t.semi
  act := twistAct t.act g.s
  PP := t.PP
  cub := t.cub
  sym := t.sym
  adj a := by
    show LBIso _ (cubeLB t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.act (g.s (H.bar a))] t.PP.L)
    rw [g.s_bar]
    exact t.adj (g.s a)
  prim := by
    show LBIso _ (cubeLB t.G ![𝟙 t.G, t.act.act (g.s H.w0)] t.PP.L)
    rw [g.integer_automorphism_fixes_weight]
    exact t.prim

def TwMod {O : Type} [CommRing O] (_s : O ≃+* O) (L : Type) : Type := L

instance {O : Type} [CommRing O] (s : O ≃+* O) (L : Type) [AddCommGroup L] : AddCommGroup (TwMod s L) :=
  inferInstanceAs (AddCommGroup L)

instance {O : Type} [CommRing O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L] : Module O (TwMod s L) :=
  Module.compHom L s.toRingHom

def twForm (D : Datum H) (g : HostAut H) : LinearMap.BilinForm ℤ (TwMod g.s D.La) := D.EF

abbrev TwIso (D : Datum H) (g : HostAut H) : Type := ProIso (𝓞 E) D.EF (twForm D g)

variable {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

def TwOK (o : Obj D l b s) (g : HostAut H) (a : TwIso D g) : Prop :=
  (∀ x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La), o.eta (a.a l.M x) = 1) ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k), x ≫ s = spMap β →
    DetCond D (twistAct o.t.act g.s) x (β b.ρ) ∧
    ∃ I : TateIso D k (Over.mk x ⟶ o.t.G) (fun c y => y ≫ o.t.act.act (g.s c))
        (fun n y y' c => Out.WeilIs o.t.G o.t.PP.L n y y' (unitOn c)),
      (I.ζ l.A : k) = β b.ζ ∧ (∀ y, toUnit _ ≫ o.etaA (a.a l.A y) = I.ev l.A y) ∧
      ∀ y ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        toUnit _ ≫ o.eta (a.a l.M y) = I.ev l.M y

def twistObj (o : Obj D l b s) (g : HostAut H) (a : TwIso D g) (h : TwOK o g a) : Obj D l b s where
  t := twistSAB o.t g
  proper := o.proper
  ample := o.ample
  ktriv := o.ktriv
  eta x := o.eta (a.a l.M x)
  eta_add x y := by rw [map_add]; exact o.eta_add _ _
  eta_ker := h.1
  etaA x := o.etaA (a.a l.A x)
  etaA_add x y := by rw [map_add]; exact o.etaA_add _ _
  etaA_ker x := by rw [map_nsmul]; exact o.etaA_ker _
  geom := h.2

def twistMap {S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (g : HostAut H) :
    SABMap (twistSAB t' g) (twistSAB t g) f where
  cm := m.cm
  cart := m.cart
  base := m.base
  act c := m.act (g.s c)
  lin := m.lin

end GlobalTheory.CompanionTheory.Ar

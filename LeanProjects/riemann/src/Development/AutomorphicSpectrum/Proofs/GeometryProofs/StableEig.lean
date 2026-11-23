import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

def zPt {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift z.x (spMap (algebraMap c.F S)) (by
    rw [z.x_over]
    simp only [Formalism.L2.Pj.sOf, spMap, ← Spec.map_comp]
    rfl)

@[reassoc (attr := simp)]
theorem zPt_fst {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) :
    zPt z ≫ pullback.fst _ _ = z.x := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem zPt_snd {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) :
    zPt z ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := pullback.lift_snd _ _ _

theorem eq_zPt {S B : Type} [CommRing S] [Algebra c.F S] [CommRing B] (z : Formalism.L2.Pj.FrPt Xo c S)
    (ψ : S →+* B) (y : Sp B ⟶ Xo.XF c) (h₁ : under y = spMap ψ ≫ z.x)
    (h₂ : y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F S))) : y = spMap ψ ≫ zPt z := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, zPt_fst]; exact h₁
  · rw [Category.assoc, zPt_snd, h₂]
    simp only [spMap, ← Spec.map_comp]
    rfl

def Tied {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {B : Type} [CommRing B] (y : Sp B ⟶ Xo.XF c)
    (v : Sp (DualNumber B) ⟶ Xo.univ.t.G.left) (v' : Sp (DualNumber B) ⟶ Y.t.G.left) : Prop :=
  ∃ u : Sp (DualNumber B) ⟶ Y.oF.t.G.left, u ≫ Y.oF.t.G.hom = spMap (algebraMap B (DualNumber B)) ≫ y ∧
    u ≫ Y.m0.toSABMap.φ = v ∧ u ≫ Y.m.φ = v'

def StableEig {X : Scheme.{0}} (t : SAB H X) {A : Type} [CommRing A] (x : Sp A ⟶ X) (κ : c.F →+* A) (σ : E →+* ℂ)
    {r : ℕ} (e : Fin r → (epsAt x ⟶ t.G)) : Prop :=
  ∀ (T : Type) [CommRing T] (θ : A →+* T) (x' : Sp T ⟶ X), spMap θ ≫ x = x' →
    ∀ v : Fin r → (epsAt x' ⟶ t.G), (∀ i, (v i).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ (e i).left) →
      IsEigFrame t.act x' ((θ.comp κ).comp (tauIn c σ)) v

end GlobalTheory.CompanionTheory.Ar.LocFn

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidArc

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FractionGeneratorsArcs

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj Classical

def GeneratesFrac {O F : Type} [CommRing O] [Field F] (β : O →+* F) : Prop :=
  ∀ x : F, ∃ r s : O, β s ≠ 0 ∧ x * β s = β r

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

def UnivCompat {O₁ O₂ : Type} [CommRing O₁] [CommRing O₂] {β₁ : O₁ →+* c.F} {β₂ : O₂ →+* c.F}
    (Y₁ : Model Xo c β₁) (Y₂ : Model Xo c β₂) {S : Scheme.{0}} {t : SAB H S} {χ₁ : S ⟶ Y₁.X} {χ₂ : S ⟶ Y₂.X}
    (m₁ : SABMap t Y₁.t χ₁) (m₂ : SABMap t Y₂.t χ₂) : Prop :=
  ∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Y₁.oF.t.G.left) (g₂ : T ⟶ Y₂.oF.t.G.left),
    g ≫ m₁.φ = g₁ ≫ Y₁.m.φ → g₁ ≫ Y₁.m0.toSABMap.φ = g₂ ≫ Y₂.m0.toSABMap.φ →
    g₁ ≫ Y₁.oF.t.G.hom = g₂ ≫ Y₂.oF.t.G.hom → g ≫ m₂.φ = g₂ ≫ Y₂.m.φ

def SameWitness {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}
    {O₁ O₂ : Type} [CommRing O₁] [CommRing O₂] {β₁ : O₁ →+* c.F} {β₂ : O₂ →+* c.F}
    {Y₁ : Model Xo c β₁} {Y₂ : Model Xo c β₂}
    {χ₁ : Sp (PowerSeries k) ⟶ Y₁.X} {χ₂ : Sp (PowerSeries k) ⟶ Y₂.X}
    (W₁ : ArcWit Y₁ (a.restrict β₁) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ₁)
    (W₂ : ArcWit Y₂ (a.restrict β₂) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ₂) : Prop :=
  ∃ (m₂ : SABMap W₁.t Y₂.t χ₂) (h : _),
    W₂ = { t := W₁.t, m := m₂, P := W₁.P, φ := W₁.φ, he := W₁.he, w := W₁.w, e := W₁.e, spec := h } ∧
    UnivCompat Y₁ Y₂ W₁.m m₂

def OneArc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O₀ O₁ O₂ : Type) [CommRing O₀] [CommRing O₁] [CommRing O₂]
    (β₀ : O₀ →+* c.F) (β₁ : O₁ →+* c.F) (β₂ : O₂ →+* c.F) (b₁ : O₀ →+* O₁) (b₂ : O₀ →+* O₂)
    (Y₀ : Model Xo c β₀) (Y₁ : Model Xo c β₁) (Y₂ : Model Xo c β₂),
    β₁.comp b₁ = β₀ → β₂.comp b₂ = β₀ → GeneratesFrac β₁ → GeneratesFrac β₂ →
    Dominates Y₀ Y₁ b₁ → Dominates Y₀ Y₂ b₂ →
    ∀ (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
      (χ₁ : Sp (PowerSeries k) ⟶ Y₁.X)
      (W₁ : ArcWit Y₁ (a.restrict β₁) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ₁)
      (y : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c),
      χ₁ ≫ Y₁.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp β₁) →
      y ≫ Y₁.j = Out.jK (PowerSeries k) ≫ χ₁ →
      ∃ (χ₂ : Sp (PowerSeries k) ⟶ Y₂.X)
        (W₂ : ArcWit Y₂ (a.restrict β₂) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ₂),
        χ₂ ≫ Y₂.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp β₂) ∧
        y ≫ Y₂.j = Out.jK (PowerSeries k) ≫ χ₂ ∧ SameWitness W₁ W₂

example {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}
    {O₁ O₂ : Type} [CommRing O₁] [CommRing O₂] {β₁ : O₁ →+* c.F} {β₂ : O₂ →+* c.F}
    {Y₁ : Model Xo c β₁} {Y₂ : Model Xo c β₂}
    {χ₁ : Sp (PowerSeries k) ⟶ Y₁.X} {χ₂ : Sp (PowerSeries k) ⟶ Y₂.X}
    (W₁ : ArcWit Y₁ (a.restrict β₁) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ₁)
    (W₂ : ArcWit Y₂ (a.restrict β₂) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ₂)
    (h : SameWitness W₁ W₂) : W₂.t = W₁.t ∧ HEq W₂.P W₁.P := by
  obtain ⟨m, h', rfl, -⟩ := h
  exact ⟨rfl, HEq.rfl⟩

example {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}
    {O₁ : Type} [CommRing O₁] {β₁ : O₁ →+* c.F} {Y₁ : Model Xo c β₁} {χ₁ : Sp (PowerSeries k) ⟶ Y₁.X}
    (W₁ : ArcWit Y₁ (a.restrict β₁) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ₁) :
    SameWitness W₁ W₁ := by
  refine ⟨W₁.m, W₁.spec, rfl, ?_⟩
  intro T g g₁ g₂ h₁ h₂ h₃
  have : g₁ = g₂ := Y₁.m0.toSABMap.cart.1.hom_ext h₂ h₃
  rw [h₁, this]

end GlobalTheory.IndefiniteRowSideFullHecke.FractionGeneratorsArcs

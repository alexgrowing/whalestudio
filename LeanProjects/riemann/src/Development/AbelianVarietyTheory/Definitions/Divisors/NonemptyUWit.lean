import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {cf : Coeff l} {C : UCompact Xo cf}

structure UWit (X : USetup C) where

  G : Over (Sp X.Ω₁)
  [grp : GrpObj G]

  α : G.left ⟶ X.ρ.P.A.left

  β : G.left ⟶ Xo.univ.t.G.left
  hα : IsGrpPullback G X.ρ.P.A (spMap X.S.R.val.toRingHom) α
  hβ : IsGrpPullback G Xo.univ.t.G (X.uΩ ≫ pullback.fst _ _) β
  hL : LBIso (X.ρ.P.L.pull α) (Xo.univ.t.PP.L.pull β)

attribute [instance] UWit.grp

theorem nonempty_uWit (X : USetup C) : Nonempty (UWit X) := by
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := X.pulled_uΩ
  exact ⟨{ G := G, α := α, β := β, hα := hα, hβ := hβ, hL := hL }⟩

def UIsLabW (X : USetup C) (wi : UWit X) {p : ℕ} [Fact p.Prime] {z : X.M.Z} (ct : UCTrait X p z)
    (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) : Prop :=
  ∃ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b)
    (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R')
    (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (u' : Sp (ratHull R') ⟶ Xo.XF cf),
    USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ spMap (ratHull R').val.toRingHom ≫ u' = X.uΩ ∧
    R' ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) ∧
    ∃ (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left),
      IsGrpPullback G ρ'.P.A (spMap (toRat R')) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧
      LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
      (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull R').val.toRingHom) m ∧ m ≫ β = wi.β ∧
        ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
          w ≫ m ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt x).left) ∧
      ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X.M.val (gPt p ≫ ct.y) a) ∧
        ∃ (u : ρ'.UTest p y₀) (lb : u.Lab) (j : u.D.toPre.X ≃+ ct.T.P.D.toPre.X),
          (∀ χ, lb.q χ = ct.sc * (ct.T.be (j χ) (j χ) : ℝ) / 2) ∧
          (∀ a χ, lb.yy a = QuotientAddGroup.mk χ → yy a = QuotientAddGroup.mk (j χ)) ∧
          ∀ (m : ℕ) (a : 𝓞 E) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
            (w w' : Sp (PadicAlgCl p) ⟶ G.left), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x →
            QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → w ≫ α = x.left ≫ u.φ → w' ≫ α = x'.left ≫ u.φ →
            w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → CongMod m (j pk'.y) (a • j pk.y)

theorem UIsLabW.uIsLab {X : USetup C} {wi : UWit X} {p : ℕ} [Fact p.Prime] {z : X.M.Z} {ct : UCTrait X p z}
    {yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X} (h : UIsLabW X wi ct yy) : UIsLab X ct yy := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', h₁, h₂, h₃, h₄, G, _, α, β, h₅, h₆, h₇, -, h₈⟩ := h
  exact ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', h₁, h₂, h₃, h₄, G, _, α, β, h₅, h₆, h₇, h₈⟩

def UDeep.Comparison₂ {X₁ : USetup C} (Dp : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit Dp.X) : Prop :=
  ∃ m : w₂.G.left ⟶ w₁.G.left, IsGrpPullback w₂.G w₁.G (spMap (algebraMap X₁.Ω₁ Dp.X.Ω₁)) m ∧ m ≫ w₁.β = w₂.β ∧
    ∀ x, ∃ w : Sp Dp.X.Ω₁ ⟶ w₂.G.left,
      w ≫ m ≫ w₁.α = spMap (algebraMap X₁.Ω₁ Dp.X.Ω₁) ≫ spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧
      w ≫ w₂.α = spMap Dp.X.S.R.val.toRingHom ≫ (Dp.X.ρ.pt (Dp.lab x)).left

end GlobalTheory.UPoinc

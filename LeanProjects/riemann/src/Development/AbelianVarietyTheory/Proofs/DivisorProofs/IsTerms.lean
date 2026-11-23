import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtChar
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UT
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSum

section
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

def UTerms (u : ρ.UTest p y₀) (x₀ : S.Gam) {C X : Type} [AddCommGroup X] (lab : C → S.Gam) (j : u.D.toPre.X ≃+ X)
    (T : X → C → PadicAlgCl p) : Prop :=
  ∃ (Φ : u.Geom) (w₀ : W0 u.U.toUnifPre) (ϑ : Fam u.D.toPre (PadicAlgCl p) 1)
    (pk : C → QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (w : ∀ c, GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) 1 (pk c).g.b),
    NormW u.U.toUnifPre w₀ Φ.rig ∧ u.U.ExpandsF (PadicAlgCl p) 1 w₀ Φ.th ϑ ∧
    (∀ c, (pk c).y = 0 ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) (pk c) (Φ.pt (lab c)) ∧ (w c).IsGen ∧
      ∀ k : ℕ, 1 ≤ k → ∀ wk : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k (pk c).g.b, wk.IsGen →
        (∀ z J, Good u.D.toPre.P.L z J → val wk (𝟙 _) z J = val (w c) (𝟙 _) z J ^ k) →
        ∀ (s : SecA u.A (PadicAlgCl p) k) (s' : Fam u.D.toPre (PadicAlgCl p) k) (v : PadicAlgCl p),
          u.U.ExpandsF (PadicAlgCl p) k w₀ s s' → ValAt s (Φ.pt (lab c)) (Φ.fr (lab c)) v →
          SumF (maximalIdeal u.V) (PadicAlgCl p) (coef s' (pk c).g wk) v) ∧
    ∀ (mu : X) (c : C), T mu c * y₀ ⟨S.th x₀, S.th_mem x₀⟩ = coef ϑ (pk c).g (w c) (j.symm mu)

end

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

def IsTerms (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) {p : ℕ} [Fact p.Prime] {z : X.M.Z}
    (c : CTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)) (x₀ : X.S.Gam)
    (t : (Fin 8 → c.T.D.toPre.X) → X.S.HH X.M z → PadicAlgCl p) : Prop :=
  ∃ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b)
    (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R')
    (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)),
    Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧
    R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧
    ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) ∧
      ∃ (u : ρ'.UTest p y₀) (l : u.Lab) (j : u.D.toPre.X ≃+ (Fin 8 → c.T.D.toPre.X)),
        (∀ χ, l.q χ = c.sc * (qW W c.T.β (j χ) : ℤ)) ∧
        (∀ a χ, l.yy a = QuotientAddGroup.mk χ → yy a = QuotientAddGroup.mk (j χ)) ∧
        (∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
          (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x →
          QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ (ε' E).left →
          CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b)) ∧
        UTerms u x₀ (fun κ : X.S.HH X.M z => (κ : X.S.Gam)) j t

end GlobalTheory.Poinc.GSum

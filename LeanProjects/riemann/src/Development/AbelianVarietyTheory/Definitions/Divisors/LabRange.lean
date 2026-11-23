import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

@[reducible] def GlobalTheory.ZH.ThetaSys.rechart {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (c : Ω) (hc : c ≠ 0)
    (R' : Subalgebra o Ω) (fg : R'.FG) (frac : ∀ x : Ω, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c * S.th x ∈ R')
    (hev : ∀ x i, c * S.ev x i ∈ R') : ThetaSys o Ω :=
  { S with
    th := fun x => c * S.th x
    ev := fun x i => c * S.ev x i
    R := R'
    fg := fg
    frac := frac
    th_mem := hth
    ev_mem := hev
    supp := by simpa [hc] using S.supp
    th_ne := S.th_ne.imp fun _ h => mul_ne_zero hc h }

namespace GlobalTheory.Poinc

variable {g n : ℕ}

open MonObj in

def IsDiagEnd (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {T : Scheme.{0}} (P : PolAV T) (u : T ⟶ F.X)
    (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) : Prop :=
  ∃ c : SiegPre g n (zetaAway n) (u ≫ F.s), SiegPB c F.univ u ∧ ∃ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) ∧
    (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y a) ∧
    LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) ∧
    ∀ E a, ε E ≫ pr a = ((List.finRange 8).map fun b => pr b ^ E a b).prod

def Same {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} (ρ : S.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (ρ' : S'.Real)
    (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)) (lab : S.Gam → S'.Gam) (φ : Ω →+* Ω') : Prop :=
  ∃ (P₀ : PolAV (Sp Ω')) (a : P₀.A.left ⟶ ρ.P.A.left) (a' : P₀.A.left ⟶ ρ'.P.A.left)
    (ε₀ : Matrix (Fin 8) (Fin 8) ℤ → (P₀.A ⟶ P₀.A)),
    IsGrpPullback P₀.A ρ.P.A (spMap (φ.comp S.R.val.toRingHom)) a ∧ IsGrpPullback P₀.A ρ'.P.A (spMap S'.R.val.toRingHom) a' ∧
    LBIso P₀.L (ρ.P.L.pull a) ∧ LBIso P₀.L (ρ'.P.L.pull a') ∧
    (∀ E, (ε₀ E).left ≫ a = a ≫ (ε E).left ∧ (ε₀ E).left ≫ a' = a' ≫ (ε' E).left) ∧
    ∀ x, ∃ w : Sp Ω' ⟶ P₀.A.left, w ≫ a = spMap (φ.comp S.R.val.toRingHom) ≫ (ρ.pt x).left ∧
      w ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt (lab x)).left

variable {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

abbrev ModN (m : ℕ) (X : Type) [AddCommGroup X] : Type := X ⧸ (nsmulAddMonoidHom m : X →+ X).range

def IsLab (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) {p : ℕ} [Fact p.Prime] {z : X.M.Z}
    (c : CTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)) : Prop :=
  ∃ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b)
    (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R')
    (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)),
    Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧
    R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧
    ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) ∧
      ∃ (u : ρ'.UTest p y₀) (l : u.Lab) (j : u.D.toPre.X ≃+ (Fin 8 → c.T.D.toPre.X)),
        (∀ χ, l.q χ = c.sc * (qW W c.T.β (j χ) : ℤ)) ∧
        (∀ a χ, l.yy a = QuotientAddGroup.mk χ → yy a = QuotientAddGroup.mk (j χ)) ∧
        ∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
          (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x →
          QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ (ε' E).left →
          CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b)

structure Deep (X₁ : Setup F W i) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) where

  X : Setup F W i

  ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)
  diag : IsDiagEnd F W X.ρ.P X.u ε
  [alg : Algebra X₁.Ω₁ X.Ω₁]
  fd : FiniteDimensional X₁.Ω₁ X.Ω₁
  gal : IsGalois X₁.Ω₁ X.Ω₁
  proj : IsProjOver X.M.s

  q : X.M.Z ⟶ X₁.M.Z
  fin : IsFinite q
  gen : X.M.pt ≫ q = spMap (algebraMap X₁.Ω₁ X.Ω₁) ≫ X₁.M.pt
  comp : q ≫ X₁.π = X.π

  m : ℕ
  sq : X.S.N = m ^ 2
  dvd : X₁.S.r * X₁.S.N ∣ m

  lab : X₁.S.Gam →+ X.S.Gam
  same : Same X₁.ρ ε₁ X.ρ ε lab (algebraMap X₁.Ω₁ X.Ω₁)
  lab_range : ∀ x : X.S.Gam, ∃ a, lab a = (X.S.r * X.S.N / (X₁.S.r * X₁.S.N)) • x

attribute [instance] Deep.alg

namespace Deep

variable {X₁ : Setup F W i} {ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (D : Deep X₁ ε₁)

@[reducible] def lift {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) :
    CTrait D.X p (y (cPt p)) where
  y := y
  cen := rfl
  T := c.T
  ι := c.ι
  int := c.int
  comm := by rw [← D.comp, ← Category.assoc y, h, c.comm]

def Compat {X : Type} [AddCommGroup X] (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) X)
    (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) X) : Prop :=
  ∀ a μ, yy₁ a = QuotientAddGroup.mk μ →
    yy (D.lab a) = QuotientAddGroup.mk ((D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) • μ)

end Deep

end GlobalTheory.Poinc

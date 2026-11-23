import Mathlib
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

def SquaresS {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {T : RootTower Ψ N} (R : RealTower T)
    (II : IntersectionSystem) : Prop :=
  ∀ B c, ∃ (m : ℝ) (d : ℕ) (S : PB.AnSys (d + 1) (Ψ × Fin N)) (K : Type) (_ : Fintype K) (ι : K → Type)
    (_ : ∀ k, Fintype (ι k)) (P : Ideal (MRing ι)) (Re : PB.Realis S P), 0 < m ∧ Nonempty (PB.FlagSys Re T.j) ∧
      PB.toWt (Re.PB II) = m • (R.tie B c).Re.PBwt II ∧ S.degPoly = m • ((R.Sys c).comap some).degPoly

def AntisymmetryFibreSquares : Prop :=
  PB.Antisymmetry → PB.AgreementPos → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N) (R : RealTower T),
      SquaresS R II → T.I8 II (hhFl Ψ N II)

def StCmp : Prop :=
  PB.Inputs → Cmp.CmpSt → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
      (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (n : ℕ)
      (M M' : RootModel (CMType H) (D.p + D.q)) (T : Cmp.HodgeTie Y S n M) (T' : Cmp.HodgeTie Y S n M'),
      Mono (spMap β) → GlobalTheory.CompanionTheory.Ar.genPt T.A.ξ₀ = GlobalTheory.CompanionTheory.Ar.genPt T'.A.ξ₀ → (∀ p ∈ S, T'.A.R p = T.A.R p) →
      T.Re.deg = 1 → T'.Re.deg = T'.Fl.deg →
      T.Re.PB II = (T.Fl.deg : ℝ) • T'.Re.PB II ∧ T.Sy.degPoly = (T.Fl.deg : ℝ) • T'.Sy.degPoly

def StX : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e : ℕ) (S : PB.AnSys e (Ψ × Fin N)) (Re : PB.Realis S P) (sing : Ψ × Fin N → HermLine ι),
    0 < S.t₀ → (∀ a, (Re.ref a).a = (Top.combLine sing (Cmp.fundOnRoot a)).a) →
    (∀ a t, IsConjInvariantH (Re.line a t)) →
    ∃ x : ℝ → Ψ × Fin N → HermLine ι, (∀ t r, (x t r).a = (sing r).a) ∧ (∀ t r, IsSmoothHerm (x t r)) ∧
      (∀ t r, IsConjInvariantH (x t r)) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ r, ∀ z ∈ mcPts P,
        (x t r).h z = (Top.combLine (fun a => Re.line a t) (Cmp.rootOnFund r)).h z

def StEmb : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (σ : Type)
    (S : PB.AnSys e σ) (Re : PB.Realis S P) (β : MRing ι) (b : K → ℕ), Re.J = ⊤ → Re.deg = 1 → Re.br = ∅ →
    IsMultiHomog β b → β ∉ P → (∀ x, Re.π x ∈ ReciprocityTheory.AnForm.P.bdry S.s → Cmp.evC (Re.R.lift x x) β = 0) →
    Cmp.AlgOver Re

def StForm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω]
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (x : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S x),
    ∃ (β : MRing J) (b : K → ℕ), IsMultiHomog β b ∧ β ∉ mCoordIdeal x ∧
      ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ x z w → ¬ 𝔐.Interior z → Cmp.evC w β = 0

def StAlg : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (M : PB.FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : PB.FlagTie M 𝔐) (n d : ℕ)
    (BM : PB.BaseMetric M n) (FA : PB.FlagAn BM d), BM.IsHodge tie → Cmp.AlgOver (FA.Re.comap some)

def StHt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω']
    (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)]
    (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (A' : HodgeCpt Y S y') (h : A'.X ⟶ A.X)
    (i : Ω →+* Ω') (j : A.Li →+ A'.Li), PB.HodgeOver A' A h i j → A'.R = A.R →
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) →
    (∀ p ∈ S, ∀ s, ((A.M.htOm A.t.PP.L (p ^ A.R p)).map (A.Vgen s).dualRestrict).IsVBOn {q | InFibre A.ξ p q}
      (labelRk D s) ⊤) →
    ∀ p ∈ S, ∀ s, ((A'.M.htOm A'.t.PP.L (p ^ A'.R p)).map (A'.Vgen s).dualRestrict).IsVBOn {q | InFibre A'.ξ p q}
      (labelRk D s) ⊤

def StSing : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) [DecidableEq (CMType H)]
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (M : PB.FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : PB.FlagTie M 𝔐) (n : ℕ)
    (BM : PB.BaseMetric M n) (𝔐' : HodgeCpt Y S y) (Fl : 𝔐'.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ)
    (e : CMType H × Fin (D.p + D.q) → Φ) (sing : CMType H × Fin (D.p + D.q) → HermLine ι),
    BM.IsHodge tie → tie.IsTotal 𝔐' Fl xdeg e → (∀ r, (sing r).a = xdeg r) → (∀ r, Fl.IsHodgeLine r (e r) (sing r)) →
    ∀ a, ∀ w ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ ReciprocityTheory.AnForm.P.bdry BM.s →
      SameOrbit (PB.basePart M.blk w) (BM.Rb.lift x x) →
      Real.log ((Top.combLine sing (Cmp.fundOnRoot a)).h w) = Real.log ((BM.hom a).h w)

def StSnc : Prop :=
  ResK.ResKStatement → ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (P : Scheme.{0}) (ξ₀ : Spec (CommRingCat.of Ω) ⟶ P) (e : ℕ) (Ab : P.Opens),
    (∀ q : P, GlobalTheory.CompanionTheory.Ar.genPt ξ₀ ⤳ q) → CoordTie ℤ ξ₀ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    Flat.NormalCpt ξ₀ → SmoothGenericFibreM y → IsArithVar (mCoordIdeal y) (e + 1) → GlobalTheory.CompanionTheory.Ar.genPt ξ₀ ∈ Ab →
    ∃ (N : ℕ) (x : Fin (N + 1) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ P)
      (bd : Ideal (MRing (fun _ : Unit => Fin (N + 1)))),
      (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) ∧ CoordTie ℤ ξ x ∧ ξ ≫ f = ξ₀ ∧
      Cmp.IsSncModel (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) e bd ∧
      ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) z w →
        (w ∈ mcPts bd ↔ f (centre z) ∉ Ab)

def StBase : Prop :=
  ResK.ResKStatement → Out.WeilSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω₀ : Type) [Field Ω₀]
    (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → (∀ p ∈ S, p.Prime) →
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) →
    ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k))
      (x : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S x) (d : ℕ),
      Nonempty K ∧ GlobalTheory.CompanionTheory.Ar.genPt 𝔐.ξ₀ = GlobalTheory.CompanionTheory.Ar.genPt ξ₀ ∧ 𝔐.IsCover d ∧ IsArithVar (mCoordIdeal x) (D.dim + 1) ∧
      PB.HasSncBoundary 𝔐 D.dim ∧ (∀ p ∈ S, 𝔐.R p = 4) ∧ 𝔐.OmVB

def StTie : Prop :=
  Given → Out.WeilSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (S : Finset ℕ) (Ω₀ : Type)
    [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → (∀ p ∈ S, p.Prime) →
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → 1 ≤ D.p → 1 ≤ D.q →
    ∃ (M' : RootModel (CMType H) (D.p + D.q)) (t : Cmp.HodgeTie Y S (Module.finrank ℚ c.F) M') (d : ℕ)
      (Sy : PB.AnSys (d + 1) (CMType H × Fin (D.p + D.q))) (K : Type) (_ : Fintype K) (ι : K → Type)
      (_ : ∀ k, Fintype (ι k)) (P : Ideal (MRing ι)) (Re : PB.Realis Sy P),
      GlobalTheory.CompanionTheory.Ar.genPt t.A.ξ₀ = GlobalTheory.CompanionTheory.Ar.genPt ξ₀ ∧ (∀ p ∈ S, t.A.R p = 4) ∧ t.Re.deg = 1 ∧ 0 < t.Fl.deg ∧
      Sy.degPoly = t.Sy.degPoly ∧ Nonempty (PB.FlagSys Re D.p) ∧ ∀ II : IntersectionSystem, Re.PB II = t.Re.PB II

def StSq : Prop :=
  Cmp.CmpSt → Given → Out.WeilSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)]
    (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem),
    o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → SquaresS (realOf o.toTowerOrigin) II

end SquareStatements

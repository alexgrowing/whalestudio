import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2.Geo

structure NgPkg where
  NgC : ℕ → Type
  NgC_ne : ∀ g, Nonempty (NgC g)
  KF : ℕ → ℕ → Type
  kfNorm : ∀ {g c : ℕ}, KF g c → NgC g → ℝ

variable (D : D7)

structure PadPkg (N j : ℕ) (Comp : Type) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ))
    (ng : NgPkg) where

  loc : ∀ p : ℕ, ModuliIntegralCharts.Loc D N j p
  ex : ∀ p, ModuliIntegralCharts.ExtA D (loc p)
  locB : ∀ p, p.Prime → BoundaryLocalData.LocB D (loc p)

  pbKF : ∀ (p : ℕ) {c : ℕ}, ng.KF (D.R.f * N) c → (loc p).Sec ((loc p).keySh c)

  levIn : ℕ → Prop
  Xg : Type
  bc : ∀ p : ℕ, Xg → (loc p).Mdl
  DivG : Xg → Type
  effD : ∀ {Z : Xg}, DivG Z → Prop
  noVertD : ∀ {Z : Xg}, DivG Z → Prop
  posBdD : ∀ {Z : Xg}, DivG Z → Prop
  ampleOnAbelianBase : ∀ Z : Xg, ℕ → DivG Z → Prop
  Met : Type
  nefFibM : Met → Prop
  ampleGen : Met → Prop
  limRA : Met → Prop

  Mp : ∀ p : ℕ, PlL D p → Type
  md : ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), Mp p la →
    DV.Mdl D p N (DV.rkOf (DV.PsiOf D (jC p la)) N j)

  CurveM : ∀ (p : ℕ) (la : PlL D p), Mp p la → Type
  degM : ∀ (p : ℕ) (la : PlL D p) (z : Mp p la), CurveM p la z → DV.Rt D.what₂.Tau N → ℝ

  htMdl : ∀ (p : ℕ) (la : PlL D p), Mp p la

  Pt : Type
  compPt : Pt → Comp

  phiDR : ℕ → Pt → DV.Rt D.what₂.Tau N → ℝ
  phiMod : ℕ → Pt → DV.Rt D.what₂.Tau N → ℝ
  phiFr : ℕ → Pt → DV.Rt D.what₂.Tau N → ℝ

  phiFr_unram : ∀ p y x, DV.UnramE D p → phiFr p y x = phiDR p y x

  normDetT : ℕ → D.what₂.Tau → Pt → ℝ
  normDetH : ℕ → D.what₂.Tau → Pt → ℝ

  htDetT : ℝ → Comp → D.what₂.Tau → ℝ

  arDeg : Finset ℕ → ℝ → MvPolynomial (DV.Rt D.what₂.Tau N) ℝ →ₗ[ℝ] ℝ
  arDeg_homog : ∀ S R (P : MvPolynomial (DV.Rt D.what₂.Tau N) ℝ) (d : ℕ),
    d ≠ Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1 → P.IsHomogeneous d → arDeg S R P = 0
  arMix : Finset ℕ → ℝ → ℕ → MvPolynomial (DV.Vm D.what₂.Tau N) ℝ →ₗ[ℝ] ℝ
  arMix_HT : ∀ S R p (P : MvPolynomial (DV.Rt D.what₂.Tau N) ℝ),
    arMix S R p (DV.tagHT D.what₂.Tau N P) = arDeg (insert p S) R P
  arMix_DR : ∀ S R p (P : MvPolynomial (DV.Rt D.what₂.Tau N) ℝ),
    arMix S R p (DV.tagDR D.what₂.Tau N P) = arDeg (S.erase p) R P

namespace PadPkg

variable {D} {N j : ℕ} {Comp : Type} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)}
  {ng : NgPkg} (X : PadPkg D N j Comp jC ng)

def FibComp (p : ℕ) : Type := (X.loc p).Gen (X.loc p).Xm

def fibInBd (p : ℕ) (η : X.FibComp p) : Prop := ¬ (X.loc p).abAt η

def CurveDR (p : ℕ) : Type := (X.loc p).Crv

def degDR (p : ℕ) (c : X.CurveDR p) (x : DV.Rt D.what₂.Tau N) : ℝ :=
  ((X.ex p).degGrD c (D.eTau x.1) ((x.2 : ℕ) + 1) : ℝ)

def CurveHT (p : ℕ) : Type := Σ la : PlL D p, X.CurveM p la (X.htMdl p la)

def degHT (p : ℕ) (c : X.CurveHT p) : DV.Rt D.what₂.Tau N → ℝ :=
  X.degM p c.1 (X.htMdl p c.1) c.2

end PadPkg

end Formalism.L2.Geo

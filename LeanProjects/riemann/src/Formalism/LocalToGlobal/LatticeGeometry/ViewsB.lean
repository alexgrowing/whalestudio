import Formalism.LocalToGlobal.LatticeGeometry.ShimuraSheafOfIndefiniteSubspace
import Formalism.SharpRestriction.Divisibility.IntegralModelsLocalData
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2.Geo

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)}
  {ng : NgPkg}

def indefiniteDataFamily (U : ∀ w : Dat D Lev, ShimU D G jC ng w) (I : Type) (dat : I → Dat D Lev)
    (hI : ∀ i, (dat i).Indef) : ModuliIntegralCharts.Prov D where
  Dat := I
  rk i := (dat i).N
  jj i := (dat i).j
  jj_range i := ⟨(hI i).1, (hI i).2⟩
  loc w p := (U (dat w)).pad.loc p
  ex w p := (U (dat w)).pad.ex p
  NgC := ng.NgC
  NgC_ne := ng.NgC_ne
  KF := ng.KF
  kfNorm := ng.kfNorm
  pbKF w p := (U (dat w)).pad.pbKF p
  levIn w M := (U (dat w)).pad.levIn M
  Xg w := (U (dat w)).pad.Xg
  bc := @fun w p Z => (U (dat w)).pad.bc p Z
  DivX := @fun w Z => (U (dat w)).pad.DivG Z
  effD := @fun w _ d => (U (dat w)).pad.effD d
  noVertD := @fun w _ d => (U (dat w)).pad.noVertD d
  posBdD := @fun w _ d => (U (dat w)).pad.posBdD d
  ampleOnAbelianBase := @fun w Z n d => (U (dat w)).pad.ampleOnAbelianBase Z n d
  Met w := (U (dat w)).pad.Met
  nefFib := @fun w M => (U (dat w)).pad.nefFibM M
  ampleGen := @fun w M => (U (dat w)).pad.ampleGen M
  limRA := @fun w M => (U (dat w)).pad.limRA M

def boundaryLocalDataOverIndefiniteData (U : ∀ w : Dat D Lev, ShimU D G jC ng w) (I : Type) (dat : I → Dat D Lev) (hI : ∀ i, (dat i).Indef) :
    BoundaryLocalData.Prov D (indefiniteDataFamily U I dat hI) where
  loc w p hp := (U (dat w)).pad.locB p hp

section Comparison₂

variable {w : Dat D Lev} (U : ShimU D G jC ng w) (h : w.Indef) (lev : Finset ℕ) (hlev : ∀ p ∈ lev, p.Prime)

def fcCast {Y : DV.ShimX D.what₂.Tau} (e : Y = toShimX U h lev hlev) (p : ℕ) (η : U.pad.FibComp p) :
    Y.FibComp p :=
  cast (congrArg (fun Z : DV.ShimX D.what₂.Tau => Z.FibComp p) e).symm η

theorem fcCast_surj {Y : DV.ShimX D.what₂.Tau} (e : Y = toShimX U h lev hlev) (p : ℕ) :
    Function.Surjective (fcCast U h lev hlev e p) := by
  subst e; intro y; exact ⟨y, rfl⟩

theorem fcCast_bd {Y : DV.ShimX D.what₂.Tau} (e : Y = toShimX U h lev hlev) (p : ℕ) (η : U.pad.FibComp p) :
    Y.fibInBd p (fcCast U h lev hlev e p η) ↔ ¬ (U.pad.loc p).abAt η := by
  subst e; exact Iff.rfl

theorem curveDR_of {Y : DV.ShimX D.what₂.Tau} (e : Y = toShimX U h lev hlev) (p : ℕ) (c : Y.CurveDR p) :
    ∃ (CC : (U.pad.loc p).Crv) (m : ℕ), 0 < m ∧ ∀ τ (i : Fin Y.N),
      (m : ℝ) * Y.degDR p c (τ, i) = (U.pad.ex p).degGrD CC (D.eTau τ) (i + 1) := by
  subst e; exact ⟨c, 1, one_pos, fun τ i => by simp [toShimX, PadPkg.degDR]⟩

theorem curveHT_of {Y : DV.ShimX D.what₂.Tau} (e : Y = toShimX U h lev hlev) (hHT : CurveHTDom U) (p n : ℕ)
    (Z' : (U.pad.loc p).Mdl) (hp : p.Prime) (hn : 3 ≤ n)
    (hZ : (U.pad.loc p).IsHTBlowup Z' ((U.pad.loc p).Xn n)) (c : Y.CurveHT p) :
    ∃ (C : (U.pad.ex p).CrvS Z') (m : ℕ), 0 < m ∧ ∀ τ (i : Fin Y.N),
      (m : ℝ) * Y.degHT p c (τ, i) = (U.pad.ex p).degGr C (D.eTau τ) (i + 1) := by
  subst e; exact hHT p n Z' hp hn hZ c

end Comparison₂

def shimuraDatumOfSetting (X : DivX D) (S : letI := D.host.cmStar; HSpace D.host.E) (κ : X.Lev)
    (hS : DV.HidaSetting D X S κ) : {w : Dat D X.Lev // w.Indef} :=
  letI := D.host.cmStar
  have hN : (X.shv S κ).N = S.rank := X.shv_N S κ hS.1
  ⟨{ S := S, κ := κ, j := (X.shv S κ).j, two_le := hS.1, sigOK := hS.2.1
     j_le := by have := (X.shv S κ).j_lt; omega
     hsig := fun τ => by rw [hS.2.2.1 τ, hN] },
   ⟨(X.shv S κ).j_pos, by have := (X.shv S κ).j_lt; show (X.shv S κ).j < S.rank; omega⟩⟩

def tieOf (X : DivX D) (levPr : X.Lev → Finset ℕ) (hlev : ∀ κ, ∀ p ∈ levPr κ, p.Prime)
    (U : ∀ w : Dat D X.Lev, ShimU D X.geo jC ng w) (hT : CompatibleLevelPrimes X levPr hlev U)
    (hHT : ∀ w : Dat D X.Lev, w.Indef → CurveHTDom (U w))
    (I : Type) (dat : I → Dat D X.Lev) (hI : ∀ i, (dat i).Indef) (i : I) :
    IntegralModelsLocalData.Comparison₂ D (indefiniteDataFamily U I dat hI) i (X.shv (dat i).S (dat i).κ) where
  rk_eq := by show (dat i).N = (X.shv (dat i).S (dat i).κ).N; rw [hT.shv (dat i) (hI i)]; rfl
  jj_eq := by show (dat i).j = (X.shv (dat i).S (dat i).κ).j; rw [hT.shv (dat i) (hI i)]; rfl
  fcOf p _ η := fcCast (U (dat i)) (hI i) _ _ (hT.shv (dat i) (hI i)) p η
  fcOf_surj p _ := fcCast_surj (U (dat i)) (hI i) _ _ (hT.shv (dat i) (hI i)) p
  fibInBd_iff p _ η := fcCast_bd (U (dat i)) (hI i) _ _ (hT.shv (dat i) (hI i)) p η
  curveHT p n Z' hp hn hZ c :=
    curveHT_of (U (dat i)) (hI i) _ _ (hT.shv (dat i) (hI i)) (hHT (dat i) (hI i)) p n Z' hp hn hZ c
  curveDR p _ _ _ _ c := curveDR_of (U (dat i)) (hI i) _ _ (hT.shv (dat i) (hI i)) p c

theorem tie_of_eq (X : DivX D) (levPr : X.Lev → Finset ℕ) (hlev : ∀ κ, ∀ p ∈ levPr κ, p.Prime)
    (U : ∀ w : Dat D X.Lev, ShimU D X.geo jC ng w) (hT : CompatibleLevelPrimes X levPr hlev U)
    (hHT : ∀ w : Dat D X.Lev, w.Indef → CurveHTDom (U w))
    (I : Type) (dat : I → Dat D X.Lev) (hI : ∀ i, (dat i).Indef) (i : I) {S κ} (hS : (dat i).S = S)
    (hκ : (dat i).κ = κ) : Nonempty (IntegralModelsLocalData.Comparison₂ D (indefiniteDataFamily U I dat hI) i (X.shv S κ)) := by
  subst hS; subst hκ
  exact ⟨tieOf X levPr hlev U hT hHT I dat hI i⟩

def settingVarietiesOverData (X : DivX D) (I : Type) (dat : I → Dat D X.Lev) (hI : ∀ i, (dat i).Indef)
    (U : ∀ w : Dat D X.Lev, ShimU D X.geo jC ng w)
    (hsurj : letI := D.host.cmStar; ∀ S κ, DV.HidaSetting D X S κ →
      ∃ i, Nonempty (IntegralModelsLocalData.Comparison₂ D (indefiniteDataFamily U I dat hI) i (X.shv S κ))) :
    IntegralModelsLocalData.Prov D X where
  P := indefiniteDataFamily U I dat hI
  dat_surj := hsurj

end Formalism.L2.Geo

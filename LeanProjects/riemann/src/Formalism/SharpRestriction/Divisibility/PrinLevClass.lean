import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace Formalism.MainNotions.DIV.Align

open Formalism.BasicNotions Formalism.MainNotions

def tauMul (D : D7) (g : D.R.Psi) : Equiv.Perm D.what₂.Tau :=
  D.eTau.trans ((Equiv.mulRight g).trans D.eTau.symm)

def rtMul (D : D7) (N : ℕ) (g : D.R.Psi) : DV.Rt D.what₂.Tau N → DV.Rt D.what₂.Tau N :=
  fun x => (tauMul D g x.1, x.2)

structure PrinLev {D : D7} (V : DivX D) where

  κg : V.Lev

  κs : V.Lev
  κg_pr : V.levPr κg = {D.host.g 0, D.host.g 1}
  κs_pr : V.levPr κs = {D.host.g 0, D.host.g 1, 3, 5}

def LevB {D : D7} {V : DivX D} (P : PrinLev V) (κ : V.Lev) : Prop := κ = P.κg ∨ κ = P.κs

abbrev PrinLevF {eps : ℝ} (Fm : FamP eps) : Type :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), PrinLev (Fm.X x i)

abbrev PrinLevClass : Type 1 := ∀ {eps : ℝ} (Fm : FamP eps), PrinLevF Fm → Prop

def FanAt (D : D7) (V : DivX D) (P : PrinLev V) : Prop :=
  letI := D.host.cmStar
  ∀ (S : HSpace D.host.E) (κ : V.Lev), DV.HidaSetting D V S κ → LevB P κ → ∀ g : D.R.Psi,
    ∃ (a : Equiv.Perm (V.shv S κ).XC) (b : Equiv.Perm (V.shv S κ).Comp),
      ∀ z,
        (V.shv S κ).compOf (a z) = b ((V.shv S κ).compOf z) ∧
        (V.shv S κ).rfn (a z) = (V.shv S κ).rfn z ∧
        (V.shv S κ).hLo (a z) = (V.shv S κ).hLo z ∧
        (V.shv S κ).hUp (a z) = (V.shv S κ).hUp z ∧
        (V.shv S κ).connN (a z) = (V.shv S κ).connN z ∧
        (V.shv S κ).curvN (a z) = (V.shv S κ).curvN z

def FanArAt (D : D7) (V : DivX D) (P : PrinLev V) : Prop :=
  letI := D.host.cmStar
  ∀ (S : HSpace D.host.E) (κ : V.Lev), DV.HidaSetting D V S κ → LevB P κ → ∀ g : D.R.Psi,
    ∀ T : Finset ℕ, Nat.primeFactors (2 * (NumberField.discr D.host.E).natAbs) ∪ (V.shv S κ).lev ⊆ T →
      ∀ (R : ℝ) (Q : MvPolynomial (DV.Rt D.what₂.Tau (V.shv S κ).N) ℝ),
        (V.shv S κ).arDeg T R (MvPolynomial.rename (rtMul D (V.shv S κ).N g) Q) = (V.shv S κ).arDeg T R Q

def FanGal {eps : ℝ} (Fm : FamP eps) (PL : PrinLevF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FanAt (Fm.D x i) (Fm.X x i) (PL x hx i)

def FanArGal {eps : ℝ} (Fm : FamP eps) (PL : PrinLevF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FanArAt (Fm.D x i) (Fm.X x i) (PL x hx i)

theorem fanAt_id (D : D7) (V : DivX D) (P : PrinLev V) : FanAt D V P :=
  fun _ _ _ _ _ => ⟨1, 1, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem fanGal_id {eps : ℝ} (Fm : FamP eps) (PL : PrinLevF Fm) : FanGal Fm PL := fun _ _ _ => fanAt_id _ _ _

def TameAtG {eps : ℝ} (Fm : FamP eps)
    (tc : ∀ x (i : Fm.Ix x), ℕ → ∀ k : Fin 2, (ZMod ((Fm.D x i).host.g k))ˣ →* ℂˣ) : Prop :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x),
    (∀ k : Fin 2, ∃ om : (ZMod ((Fm.D x i).host.g k))ˣ →* ℂˣ,
      orderOf om = (Fm.D x i).host.g k - 1 ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ (Fm.D x i).R.m → tc x i j k = om ^ (2 * j)) ∧
    ∀ j : Fin (Fm.D x i).R.m, ∃ n : ℤ, (∑ τ, (((Fm.D x i).hc τ).e j : ℚ)) = 2 * n

def FunData {eps : ℝ} (Fm : FamP eps) (cF : List ℝ → ℝ)
    (cond : ∀ x (_ : Fm.Ix x), ℕ → ℕ → ℕ) (q0 : ∀ x (_ : Fm.Ix x), ℕ)
    (nb : ∀ x (_ : Fm.Ix x), Fin 2 → ℕ) : Prop :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x),
    (∀ k, 1 ≤ k → k ≤ (Fm.D x i).R.m → ∀ p : ℕ, p.Prime →
      cond x i k p =
        if p = (Fm.D x i).host.g 0 ∨ p = (Fm.D x i).host.g 1 ∨ p = (Fm.D x i).host.pde ∨
            p = (Fm.D x i).host.pde' then 2
        else if p = q0 x i then 1 else 0) ∧
    Real.log (q0 x i : ℝ) ≤ cF Fm.cOut * (Fm.L x i).sc.L ∧
    ∀ k, Real.log (nb x i k : ℝ) ≤ cF Fm.cOut * ((Fm.D x i).R.f : ℝ) ^ 2 * (Fm.L x i).sc.L

end Formalism.MainNotions.DIV.Align

end

import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataDIV
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.Divisibility.PrinLevClass

noncomputable section

open NumberField MvPolynomial Finset
open scoped BigOperators

namespace Formalism.MainNotions.LatticeTransfer

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

def wt (Tau : Type) [Fintype Tau] (N : ℕ) : Vm Tau N → ℕ
  | Sum.inl _ => 1
  | Sum.inr (_, k) => k

def evV {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} {rk : Emb D p → ℕ} (M : Mdl D p N rk)
    (rt : Bool × Rt D.what₂.Tau N → M.Z.LB) :
    MvPolynomial (Vm D.what₂.Tau N) ℚ →ₐ[ℚ] MvPolynomial M.Z.LB ℚ :=
  aeval (fun v => match v with
    | Sum.inl r => X (rt r)
    | Sum.inr (false, k) => C ((Nat.factorial k : ℚ)⁻¹) *
        ((∑ l, X (M.lieW.x l) ^ k) + ∑ l, X (M.omW.x l) ^ k)
    | Sum.inr (true, k) => C ((Nat.factorial k : ℚ)⁻¹) *
        ((∑ l, X (M.lieW.x' l) ^ k) + ∑ l, X (M.omW.x' l) ^ k))

def evC {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} {rk : Emb D p → ℕ} (M : Mdl D p N rk)
    (rt : Bool × Rt D.what₂.Tau N → M.Z.LB) (G : MvPolynomial (Vm D.what₂.Tau N) ℚ) : M.Z.Ch :=
  evQ M.Z (evV M rt G)

def toR {σ : Type} (G : MvPolynomial σ ℚ) : MvPolynomial σ ℝ := map (algebraMap ℚ ℝ) G

def dRt (Tau : Type) [Fintype Tau] (N : ℕ) (r : Rt Tau N) : MvPolynomial (Vm Tau N) ℝ :=
  X (Sum.inl (false, r)) - X (Sum.inl (true, r))

def dCh (Tau : Type) [Fintype Tau] (N : ℕ) (k : ℕ) : MvPolynomial (Vm Tau N) ℝ :=
  X (Sum.inr (false, k)) - X (Sum.inr (true, k))

structure Loc (D : D7) (XD : DivX D) where

  rt : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev) (p : ℕ) [Fact p.Prime]
    (la : XD.PlP p) (z : XD.Mp S κ p la), Bool × Rt D.what₂.Tau (XD.shv S κ).N → (XD.md S κ p la z).Z.LB

  rt_lie : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
    ∀ (i : Fin (rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ)) (i' : Fin (XD.shv S κ).N),
      (i' : ℕ) = i →
      rt S κ p la z (false, (τ0, i')) = ((XD.md S κ p la z).lie τ).x i ∧
      rt S κ p la z (true, (τ0, i')) = ((XD.md S κ p la z).lie τ).x' i

  rt_om : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
    ∀ (i : Fin ((XD.shv S κ).N - rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ))
      (i' : Fin (XD.shv S κ).N), (i' : ℕ) = (XD.shv S κ).j + i →
      rt S κ p la z (false, (τ0, i')) = ((XD.md S κ p la z).om τ).x i ∧
      rt S κ p la z (true, (τ0, i')) = ((XD.md S κ p la z).om τ).x' i

  lieW_gen : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la), ∃ (e : Fin (D.R.f * (XD.shv S κ).N) ≃ Rt D.what₂.Tau (XD.shv S κ).N)
      (V : Fin (D.R.f * (XD.shv S κ).N) → (XD.md S κ p la z).Z.VDiv), ∀ l,
      (XD.md S κ p la z).Z.c1 ((XD.md S κ p la z).lieW.x l) =
        (if ((e l).2 : ℕ) < (XD.shv S κ).j then (1 : ℚ) else -1) •
            (XD.md S κ p la z).Z.c1 (rt S κ p la z (false, e l)) +
          (XD.md S κ p la z).Z.cD (V l)

section One
variable (D : D7) (XD : DivX D) (T : Loc D XD)
  (S : letI := D.host.cmStar; HSpace D.host.E) (κ : XD.Lev)

def adm1 : Prop :=
  ∀ p : ℕ, p.Prime → ∀ c : (XD.shv S κ).FibComp p, ¬ (XD.shv S κ).fibInBd p c

def adm2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p), ∃ n0 : ℕ, (p ∉ (XD.shv S κ).lev → n0 = 0) ∧
    ∀ n : ℕ, n0 ≤ n → (1 + 1 / ((p : ℝ) - 1)) < n → ∃ z : XD.Mp S κ p la, (XD.md S κ p la z).lvl = n

def adm3 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (E E' : (XD.md S κ p la z).Z.VDiv)
    (a : (XD.md S κ p la z).Z.Ch),
    (XD.md S κ p la z).Z.capDeg E ((XD.md S κ p la z).Z.cD E' * a) =
      (XD.md S κ p la z).Z.capDeg E' ((XD.md S κ p la z).Z.cD E * a)

def ArchimedeanSignatureMatching : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la),
  (∀ (r : ℕ) (P P' P'' : FPair (XD.md S κ p la z).Z r), P'.x = P.x' → P''.x = P.x → P''.x' = P'.x' →
      (∀ i, P''.Dv i = P.Dv i + P'.Dv i) →
      ∀ (k : ℕ) (Q : (XD.md S κ p la z).Z.Ch), ck P'' k Q = ck P k Q + ck P' k Q) ∧
  (∀ (r : ℕ) (P : FPair (XD.md S κ p la z).Z r) (v : ℚ),
      (∀ i, P.Dv i = v • (XD.md S κ p la z).Z.divP) →
      ∀ (k : ℕ) (Q : (XD.md S κ p la z).Z.Ch), 1 ≤ k →
      ck P k Q = (k : ℚ) * v * (XD.md S κ p la z).Z.capDeg (XD.md S κ p la z).Z.divP
        ((∑ i, (XD.md S κ p la z).Z.c1 (P.x i) ^ (k - 1)) * Q)) ∧
  (∀ (r : ℕ) (P P' : FPair (XD.md S κ p la z).Z r),
      (∀ i, (XD.md S κ p la z).Z.c1 (P'.x i) = (p : ℚ) • (XD.md S κ p la z).Z.c1 (P.x i)) →
      (∀ i, (XD.md S κ p la z).Z.c1 (P'.x' i) = (p : ℚ) • (XD.md S κ p la z).Z.c1 (P.x' i)) →
      (∀ i, P'.Dv i = (p : ℚ) • P.Dv i) →
      ∀ (k : ℕ) (Q : (XD.md S κ p la z).Z.Ch), ck P' k Q = (p : ℚ) ^ k * ck P k Q)

def adm5 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la)
    (G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ),
    G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) (dimFl D.what₂.Tau (XD.shv S κ).N) →
    (((XD.md S κ p la z).Z.capDeg (XD.md S κ p la z).Z.divP
        (evC (XD.md S κ p la z) (T.rt S κ p la z) G) : ℚ) : ℝ) / ((XD.md S κ p la z).cov : ℝ) =
      (XD.shv S κ).chern (collapse D _ (toR G))

def adm6 : Prop :=
  (∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ) [Fact p.Prime] (z : ∀ la : XD.PlP p, XD.Mp S κ p la)
    (τ0 : D.what₂.Tau) (τ' : XD.PlP p → Emb D p),
    (∀ la, (XD.jC p la).comp (τ' la) = tauEmb D τ0) →
    ∀ (i : ∀ la, Fin (rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j (τ' la)))
      (i' : Fin (XD.shv S κ).N), (∀ la, (i' : ℕ) = i la) →
      ∀ G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ,
      G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) (dimFl D.what₂.Tau (XD.shv S κ).N) →
      (XD.shv S κ).arMix Sx R p (dRt D.what₂.Tau (XD.shv S κ).N (τ0, i') * toR G) =
        Real.log p * ∑ la, XD.wtP p la *
          ((((XD.md S κ p la (z la)).Z.capDeg (((XD.md S κ p la (z la)).lie (τ' la)).Dv (i la))
            (evC (XD.md S κ p la (z la)) (T.rt S κ p la (z la)) G) : ℚ) : ℝ) /
              ((XD.md S κ p la (z la)).cov : ℝ))) ∧
  (∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ) [Fact p.Prime] (z : ∀ la : XD.PlP p, XD.Mp S κ p la)
    (τ0 : D.what₂.Tau) (τ' : XD.PlP p → Emb D p),
    (∀ la, (XD.jC p la).comp (τ' la) = tauEmb D τ0) →
    ∀ (i : ∀ la, Fin ((XD.shv S κ).N -
        rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j (τ' la)))
      (i' : Fin (XD.shv S κ).N), (∀ la, (i' : ℕ) = (XD.shv S κ).j + i la) →
      ∀ G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ,
      G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) (dimFl D.what₂.Tau (XD.shv S κ).N) →
      (XD.shv S κ).arMix Sx R p (dRt D.what₂.Tau (XD.shv S κ).N (τ0, i') * toR G) =
        Real.log p * ∑ la, XD.wtP p la *
          ((((XD.md S κ p la (z la)).Z.capDeg (((XD.md S κ p la (z la)).om (τ' la)).Dv (i la))
            (evC (XD.md S κ p la (z la)) (T.rt S κ p la (z la)) G) : ℚ) : ℝ) /
              ((XD.md S κ p la (z la)).cov : ℝ))) ∧
  (∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ) [Fact p.Prime] (z : ∀ la : XD.PlP p, XD.Mp S κ p la)
    (k m : ℕ), 1 ≤ k → m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
    ∀ G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ,
      G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) m →
      (XD.shv S κ).arMix Sx R p (dCh D.what₂.Tau (XD.shv S κ).N k * toR G) =
        Real.log p * ∑ la, XD.wtP p la *
          ((chk (XD.md S κ p la (z la)).lieW k
              (evC (XD.md S κ p la (z la)) (T.rt S κ p la (z la)) G) +
            chk (XD.md S κ p la (z la)).omW k
              (evC (XD.md S κ p la (z la)) (T.rt S κ p la (z la)) G)) /
            ((XD.md S κ p la (z la)).cov : ℝ)))

def admitted : Prop :=
  adm1 D XD S κ ∧ adm2 D XD S κ ∧ adm3 D XD S κ ∧ ArchimedeanSignatureMatching D XD S κ ∧ adm5 D XD T S κ ∧
    adm6 D XD T S κ

def Conclusion1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → UnramE D p → p ∉ (XD.shv S κ).lev →
  ∀ (la : XD.PlP p) (z : XD.Mp S κ p la) (τ : Emb D p) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
  ∀ Q : MvPolynomial (XD.md S κ p la z).Z.LB ℚ, Q.IsHomogeneous m →
    (chk ((XD.md S κ p la z).lie τ) k (evQ _ Q) + chk ((XD.md S κ p la z).om τ) k (evQ _ Q)) /
        ((XD.md S κ p la z).cov : ℝ) =
      ((∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
            chDiv ((XD.md S κ p la z).lie (phiPow D (n + 1) τ)).x (k - 1) (evQ _ Q)) -
          chDiv ((XD.md S κ p la z).lie τ).x (k - 1) (evQ _ Q) / ((p : ℝ) - 1)) /
        ((XD.md S κ p la z).cov : ℝ)

def Conclusion2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
  ∀ Q : MvPolynomial (XD.md S κ p la z).Z.LB ℚ, Q.IsHomogeneous m →
    (chk (XD.md S κ p la z).lieW k (evQ _ Q) + chk (XD.md S κ p la z).omW k (evQ _ Q)) /
        ((XD.md S κ p la z).cov : ℝ) =
      ((∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
            chDiv (XD.md S κ p la z).lieW.x (k - 1) (evQ _ Q)) -
          chDiv (XD.md S κ p la z).lieW.x (k - 1) (evQ _ Q) / ((p : ℝ) - 1)) /
        ((XD.md S κ p la z).cov : ℝ)

def stp1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → UnramE D p → p ∉ (XD.shv S κ).lev →
  ∀ (la : XD.PlP p) (z : XD.Mp S κ p la) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
  ∀ Q : MvPolynomial (XD.md S κ p la z).Z.LB ℚ, Q.IsHomogeneous m →
  ∃ q : ℕ → Emb D p → ℝ,
    (∀ τ, chk ((XD.md S κ p la z).lie τ) k (evQ _ Q) + chk ((XD.md S κ p la z).om τ) k (evQ _ Q) =
      q 0 τ - chDiv ((XD.md S κ p la z).lie τ).x (k - 1) (evQ _ Q) / ((p : ℝ) - 1)) ∧
    (∀ r τ, q r τ = ((p : ℝ) ^ ((r + 1) * k))⁻¹ *
      chDiv ((XD.md S κ p la z).lie (phiPow D (r + 1) τ)).x (k - 1) (evQ _ Q) + q (r + 1) τ) ∧
    (∀ r τ, q (r + 1) τ = ((p : ℝ) ^ k)⁻¹ * q r (phiPow D 1 τ))

def stp2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
  ∀ Q : MvPolynomial (XD.md S κ p la z).Z.LB ℚ, Q.IsHomogeneous m →
  ∃ q : ℕ → ℝ,
    (chk (XD.md S κ p la z).lieW k (evQ _ Q) + chk (XD.md S κ p la z).omW k (evQ _ Q) =
      q 0 - chDiv (XD.md S κ p la z).lieW.x (k - 1) (evQ _ Q) / ((p : ℝ) - 1)) ∧
    (∀ r, q r = ((p : ℝ) ^ ((r + 1) * k))⁻¹ *
      chDiv (XD.md S κ p la z).lieW.x (k - 1) (evQ _ Q) + q (r + 1)) ∧
    (∀ r, q (r + 1) = ((p : ℝ) ^ k)⁻¹ * q r)

end One

def PointsLemma (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) : Prop :=
  ∀ S κ, HidaSetting D XD S κ → DIV.Align.LevB P κ → ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ),
  p.Prime → p ≠ 2 → UnramE D p → p ∉ (XD.shv S κ).lev → ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
  ∀ Q : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℝ,
    Q.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) m →
    (XD.shv S κ).arMix Sx R p
        ((tagDR D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k) -
          tagHT D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k)) * Q) =
      Real.log p * ((∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          (XD.shv S κ).chern (chLie (XD.shv S κ).j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) *
            collapse D _ Q)) -
        (XD.shv S κ).chern (chLie (XD.shv S κ).j (k - 1) (Sum.inl τ) * collapse D _ Q) /
          ((p : ℝ) - 1))

def Conclusion4 (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) : Prop :=
  ∀ S κ, HidaSetting D XD S κ → DIV.Align.LevB P κ → ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ),
  p.Prime → ∀ (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
  ∀ Q : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℝ,
    Q.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) m →
    (XD.shv S κ).arMix Sx R p ((X (Sum.inr (false, k)) - X (Sum.inr (true, k))) * Q) =
      Real.log p * ((∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          (XD.shv S κ).chern (chLieA D _ (XD.shv S κ).j (k - 1) * collapse D _ Q)) -
        (XD.shv S κ).chern (chLieA D _ (XD.shv S κ).j (k - 1) * collapse D _ Q) / ((p : ℝ) - 1))

def AdmX (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) (T : Loc D XD) : Prop :=
  ∀ S κ, HidaSetting D XD S κ → DIV.Align.LevB P κ → admitted D XD T S κ

def ConclusionL (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) : Prop :=
  ∀ S κ, HidaSetting D XD S κ → DIV.Align.LevB P κ → Conclusion1 D XD S κ ∧ Conclusion2 D XD S κ

def stpX (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) : Prop :=
  ∀ S κ, HidaSetting D XD S κ → DIV.Align.LevB P κ → stp1 D XD S κ ∧ stp2 D XD S κ

def Stmt (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) (T : Loc D XD) : Prop :=
  AdmX D XD P T → ConclusionL D XD P ∧ PointsLemma D XD P ∧ Conclusion4 D XD P

def TateModuleDieudonneOfAdmissible (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) (T : Loc D XD) : Prop := AdmX D XD P T → stpX D XD P

def LastRelationsAlgebra (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) : Prop := stpX D XD P → ConclusionL D XD P

def LocalToGlobalPassage (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) (T : Loc D XD) : Prop :=
  AdmX D XD P T → ConclusionL D XD P → PointsLemma D XD P ∧ Conclusion4 D XD P

abbrev LocF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.X x i)

def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm) (TF : LocF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AdmX (Fm.D x i) (Fm.X x i) (PL x hx i) (TF x hx i)

def LocalPropertiesFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConclusionL (Fm.D x i) (Fm.X x i) (PL x hx i)

def Conclusion3Family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), PointsLemma (Fm.D x i) (Fm.X x i) (PL x hx i)

def SlopeLemmaFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion4 (Fm.D x i) (Fm.X x i) (PL x hx i)

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm) (TF : LocF Fm) : Prop :=
  AdmF Fm PL TF → LocalPropertiesFamily Fm PL ∧ Conclusion3Family Fm PL ∧ SlopeLemmaFamily Fm PL

section One1
variable (D : D7) (XD : DivX D) (T : Loc D XD)
  (S : letI := D.host.cmStar; HSpace D.host.E) (κ : XD.Lev)

def vLie (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ : Emb D p)
    (i : Fin (rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ))
    (G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ) : ℝ :=
  (((XD.md S κ p la z).Z.capDeg (((XD.md S κ p la z).lie τ).Dv i)
      (evC (XD.md S κ p la z) (T.rt S κ p la z) G) : ℚ) : ℝ) / ((XD.md S κ p la z).cov : ℝ)

def vOm (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ : Emb D p)
    (i : Fin ((XD.shv S κ).N - rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ))
    (G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ) : ℝ :=
  (((XD.md S κ p la z).Z.capDeg (((XD.md S κ p la z).om τ).Dv i)
      (evC (XD.md S κ p la z) (T.rt S κ p la z) G) : ℚ) : ℝ) / ((XD.md S κ p la z).cov : ℝ)

def vCh (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (k : ℕ)
    (G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ) : ℝ :=
  (chk (XD.md S κ p la z).lieW k (evC (XD.md S κ p la z) (T.rt S κ p la z) G) +
      chk (XD.md S κ p la z).omW k (evC (XD.md S κ p la z) (T.rt S κ p la z) G)) /
    ((XD.md S κ p la z).cov : ℝ)

def ModInd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z z' : XD.Mp S κ p la),
    (∀ (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
        ∀ (i : Fin (rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ))
        (G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ),
        G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) (dimFl D.what₂.Tau (XD.shv S κ).N) →
        vLie D XD T S κ p la z τ i G = vLie D XD T S κ p la z' τ i G) ∧
    (∀ (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
        ∀ (i : Fin ((XD.shv S κ).N - rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ))
        (G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ),
        G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) (dimFl D.what₂.Tau (XD.shv S κ).N) →
        vOm D XD T S κ p la z τ i G = vOm D XD T S κ p la z' τ i G) ∧
    (∀ (k m : ℕ), 1 ≤ k → m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
        ∀ G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ,
        G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) m →
        vCh D XD T S κ p la z k G = vCh D XD T S κ p la z' k G)

def ThreeIdentitiesOnModel : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ z : ∀ la : XD.PlP p, XD.Mp S κ p la,
  (∀ (Sx : Finset ℕ) (R : ℝ) (τ0 : D.what₂.Tau) (τ' : XD.PlP p → Emb D p),
    (∀ la, (XD.jC p la).comp (τ' la) = tauEmb D τ0) →
    ∀ (i : ∀ la, Fin (rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j (τ' la)))
      (i' : Fin (XD.shv S κ).N), (∀ la, (i' : ℕ) = i la) →
      ∀ G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ,
      G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) (dimFl D.what₂.Tau (XD.shv S κ).N) →
      (XD.shv S κ).arMix Sx R p (dRt D.what₂.Tau (XD.shv S κ).N (τ0, i') * toR G) =
        Real.log p * ∑ la, XD.wtP p la * vLie D XD T S κ p la (z la) (τ' la) (i la) G) ∧
  (∀ (Sx : Finset ℕ) (R : ℝ) (τ0 : D.what₂.Tau) (τ' : XD.PlP p → Emb D p),
    (∀ la, (XD.jC p la).comp (τ' la) = tauEmb D τ0) →
    ∀ (i : ∀ la, Fin ((XD.shv S κ).N -
        rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j (τ' la)))
      (i' : Fin (XD.shv S κ).N), (∀ la, (i' : ℕ) = (XD.shv S κ).j + i la) →
      ∀ G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ,
      G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) (dimFl D.what₂.Tau (XD.shv S κ).N) →
      (XD.shv S κ).arMix Sx R p (dRt D.what₂.Tau (XD.shv S κ).N (τ0, i') * toR G) =
        Real.log p * ∑ la, XD.wtP p la * vOm D XD T S κ p la (z la) (τ' la) (i la) G) ∧
  (∀ (Sx : Finset ℕ) (R : ℝ) (k m : ℕ), 1 ≤ k → m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
    ∀ G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ,
      G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) m →
      (XD.shv S κ).arMix Sx R p (dCh D.what₂.Tau (XD.shv S κ).N k * toR G) =
        Real.log p * ∑ la, XD.wtP p la * vCh D XD T S κ p la (z la) k G)

theorem three_identities_of_model_independence (h : ThreeIdentitiesOnModel D XD T S κ) (ht : ModInd D XD T S κ) : adm6 D XD T S κ := by
  refine ⟨?_, ?_, ?_⟩
  · intro Sx R p _ z τ0 τ' hτ i i' hi G hG
    obtain ⟨z0, h1, -, -⟩ := h p
    rw [h1 Sx R τ0 τ' hτ i i' hi G hG]
    congr 1
    refine Finset.sum_congr rfl (fun la _ => ?_)
    rw [(ht p la (z0 la) (z la)).1 τ0 (τ' la) (hτ la) (i la) G hG]
    rfl
  · intro Sx R p _ z τ0 τ' hτ i i' hi G hG
    obtain ⟨z0, -, h2, -⟩ := h p
    rw [h2 Sx R τ0 τ' hτ i i' hi G hG]
    congr 1
    refine Finset.sum_congr rfl (fun la _ => ?_)
    rw [(ht p la (z0 la) (z la)).2.1 τ0 (τ' la) (hτ la) (i la) G hG]
    rfl
  · intro Sx R p _ z k m hk hm G hG
    obtain ⟨z0, -, -, h3⟩ := h p
    rw [h3 Sx R k m hk hm G hG]
    congr 1
    refine Finset.sum_congr rfl (fun la _ => ?_)
    rw [(ht p la (z0 la) (z la)).2.2 k m hk hm G hG]
    rfl

theorem three_identities_on_model_of (h : adm6 D XD T S κ) : ThreeIdentitiesOnModel D XD T S κ := by
  intro p _
  refine ⟨fun la => XD.htMdl S κ p la, ?_, ?_, ?_⟩
  · intro Sx R τ0 τ' hτ i i' hi G hG
    exact h.1 Sx R p _ τ0 τ' hτ i i' hi G hG
  · intro Sx R τ0 τ' hτ i i' hi G hG
    exact h.2.1 Sx R p _ τ0 τ' hτ i i' hi G hG
  · intro Sx R k m hk hm G hG
    exact h.2.2 Sx R p _ k m hk hm G hG

end One1

def LocalToGlobalOnModel (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) (T : Loc D XD) : Prop :=
  (∀ S κ, HidaSetting D XD S κ → DIV.Align.LevB P κ → adm3 D XD S κ ∧ adm5 D XD T S κ ∧ ThreeIdentitiesOnModel D XD T S κ) →
    ConclusionL D XD P → PointsLemma D XD P ∧ Conclusion4 D XD P

def ThreeIdentitiesOnModelFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm) (TF : LocF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) S κ, HidaSetting (Fm.D x i) (Fm.X x i) S κ → DIV.Align.LevB (PL x hx i) κ →
    ThreeIdentitiesOnModel (Fm.D x i) (Fm.X x i) (TF x hx i) S κ

def ModIndF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm) (TF : LocF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) S κ, HidaSetting (Fm.D x i) (Fm.X x i) S κ → DIV.Align.LevB (PL x hx i) κ →
    ModInd (Fm.D x i) (Fm.X x i) (TF x hx i) S κ

theorem three_identities_family_of_model {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm) (TF : LocF Fm)
    (h : ThreeIdentitiesOnModelFamily Fm PL TF) (ht : ModIndF Fm PL TF) :
    ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) S κ, HidaSetting (Fm.D x i) (Fm.X x i) S κ → DIV.Align.LevB (PL x hx i) κ →
      adm6 (Fm.D x i) (Fm.X x i) (TF x hx i) S κ :=
  fun x hx i S κ hs hB => three_identities_of_model_independence _ _ _ _ _ (h x hx i S κ hs hB) (ht x hx i S κ hs hB)

theorem one_model_family_of_identities {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm) (TF : LocF Fm)
    (h : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) S κ, HidaSetting (Fm.D x i) (Fm.X x i) S κ → DIV.Align.LevB (PL x hx i) κ →
      adm6 (Fm.D x i) (Fm.X x i) (TF x hx i) S κ) : ThreeIdentitiesOnModelFamily Fm PL TF :=
  fun x hx i S κ hs hB => three_identities_on_model_of _ _ _ _ _ (h x hx i S κ hs hB)

def LocalToGlobalOnModelFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm) (TF : LocF Fm) : Prop :=
  (∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) S κ, HidaSetting (Fm.D x i) (Fm.X x i) S κ → DIV.Align.LevB (PL x hx i) κ →
      adm3 (Fm.D x i) (Fm.X x i) S κ ∧ adm5 (Fm.D x i) (Fm.X x i) (TF x hx i) S κ ∧
        ThreeIdentitiesOnModel (Fm.D x i) (Fm.X x i) (TF x hx i) S κ) →
    LocalPropertiesFamily Fm PL → Conclusion3Family Fm PL ∧ SlopeLemmaFamily Fm PL

end Formalism.MainNotions.LatticeTransfer

end

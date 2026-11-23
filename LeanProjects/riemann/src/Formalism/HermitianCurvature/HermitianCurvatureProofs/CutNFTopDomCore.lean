import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomPtw
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJD

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory

noncomputable section

section kb

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def trJKB (p : KB.Pl P Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) :
    M.Ty P → MA.SmQ P.r P.TT :=
  fun ρ => MA.toSm P fun q =>
    ((Real.sqrt (MA.wq P.k q.1 P.TT) : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq p.T.base q.1)))

def IsFrameKB (p : KB.Pl P Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e ρ) {ζ : ℂ | P.TT < Complex.normSq ζ}) ∧
  ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
    (∀ ρ, e ρ ζ ∈ NF.Fib P.k P.r p.T.base.z p.T.base.z' p.T.base.μsec p.T.base.π p.T.base.π' ζ) ∧
    (∀ ρ ρ', inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (e ρ' ζ)) = if ρ = ρ' then (1 : ℂ) else 0) ∧
    ∀ X ∈ NF.Fib P.k P.r p.T.base.z p.T.base.z' p.T.base.μsec p.T.base.π p.T.base.π' ζ,
      X = ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) • e ρ ζ

end kb

def NFModelNF : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ (l0 : ℕ) (Y : Finset ℝ) (w : List C.Letter), TBB.AdmW P l0 Y w → ∀ e : Wd.Ix (Fin w.length),
      ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (i i' : Fin m → ℕ) (h : Fin m → List (MA.A P (MA.DQ P))),
        (∀ j, b j ∈ Submonoid.closure (MA.bddSet P L)) ∧ (∀ j, i j + i' j = w.length) ∧
        (∀ j, (h j).length = w.length ∧ ∀ a ∈ h j, a ∈ MA.hatSet P L) ∧
        (Fr.ofWord L (MA.startM P (MA.DQ P) l0) (D.positionted w)).F e (fun _ => 0) =
          ∑ j, b j * L.Di ^ i j * L.Dbi ^ i' j * (h j).prod

def NFTieHat : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ →
    ∃ (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (L : R.LevelData (MA.A P (MA.DQ P)) P.r),
      IsFrameKB p e ∧ MA.IsModelLevel P (MA.DQ P) L ∧
      ∀ (Y : Finset ℝ) (w : List C.Letter), TBB.AdmW P p.l0 Y w →
      ∀ (ee : Wd.Ix (Fin w.length)) (Q : ℕ) (Lq : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq), IsSCoef p w ee Q Lq →
      ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (u : Fin m → List (MA.A P (MA.DQ P))) (C : ℝ),
        (∀ j, b j ∈ Submonoid.closure (MA.bddSet P L)) ∧ (∀ j, (u j).length = w.length ∧ ∀ a ∈ u j, a ∈ MA.hatSet P L) ∧
        ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
          Cc * ((P.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
          ∀ (qq : Fin (Q + 1)) (ρ : M.Ty P) (c : Fin (P.r + 1) → ℂ) (q : MA.Qp P.r P.TT),
            q.1 = ((fun l => c l.castSucc), c (Fin.last P.r)) →
            D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
            Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
                Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
                (∏ l : Fin P.r, Complex.normSq (c l.castSucc)) *
              (Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) ee ρ ^ 2 *
                ‖B.hsVec ((p.TP.E ρ).comp (p.V (B.opApply (Lq qq) F) (TBB.bigPt P.r c)))‖ ^ 2) ≤
              C * TBB.Gp p (TBB.bigPt P.r c) ^ (-(w.length : ℤ)) *
                ∑ j, ∑ ρ' : M.Ty P, ‖MA.evQ P (MA.actA P (b j * (u j).prod) (trJKB p e (B.JF p.T.base F)) ρ') q‖ ^ 2

def NFHatProdKB : Prop :=
  ∃ C₁ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (L : R.LevelData (MA.A P (MA.DQ P)) P.r),
    IsFrameKB p e → MA.IsModelLevel P (MA.DQ P) L → ∀ (N : ℕ) (u : List (MA.A P (MA.DQ P))), u.length ≤ N →
      (∀ a ∈ u, a ∈ MA.hatSet P L) →
      ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (Th : Fin m → B.DiffOp P.k P.r Wp Wq),
        (∀ k, b k ∈ Submonoid.closure (MA.bddSet P L)) ∧ (∀ k, NFOpOK C₁ p N (Th k)) ∧
        ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
          Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
          MA.actA P u.prod (trJKB p e (B.JF p.T.base F)) =
            ∑ k, MA.actA P (b k) (trJKB p e (B.JF p.T.base (B.opApply (Th k) F)))

def NFBddPtw : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ b ∈ Submonoid.closure (MA.bddSet P L), ∃ C : ℝ, ∀ (u : M.Ty P → MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT),
      ∑ ρ, ‖MA.evQ P (MA.actA P b u ρ) q‖ ^ 2 ≤ C * ∑ ρ, ‖MA.evQ P (u ρ) q‖ ^ 2

def NFTrNormKB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)), IsFrameKB p e → ∃ C : ℝ, ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (c : Fin (P.r + 1) → ℂ) (q : MA.Qp P.r P.TT), q.1 = ((fun l => c l.castSucc), c (Fin.last P.r)) →
      D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
      ∑ ρ, ‖MA.evQ P (trJKB p e (B.JF p.T.base H) ρ) q‖ ^ 2 ≤
        C * (∏ l : Fin P.r, Complex.normSq (c l.castSucc)) * TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)

end

end Formalism.FourierDecayAlt.P.CutBP

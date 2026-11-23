import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped ComplexOrder

namespace Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {m n : ℕ}

section Subst

abbrev complexSquareMatrixFamily (D : D7) (p : D.what₂.Tau → ℕ) : Type := ∀ τ : D.what₂.Tau, Matrix (Fin (p τ)) (Fin (p τ)) ℂ

abbrev complementBlockMatrixFamily (D : D7) (m : ℕ) (p : D.what₂.Tau → ℕ) : Type :=
  ∀ τ : D.what₂.Tau, Matrix (Fin (m - p τ)) (Fin (m - p τ)) ℂ

abbrev HFam (D : D7) (n : ℕ) : Type := D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ

def zPlus (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin (p τ)) (MvPolynomial (FVar D m n) ℂ) :=
  Matrix.of fun c a => varF τ (a : ℕ) (c : ℕ)

def zMinus (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) :
    Matrix (Fin n) (Fin (m - p τ)) (MvPolynomial (FVar D m n) ℂ) :=
  Matrix.of fun c b => varF τ (p τ + (b : ℕ)) (c : ℕ)

def zPlusS (p : D.what₂.Tau → ℕ) (k₁ : complexSquareMatrixFamily D p) (h : HFam D n) (τ : D.what₂.Tau) :
    Matrix (Fin n) (Fin (p τ)) (MvPolynomial (FVar D m n) ℂ) :=
  let hi : Matrix (Fin n) (Fin n) (MvPolynomial (FVar D m n) ℂ) := Matrix.map (h τ)⁻¹ MvPolynomial.C
  let k : Matrix (Fin (p τ)) (Fin (p τ)) (MvPolynomial (FVar D m n) ℂ) := Matrix.map (k₁ τ) MvPolynomial.C
  let z : Matrix (Fin n) (Fin (p τ)) (MvPolynomial (FVar D m n) ℂ) := zPlus p τ
  let hz : Matrix (Fin n) (Fin (p τ)) (MvPolynomial (FVar D m n) ℂ) := hi * z
  hz * k

def zMinusS (p : D.what₂.Tau → ℕ) (k₂ : complementBlockMatrixFamily D m p) (h : HFam D n) (τ : D.what₂.Tau) :
    Matrix (Fin n) (Fin (m - p τ)) (MvPolynomial (FVar D m n) ℂ) :=
  let ht : Matrix (Fin n) (Fin n) (MvPolynomial (FVar D m n) ℂ) := Matrix.map (h τ)ᵀ MvPolynomial.C
  let k : Matrix (Fin (m - p τ)) (Fin (m - p τ)) (MvPolynomial (FVar D m n) ℂ) :=
    Matrix.map (k₂ τ) fun x => MvPolynomial.C (starRingEnd ℂ x)
  let z : Matrix (Fin n) (Fin (m - p τ)) (MvPolynomial (FVar D m n) ℂ) := zMinus p τ
  let hz : Matrix (Fin n) (Fin (m - p τ)) (MvPolynomial (FVar D m n) ℂ) := ht * z
  hz * k

def substVar (p : D.what₂.Tau → ℕ) (k₁ : complexSquareMatrixFamily D p) (k₂ : complementBlockMatrixFamily D m p) (h : HFam D n) :
    FVar D m n → MvPolynomial (FVar D m n) ℂ :=
  fun x => if hx : (x.2.1 : ℕ) < p x.1 then zPlusS p k₁ h x.1 x.2.2 ⟨x.2.1, hx⟩
    else zMinusS p k₂ h x.1 x.2.2 ⟨(x.2.1 : ℕ) - p x.1, by have := x.2.1.isLt; omega⟩

def polySubst (p : D.what₂.Tau → ℕ) (k₁ : complexSquareMatrixFamily D p) (k₂ : complementBlockMatrixFamily D m p) (h : HFam D n) :
    MvPolynomial (FVar D m n) ℂ →ₐ[ℂ] MvPolynomial (FVar D m n) ℂ :=
  MvPolynomial.bind₁ (substVar p k₁ k₂ h)

theorem polySubst_X (p : D.what₂.Tau → ℕ) (k₁ : complexSquareMatrixFamily D p) (k₂ : complementBlockMatrixFamily D m p) (h : HFam D n) (x : FVar D m n) :
    polySubst p k₁ k₂ h (MvPolynomial.X x) = substVar p k₁ k₂ h x := by
  simp [polySubst]

theorem substVar_one (p : D.what₂.Tau → ℕ) :
    substVar (m := m) (n := n) p (fun τ => (1 : Matrix (Fin (p τ)) (Fin (p τ)) ℂ))
      (fun τ => (1 : Matrix (Fin (m - p τ)) (Fin (m - p τ)) ℂ)) (fun _ => 1) = MvPolynomial.X := by
  funext ⟨τ, i, c⟩
  have hi := i.isLt
  have e : ∀ k : ℕ, Matrix.map (1 : Matrix (Fin k) (Fin k) ℂ)
      (MvPolynomial.C : ℂ →+* MvPolynomial (FVar D m n) ℂ) = 1 :=
    fun k => Matrix.map_one _ (map_zero _) (map_one _)
  by_cases hx : (i : ℕ) < p τ
  · simp [substVar, hx, zPlusS, zPlus, varF, e, hi]
  · have h3 : p τ + ((i : ℕ) - p τ) < m := by omega
    simp only [substVar, hx, zMinusS, zMinus, varF, e, dif_neg, not_false_eq_true, transpose_one, Matrix.map_one,
      map_zero, map_one, Matrix.one_mul, Matrix.mul_one, Matrix.of_apply]
    rw [dif_pos (by omega)]
    congr 1
    simp only [Prod.mk.injEq, Fin.ext_iff, true_and, and_true]
    omega

def dExp (m : ℕ) (p : D.what₂.Tau → ℕ) (e : D.what₂.Tau → ℤ) (τ : D.what₂.Tau) : ℤ := (p τ : ℤ) - ((m + 1) / 2 : ℕ) - e τ

def fockChar (p : D.what₂.Tau → ℕ) (a : ℤ) (e : D.what₂.Tau → ℤ)
    (k₁ : complexSquareMatrixFamily D p) (k₂ : complementBlockMatrixFamily D m p) (h : HFam D n) : ℂ :=
  ∏ τ, (k₁ τ).det ^ (a - e τ) * (k₂ τ).det ^ (-a - e τ) * (h τ).det ^ (-dExp m p e τ)

def piAct (p : D.what₂.Tau → ℕ) (a : ℤ) (e : D.what₂.Tau → ℤ)
    (k₁ : complexSquareMatrixFamily D p) (k₂ : complementBlockMatrixFamily D m p) (h : HFam D n) :
    MvPolynomial (FVar D m n) ℂ →ₗ[ℂ] MvPolynomial (FVar D m n) ℂ :=
  fockChar p a e k₁ k₂ h • (polySubst p k₁ k₂ h).toLinearMap

def blockDiagonalOfBlocks (p : D.what₂.Tau → ℕ) (k₁ : complexSquareMatrixFamily D p) (k₂ : complementBlockMatrixFamily D m p) (τ : D.what₂.Tau) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j =>
    if hi : (i : ℕ) < p τ then (if hj : (j : ℕ) < p τ then k₁ τ ⟨i, hi⟩ ⟨j, hj⟩ else 0)
    else if hj : (j : ℕ) < p τ then 0
    else k₂ τ ⟨(i : ℕ) - p τ, by have := i.isLt; omega⟩ ⟨(j : ℕ) - p τ, by have := j.isLt; omega⟩

def sgnDiag (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.diagonal fun i => if (i : ℕ) < p τ then 1 else -1

end Subst

section Equiv

def IsInfEl (θ : InfFam D) (V : HSp D) (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (x : GA D V) : Prop :=
  x ∈ GinfC V ∧ ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) x = g τ

def FockEquiv (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (p : D.what₂.Tau → ℕ) (a : ℤ) (e : D.what₂.Tau → ℤ) : Prop :=
  IsInfFam θ → IsWeilDatumO ψ S T χS χT om → 2 * a = (S.rank : ℤ) → (∀ τ, p τ ≤ T.rank) → Odd T.rank →
  (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, HasInfExp D χS τ (-(e τ : ℚ))) → (∀ τ, HasInfExp D χT τ (-(e τ : ℚ) - 1 / 2)) →
  (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
  (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1 ∧ sS τ * BS τ = BS τ) →
  (∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = sgnDiag p τ ∧ sT τ * BT τ = BT τ * sgnDiag p τ) →
  ∀ (k₁ : complexSquareMatrixFamily D p) (k₂ : complementBlockMatrixFamily D T.rank p) (h : HFam D S.rank),
    (∀ τ, k₁ τ ∈ Matrix.unitaryGroup (Fin (p τ)) ℂ) → (∀ τ, k₂ τ ∈ Matrix.unitaryGroup (Fin (T.rank - p τ)) ℂ) →
    (∀ τ, h τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) →
    ∀ (g : GA D S) (h' : GA D T), IsInfEl θ S (fun τ => BS τ * h τ * (BS τ)⁻¹) g →
      IsInfEl θ T (fun τ => BT τ * blockDiagonalOfBlocks p k₁ k₂ τ * (BT τ)⁻¹) h' →
      ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
        ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ,
          om (g, h') (pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) f P) =
            pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) f
              (piAct p a e k₁ k₂ h P)

end Equiv

end Formalism.IndefR.Datum

end

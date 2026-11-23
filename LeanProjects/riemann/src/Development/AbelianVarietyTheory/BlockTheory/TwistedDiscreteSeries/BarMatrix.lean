import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Links Formalism.IndefR.Mult Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SignCompat {p q n : ℕ} (ε : Fin n → Bool) (e : Ix p q ≃ Fin n) : Prop := ∀ a, ε (e a) = a.isLeft

def plainMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) : Matrix (Fin n) (Fin n) ℂ := Matrix.reindex e e g

def barMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.reindex e e (g.map (starRingEnd ℂ))

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def toFrame (M : DSModel V S) (τ : D.what₂.Tau) (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Matrix (Fin V.rank) (Fin V.rank) ℂ := (M.fr τ)⁻¹ * Y * M.fr τ

open Classical in

structure Matches {p q : ℕ} {T : GrpData p q} (R : DSRep T) (M : DSModel V S) (τ : D.what₂.Tau)
    (φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ) (m : ℤ) (U : M.H τ → R.U.H) : Prop where

  grp : ∀ (g : T.G) (x : M.H τ),
    R.U.π g (U x) = ((T.sq g : ℂˣ) : ℂ) ^ (-m) • U (M.σ τ (φ ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) x)

  kfin : ∀ x : M.H τ, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) x ↔ U x ∈ Set.range R.ι

  smooth : ∀ x : M.H τ, U x ∈ Set.range R.ι → SmoothVec (lieAt V τ) (M.rep τ) x

  lie : (fun Z => toFrame M τ (φ Z)) '' upq p q = lieAt V τ

  der : ∀ Z ∈ upq p q, ∀ (v : R.HK.V) (x : M.H τ), U x = R.ι v →
    U (dRep (M.rep τ) (toFrame M τ (φ Z)) x) = R.ι (R.HK.act Z v + ((m : ℂ) / 2 * Z.trace) • v)

  derT : ∀ Z ∈ upq p q, ∀ (v : R.HK.V) (x : M.Vec) (y : M.sm τ), U (x τ : M.H τ) = R.ι v →
    U (y : M.H τ) = R.ι (R.HK.act Z v + ((m : ℂ) / 2 * Z.trace) • v) →
    DerT M τ (toFrame M τ (φ Z)) (PiTensorProduct.tprod ℂ x) (PiTensorProduct.tprod ℂ (Function.update x τ y))

def HidaSetting (X : ProvA) (p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ) (S : D.what₂.Tau → SPar) (τ : D.what₂.Tau) : Prop :=
  1 ≤ p + q ∧ l₁.length = p ∧ l₂.length = q ∧ IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ) ∧
    HasParam (X.ds p q (ofBlocks l₁ l₂)) (ofBlocks l₁ l₂) ∧ S τ = dualPar (GlobalTheory.Chain.signed l₁ l₂ c)

def SourceBridge (D : D7) : Prop :=
  ∀ (X : ProvA) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
    (p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ), HidaSetting X p q l₁ l₂ c S τ →
    (∃ e : Ix p q ≃ Fin V.rank, SignCompat (M.ε τ) e) ∧
    ∃ m : ℤ, (m : ℚ) = 2 * c ∧ ∀ e : Ix p q ≃ Fin V.rank, SignCompat (M.ε τ) e →
      ∃ U : M.H τ ≃ₗᵢ[ℂ] (X.ds p q (ofBlocks l₁ l₂)).U.H,
        Matches (X.ds p q (ofBlocks l₁ l₂)) M τ (barMat e) m U

def TargetBridge (D : D7) : Prop :=
  ∀ (X : ProvA) (W : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel W S) (τ : D.what₂.Tau)
    (r s : ℕ) (l₁ l₂ : List ℚ) (c : ℚ), HidaSetting X r s l₁ l₂ c S τ →
    (∃ e : Ix r s ≃ Fin W.rank, SignCompat (M.ε τ) e) ∧
    ∃ m : ℤ, (m : ℚ) = 2 * c ∧ ∀ e : Ix r s ≃ Fin W.rank, SignCompat (M.ε τ) e →
      ∃ U : M.H τ ≃ₗᵢ⋆[ℂ] (X.ds r s (ofBlocks l₁ l₂)).U.H,
        Matches (X.ds r s (ofBlocks l₁ l₂)) M τ (plainMat e) m U

def ModelsAreCoverSeries (D : D7) : Prop := SourceBridge D ∧ TargetBridge D

theorem reindex_form {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) :
    Matrix.reindex e e (Formalism.UG.Jpq p q) = Formalism.REAL.Jm ε := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  have ha := h a
  rcases a with a | a <;> rcases b with b | b <;>
    simp_all [Formalism.UG.Jpq, Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp_all

theorem plainMat_mem {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) {g : Mat p q}
    (hg : gᴴ * Formalism.UG.Jpq p q * g = Formalism.UG.Jpq p q) : plainMat e g ∈ Formalism.MainNotions.S.UJset ε := by
  change (plainMat e g)ᴴ * Formalism.REAL.Jm ε * plainMat e g = Formalism.REAL.Jm ε
  rw [← reindex_form h]
  simp only [plainMat, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hg]

theorem barMat_mem {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) {g : Mat p q}
    (hg : gᴴ * Formalism.UG.Jpq p q * g = Formalism.UG.Jpq p q) : barMat e g ∈ Formalism.MainNotions.S.UJset ε := by
  refine plainMat_mem h ?_
  have hJ : (Formalism.UG.Jpq p q).map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> simp [Formalism.UG.Jpq, Matrix.one_apply] <;> split_ifs <;> simp
  have h1 := congrArg (fun A : Mat p q => A.map (starRingEnd ℂ)) hg
  simp only [Matrix.map_mul, hJ] at h1
  exact h1

example : dualPar (GlobalTheory.Chain.signed [2] [-3] (1 / 2)) = {(-5 / 2, true), (5 / 2, false)} := by
  simp [dualPar, GlobalTheory.Chain.signed]
  norm_num

end GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

end

import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleRead

variable {D : D7}

def toUX (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (g : GA D X) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J :=
  ⟨⟨(mt X g).submatrix e e, (mt X g⁻¹).submatrix e e,
    by rw [Matrix.submatrix_mul_equiv]; simp only [Formalism.L2.Theta.mt, map_inv, Units.mul_inv]; exact Matrix.submatrix_one_equiv e,
    by rw [Matrix.submatrix_mul_equiv]; simp only [Formalism.L2.Theta.mt, map_inv, Units.inv_mul]; exact Matrix.submatrix_one_equiv e⟩, by
    subst hJ
    have k : (mt X g)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ * (mt X g).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ := by
      have := congrArg transpose (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram X g)
      rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this
      exact this
    show ((mt X g).submatrix e e)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • (X.gramᵀ).submatrix e e) *
      ((mt X g).submatrix e e).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • (X.gramᵀ).submatrix e e)
    rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((X.gramᵀ).submatrix e e) = (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ).submatrix e e := rfl
    have e2 : ((mt X g).submatrix e e).map (cA D) = ((mt X g).map (cA D)).submatrix e e := rfl
    rw [e1, e2, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, k]⟩

theorem toUX_val (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (g : GA D X) : (toUX X e hJ g).1.1 = (mt X g).submatrix e e := rfl

end GlobalTheory.TripleRead

namespace GlobalTheory.TripleRead

variable {D : D7}

structure IsReading (ψ : AddChar (AF D.host.F) ℂ) {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle) (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) : Prop where

  ψ : Bs.ψ = ψ

  JW : Γ.V.J = (1 : D.host.E) • W.gram

  JW₁ : Γ.V'.J = (-1 : D.host.E) • W₁.gram

  JX : Γ.W.J = D.host.xi0 • (X.gramᵀ).submatrix e e

  cart : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = conj (tauE D τ x)) ∧ Γ.V.θ w = A.cart τ ∧ Γ.V'.θ w = -A₁.cart τ ∧
    Γ.W.θ w = ((B.cart τ).submatrix e e).map conj

  α : Xc.α = α

  β : Xc.β = β

def ptO {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d) (x : Matrix (Fin d) (Fin m) (AE D)) :
    Matrix (Fin m) (Fin k) (AE D) :=
  ((x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹)ᵀ).submatrix id e

def thO {m k : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (ψ : AddChar (AF D.host.F) ℂ) {d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E)
    (e : Fin k ≃ Fin d) (Φ : (Fin m × Fin k → AF D.host.F) → ℂ) (x : Matrix (Fin d) (Fin m) (AE D)) : ℂ :=
  GlobalTheory.WeilM.thetaSum D.host.F (Mo.co.rho ψ (ptO G e x) Φ)

def IsTransp (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) {M X : HSp D} {k : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank}
    {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k} (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Y Z) (ω : WRep M X) (e : Fin k ≃ Fin X.rank)
    (gM : GA D M → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Y.J) (gX : GA D X → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Z.J) : Prop :=
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin k), ∀ g h,
    thO Mo ψ (sgn ε M).gram e (om (gM g, gX h) Φ) = ω (g, h) (thO Mo ψ (sgn ε M).gram e Φ)

end GlobalTheory.TripleRead

end

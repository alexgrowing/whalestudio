import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagSiegel

open MeasureTheory Formalism.IndefR.Datum

def diagInt {F : Type} [Field F] [NumberField F] {κ : Type} (μ : @Measure (κ → AF F) (borel _))
    (Φ : (κ ⊕ κ → AF F) → ℂ) : ℂ :=
  @integral (κ → AF F) ℂ _ _ (borel _) μ (fun u => Φ (Sum.elim u u))

def diagMat {m n : ℕ} {X : Type} (w : Matrix (Fin m) (Fin n) X) : Matrix (Fin m) (Fin (n + n)) X :=
  (Matrix.fromCols w w).submatrix id finSumFinEquiv.symm

def thetaDiagInt {D : D7} {m n : ℕ} (ν : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (f : Mx D m (n + n) → ℂ) : ℂ :=
  ∫ w in 𝓕, f (diagMat w) ∂ν

def ruleFac {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (_c : E →ₐ[R] E) (C : GlobalTheory.WeilM.TestClass R)
    (χ : Eˣ →* Circle) (a : ℕ) {ν : Type} [Fintype ν] [DecidableEq ν] (t : GL ν E) : ℂ :=
  (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    (((C.modu (Units.map (Algebra.norm R : E →* R) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ)

end GlobalTheory.DiagSiegel

end

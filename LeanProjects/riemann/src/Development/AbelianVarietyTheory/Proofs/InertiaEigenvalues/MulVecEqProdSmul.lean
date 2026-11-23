import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightHighestWeightExistsUniqueAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolynomialRepGLComplexAlgebraicWeightEvalPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBorelEigenvectorOfPolynomialRepGLComplexStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRationalPointOrbitAlgebraicWeight
import Formalism.LocalToGlobal.Columns.MtAdWtIrr
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwFixEx
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwFixLine
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GLDense
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

open Matrix

namespace GlobalTheory.MulVecProduct

theorem mulVec_eq_prod_smul {n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] {ι : Type} [Fintype ι]
    [DecidableEq ι] {Φ : (ι → GL (Fin n) ℂ) → Matrix κ κ ℂ}
    (h1 : Φ (1 : ι → GL (Fin n) ℂ) = (1 : Matrix κ κ ℂ))
    (hmul : ∀ (g h : ι → GL (Fin n) ℂ), Φ (g * h) = Φ g * Φ h)
    {v : κ → ℂ} {lam : ι → Fin n → ℤ}
    (hv : ∀ (τ : ι), GlobalTheory.AlgWtHW.IsBEig (fun (B : GL (Fin n) ℂ) ↦ Φ (Pi.mulSingle τ B)) v (lam τ))
    (g : ι → GL (Fin n) ℂ)
    (hg : ∀ (τ : ι), Matrix.BlockTriangular (↑(g τ) : Matrix (Fin n) (Fin n) ℂ) id) :
    Matrix.mulVec (Φ g) v =
      (∏ τ : ι, ∏ i : Fin n, (↑(g τ) : Matrix (Fin n) (Fin n) ℂ) i i ^ lam τ i) • v := by
  classical
  have key : ∀ S : Finset ι, Φ (fun τ => if τ ∈ S then g τ else 1) *ᵥ v =
      (∏ τ ∈ S, ∏ i : Fin n, (↑(g τ) : Matrix (Fin n) (Fin n) ℂ) i i ^ lam τ i) • v := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have h0 : (fun τ : ι => if τ ∈ (∅ : Finset ι) then g τ else 1) = 1 := by
        funext τ
        simp
      rw [h0, h1, Finset.prod_empty, one_smul, Matrix.one_mulVec]
    | insert a S ha ih =>
      have hsplit : (fun τ => if τ ∈ insert a S then g τ else 1) =
          Pi.mulSingle a (g a) * (fun τ => if τ ∈ S then g τ else 1) := by
        funext τ
        by_cases hτ : τ = a
        · subst hτ
          simp [ha]
        · simp [hτ]
      have ha' := (hv a).2 (g a) (hg a)
      simp only at ha'
      rw [hsplit, hmul, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, ha', smul_smul,
        Finset.prod_insert ha]
      congr 1
      ring
  have hall : (fun τ => if τ ∈ (Finset.univ : Finset ι) then g τ else 1) = g := by
    funext τ
    simp
  have := key Finset.univ
  rw [hall] at this
  exact this

end GlobalTheory.MulVecProduct

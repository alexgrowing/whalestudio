import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowerWittTowerIsotropicSplitEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SignEquivInl
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.RealData

theorem isKC_comm_Jpq {p q : ℕ} {b : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hb : IsKC b) :
    b * Formalism.UG.Jpq p q = Formalism.UG.Jpq p q * b := by
  ext a c
  rcases a with i | i <;> rcases c with j | j <;>
    simp [Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]
  · rw [hb (Sum.inl i) (Sum.inr j) (by simp [sameBlock]), neg_zero]
  · rw [hb (Sum.inr i) (Sum.inl j) (by simp [sameBlock]), neg_zero]

theorem conj_mem_Kset {n p q : ℕ} (ε : Fin n → Bool) (e : Fin n ≃ Fin p ⊕ Fin q)
    (hJ : (Formalism.UG.Jpq p q).submatrix e e = Formalism.REAL.Jm ε) (fr g : Matrix (Fin n) (Fin n) ℂ) (hfr : IsUnit fr)
    (hg : gᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * g = frᴴ * Formalism.REAL.Jm ε * fr)
    (b : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (hb : IsKC b)
    (hbA : b * fr.submatrix e.symm id = fr.submatrix e.symm id * g) :
    fr * g * fr⁻¹ ∈ Formalism.REAL.Kset ε := by
  have hdet : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det _).1 hfr
  have hinv : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet

  set X := b.submatrix e e with hX
  have hXfr : X * fr = fr * g := by
    have h1 := congrArg (fun N => N.submatrix e id) hbA
    rw [Matrix.submatrix_mul _ _ _ _ _ e.bijective, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id] at h1
    simpa [Matrix.submatrix_submatrix] using h1
  have hXe : fr * g * fr⁻¹ = X := by
    rw [← hXfr, Matrix.mul_assoc, hinv, Matrix.mul_one]
  rw [hXe]
  have hcomm : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X := by
    rw [← hJ, hX, ← Matrix.submatrix_mul _ _ _ _ _ e.bijective, ← Matrix.submatrix_mul _ _ _ _ _ e.bijective,
      isKC_comm_Jpq hb]

  have hiso : Xᴴ * Formalism.REAL.Jm ε * X = Formalism.REAL.Jm ε := by
    have hgX : g = fr⁻¹ * X * fr := by
      rw [Matrix.mul_assoc, hXfr, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
    have hinvH : (fr⁻¹)ᴴ * frᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one]
    have key : X = fr * g * fr⁻¹ := hXe.symm
    calc Xᴴ * Formalism.REAL.Jm ε * X
        = (fr⁻¹)ᴴ * (gᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * g) * fr⁻¹ := by
          rw [key]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (fr⁻¹)ᴴ * frᴴ * Formalism.REAL.Jm ε * (fr * fr⁻¹) := by
          rw [hg]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hinvH, hinv, Matrix.one_mul, Matrix.mul_one]
  refine ⟨?_, hcomm⟩
  rw [Matrix.mem_unitaryGroup_iff']
  change Xᴴ * X = 1
  calc Xᴴ * X = Xᴴ * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) * X := by rw [Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    _ = Xᴴ * Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε := by
        rw [Matrix.mul_assoc (Xᴴ * Formalism.REAL.Jm ε) X, hcomm]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hiso, Formalism.REAL.Jm_mul_self]

theorem conj_mem_Kset_of_mem_Kinf : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (hV : V.SigOK) (k : GA D V), IsInfFam θ → k ∈ GlobalTheory.Cusp.Kinf θ V (GlobalTheory.ChainOnto.RealData.sortedFrame M hV) → ∀ τ, M.fr τ * infMat D.sp.cm.sig V.gram (θ τ) k * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) := by
  intro D θ V S M hV k hθ hk τ
  obtain ⟨-, hkτ⟩ := GlobalTheory.Cusp.mem_Kinf.1 hk
  obtain ⟨b, hb, hbA⟩ := hkτ τ
  have hU := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V k τ
  have hU' : (infMat D.sp.cm.sig V.gram (θ τ) k)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) *
      infMat D.sp.cm.sig V.gram (θ τ) k = (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ := by
    rw [M.fr_gram τ]; exact hU
  exact conj_mem_Kset (M.ε τ) (signEquiv (M.ε τ) (card_true M hV τ) (card_false M hV τ))
    (Jpq_submatrix _ _) (M.fr τ) _ (M.fr_unit τ) hU' b hb hbA

end GlobalTheory.ChainOnto.RealData

end

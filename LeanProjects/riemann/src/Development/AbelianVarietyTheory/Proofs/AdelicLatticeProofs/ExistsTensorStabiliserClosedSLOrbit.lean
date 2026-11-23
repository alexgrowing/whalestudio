import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLeftTranslationReynoldsOperatorStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsClosedImageSLUnderGeneratingInvariantsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLeftInvariantPolySeparatingCosetStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalInvariantTensorStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MatrixKroneckerPowerTensorActionAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatPolyEvalEqTensorPowerSumRightActionStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_tensor_stabiliser_closed_orbit : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsQGroup Γ → SS Γ → ∃ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), (∀ g ∈ Γ, act d (fun k => ((t k : ℚ) : ℂ)) g = (fun k => ((t k : ℚ) : ℂ))) ∧ (∀ y : Matrix ι ι ℂ, y.det = 1 → act d (fun k => ((t k : ℚ) : ℂ)) y = (fun k => ((t k : ℚ) : ℂ)) → y ∈ Γ) ∧ IsClosed (orb d (fun k => ((t k : ℚ) : ℂ))) := by
  intro ι _ _ Γ hΓ hss
  obtain ⟨Rey, hRey⟩ := GlobalTheory.T.exists_leftTranslation_reynoldsOperator ι Γ hΓ.toIsPre hss
  obtain ⟨m, d, t, hfix, hgen⟩ := GlobalTheory.T.exists_rational_invariant_tensor' ι Γ hΓ.toIsPre hss
  obtain ⟨h1, hmul, -⟩ := (GlobalTheory.T.matrixKroneckerPower_tensorAction_algebra ι ℂ).2 m d (fun k => ((t k : ℚ) : ℂ))
  refine ⟨m, d, t, hfix, ?_, ?_⟩
  · intro y hy hyt
    by_contra hn
    obtain ⟨f, hf, hne⟩ := GlobalTheory.T.exists_leftInvariantPoly_separating_coset ι Γ Rey hΓ hRey y hy hn
    obtain ⟨P, hP⟩ := hgen f hf
    apply hne
    rw [hP, hP, h1, hyt]
  · obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_ratPoly_eval_eq_tensorPowerSumRightAction ι m d t
    have hev : ∀ (y : Matrix ι ι ℂ) (k : TIdx ι d),
        evC (MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) y = act d (fun k => ((t k : ℚ) : ℂ)) y k := by
      intro y k
      have h := hΦ ℂ y k
      simp only [eq_ratCast] at h
      rw [← h, evC, ev, MvPolynomial.eval_map, MvPolynomial.aeval_def]
    have hcl := GlobalTheory.T.isClosed_image_SL_under_generating_invariants ι Γ Rey (TIdx ι d) (fun k => MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) hRey
      hΓ.det_eq (fun k g hg y => by rw [hev, hev, hmul, hfix g hg]) (fun f hf => by
        obtain ⟨P, hP⟩ := hgen f hf
        rw [Algebra.adjoin_range_eq_range_aeval]
        refine ⟨P, ?_⟩
        apply MvPolynomial.funext
        intro x
        have h := hP (Matrix.of fun i j => x (i, j))
        have hx : (fun ij : ι × ι => (Matrix.of fun i j => x (i, j)) ij.1 ij.2) = x := rfl
        have h2 : act d (fun k => ((t k : ℚ) : ℂ)) (Matrix.of fun i j => x (i, j)) =
            fun k => MvPolynomial.eval x (MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) := by
          funext k
          rw [← hev, evC, hx]
        rw [evC, hx, h2] at h
        rw [h]
        show MvPolynomial.eval x (MvPolynomial.aeval _ P) = _
        clear hP h
        induction P using MvPolynomial.induction_on with
        | C a => simp
        | add p q hp hq => simp only [map_add, hp, hq]
        | mul_X p n hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X])
    have : orb d (fun k => ((t k : ℚ) : ℂ)) = {z : TIdx ι d → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧
        z = fun k => evC (MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) y} := by
      ext z
      simp only [orb, hev]
    rw [this]
    exact hcl

end GlobalTheory.ClassFin

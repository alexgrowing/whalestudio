import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

theorem isCMExt_sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (t : E) : σ (σ t) = t := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem hform_incV {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (K : Type) [CommRing K] [Algebra F K] (x y : Fin M → E) :
    Formalism.UG.hform (sigR K σ) (JR K J) (incV K x) (incV K y) = inclR K (hf σ J x y) := by
  simp only [Formalism.UG.hform, hf, incV, JR, map_sum, map_mul, Matrix.map_apply]
  rfl

theorem exists_rational_orth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (K : Type) [Field K] [Algebra F K], ∃ e : Fin M → Fin M → K ⊗[F] E,
      (∀ i j, i ≠ j → Formalism.UG.hform (sigR K σ) (JR K J) (e i) (e j) = 0) ∧
      (∀ i, IsUnit (Formalism.UG.hform (sigR K σ) (JR K J) (e i) (e i))) ∧ IsUnit (Matrix.of e).det := by
  intro F E _ _ _ _ _ σ hσ M J hJ K _ _
  have hcc := isCMExt_sigma_sigma hσ
  obtain ⟨P, d, hP, hd, -, hd0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E)) (G := J)
    two_ne_zero hcc (fun a b => hJ.1 b a)
  have hd0' := hd0 hJ.2
  let x : Fin M → Fin M → E := fun i k => σ (P k i)
  have hx : ∀ i j, hf σ J (x i) (x j) = (Matrix.diagonal d) i j := by
    intro i j
    rw [← hd]
    simp only [hf, x, hcc, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  refine ⟨fun i => incV K (x i), fun i j hij => ?_, fun i => ?_, ?_⟩
  · rw [hform_incV, hx, Matrix.diagonal_apply_ne _ hij, map_zero]
  · rw [hform_incV, hx, Matrix.diagonal_apply_eq]
    exact (IsUnit.mk0 _ (hd0' i)).map _
  · have hm : Matrix.of (fun i => incV (F := F) K (x i)) = ((P.map σ).transpose).map (inclR K) := by
      ext i k
      rfl
    rw [hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_transpose]
    have : (P.map σ).det = σ P.det := (RingHom.map_det (σ : E →+* E) P).symm
    rw [this]
    exact (IsUnit.mk0 _ ((map_ne_zero σ).2 hP)).map _

end GlobalTheory.CompanionTheory.SaGen

import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage

theorem exists_leftInv_frame_kill_emb : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∃ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 ∧ K * B = 0 := by
  intro D V V' r C B hs
  have hadj : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), adj D X = Xᴴ := fun X => rfl
  have hG : V.gramᴴ = V.gram := by
    ext i j; simp [Matrix.conjTranspose_apply, GlobalTheory.LatVac.gram_star]
  have hBC : adj D B * V.gram * C = 0 := by
    have h := congrArg Matrix.conjTranspose hs.orth
    rw [hadj] at h ⊢
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h
  let f := C.mulVecLin.coprod B.mulVecLin
  have hf : ∀ c b, f (c, b) = C *ᵥ c + B *ᵥ b := fun c b => rfl
  have hker : LinearMap.ker f = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun ⟨c, b⟩ h => ?_
    rw [hf] at h
    have h1 := congrArg ((adj D B * V.gram).mulVec) h
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBC, hs.isom, Matrix.zero_mulVec,
      zero_add, Matrix.mulVec_zero] at h1
    have hb : b = 0 := Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (GlobalTheory.LatVac.gram_det_isUnit V')) (by rw [h1, Matrix.mulVec_zero])
    subst hb
    rw [Matrix.mulVec_zero, add_zero] at h
    have hc : c = 0 := Matrix.mulVec_injective_iff.2 hs.frame.2.1 (by rw [h, Matrix.mulVec_zero])
    subst hc
    rfl
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hker
  have key : ∀ c b, g (C *ᵥ c + B *ᵥ b) = (c, b) := fun c b => by
    rw [← hf]; exact LinearMap.congr_fun hg (c, b)
  have k1 : ∀ c, g (C *ᵥ c) = (c, 0) := fun c => by simpa using key c 0
  have k2 : ∀ b, g (B *ᵥ b) = (0, b) := fun b => by simpa using key 0 b
  refine ⟨LinearMap.toMatrix' (LinearMap.fst _ _ _ ∘ₗ g), ?_, ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp [Matrix.toLin'_mul, Matrix.toLin'_apply, k1]
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp [Matrix.toLin'_mul, Matrix.toLin'_apply, k2]

end GlobalTheory.HalfAverage

end

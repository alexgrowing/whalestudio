import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneBasisChangeMatrix
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_basis_change_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d₁ r' s' i₀ i₁ : ℕ) (W : Spc F E (d₁ + 2)) (W₁ : Spc F E d₁) (H' : Plane E (d₁ + 2) d₁)
    (Q : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E), W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ →
    (∀ r a, Q r (Fin.castAdd 2 a) = H'.ι r a) → (∀ r, Q r (Fin.natAdd d₁ 0) = H'.x r) →
    (∀ r, Q r (Fin.natAdd d₁ 1) = H'.y r) → Q.det ≠ 0 := by
  first | exact @GlobalTheory.ThK.FrameDet.frame_det_ne_zero | exact GlobalTheory.ThK.FrameDet.frame_det_ne_zero | (intros; apply GlobalTheory.ThK.FrameDet.frame_det_ne_zero <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointInvolution
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Idem3

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipHaar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_adjoint_involution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ x, σ (σ x) = x) → (∀ i j, σ (J j i) = -J i j) → J.det ≠ 0 → Continuous (adj σ J) ∧ (∀ X Y, adj σ J (X * Y) = adj σ J Y * adj σ J X) ∧ (∀ X, adj σ J (adj σ J X) = X) ∧ (∀ X ∈ ((inclR (F := F) (E := E) (AF F)).mapMatrix (m := Fin n)).range, adj σ J X ∈ ((inclR (F := F) (E := E) (AF F)).mapMatrix (m := Fin n)).range) ∧ ∀ X, adj σ J X * X = 1 ↔ Xᵀ * incM F J * X.map (cA σ) = incM F J := by
  first | exact @GlobalTheory.UnipHaar.adj_props | exact GlobalTheory.UnipHaar.adj_props | (intros; apply GlobalTheory.UnipHaar.adj_props <;> assumption)

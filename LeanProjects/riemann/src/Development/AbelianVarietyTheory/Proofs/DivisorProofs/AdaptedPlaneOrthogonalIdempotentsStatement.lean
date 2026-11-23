import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneOrthogonalIdempotents
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Idem3

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipHaar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_orthogonal_idempotents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ : ℕ), (∀ x, σ (σ x) = x) → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 → H.IsAdapted σ B W W₁ i₀ i₁ → CompleteOrthogonalIdempotents (idem3 σ W.J H) ∧ (∀ a, idem3 σ W.J H a ∈ ((inclR (F := F) (E := E) (AF F)).mapMatrix (m := Fin n)).range) ∧ ∀ a, ∃ a', GlobalTheory.UnipHaar.adj σ W.J (idem3 σ W.J H a) = idem3 σ W.J H a' ∧ wt3 a' = -wt3 a := by
  first | exact @GlobalTheory.ProjIdem.idem_main | exact GlobalTheory.ProjIdem.idem_main | (intros; apply GlobalTheory.ProjIdem.idem_main <;> assumption)

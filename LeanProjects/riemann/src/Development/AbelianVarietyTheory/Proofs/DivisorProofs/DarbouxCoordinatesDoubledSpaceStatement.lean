import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesDoubledSpace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darboux_coordinates_doubled_space : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n m : ℕ)
    (J : Matrix (Fin m) (Fin m) E) (J' : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    J₂ = dblGram finSumFinEquiv J' →
    ∀ d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')) (Fin m × Fin n),
      (∀ x : Matrix (Fin m) (Fin n) E, ∃ y z : Fin m × Fin n → F,
        d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J₂)) (Fin m × Fin (n + n)),
      (∀ x : Matrix (Fin m) (Fin (n + n)) E, ∃ y z : Fin m × Fin (n + n) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) ∧
      (∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) := by
  first | exact @GlobalTheory.SWAniso.exists_rational_dblCoord_right | exact GlobalTheory.SWAniso.exists_rational_dblCoord_right | (intros; apply GlobalTheory.SWAniso.exists_rational_dblCoord_right <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLagrangianVecMulVecCoords
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIncMLagP

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_lagrangian_vecMulVec_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (κ : Type) [Fintype κ]
    (De : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) →ₗ[AF F] (κ → AF F) × (κ → AF F))
    (D : Matrix (Fin d) (Fin n ⊕ Fin n) E →ₗ[F] (κ → F) × (κ → F)), (∀ u, De (incM F u) = GlobalTheory.SiegelConv.ratP (D u)) →
    ∀ (w : Fin d → E) (t : Fin n × Fin (Module.finrank F E) → AF F),
      De (Matrix.vecMulVec (incV F w) (Sum.elim (GlobalTheory.SiegelConv.basisMap F E n t) (GlobalTheory.SiegelConv.basisMap F E n t))) =
        GlobalTheory.SiegelConv.extA (D ∘ₗ GlobalTheory.SiegelConv.vvMap F (n := n) w) t := by
  first | exact @GlobalTheory.SiegelConv.De_vecMulVec_basisMap | exact GlobalTheory.SiegelConv.De_vecMulVec_basisMap | (intros; apply GlobalTheory.SiegelConv.De_vecMulVec_basisMap <;> assumption)

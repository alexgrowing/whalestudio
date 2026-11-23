import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactFixesVacuumNonsplit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_fixes_vacuum_nonsplit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → v ∉ X.T → ∀ k ∈ KAt σ G.W v,
      Acts (evFin F v) (om (1, k)) (G.M.vac v) (G.M.vac v) := by
  first | exact @GlobalTheory.VacFixKAt.vacFixed | exact GlobalTheory.VacFixKAt.vacFixed | (intros; apply GlobalTheory.VacFixKAt.vacFixed <;> assumption)

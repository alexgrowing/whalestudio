import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmAdeleSplitComplexFiniteAdeles
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValHalfInf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmType
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorFiniteAdeleEquiv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousSymmFinite
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmAdele_split_complex_finiteAdeles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ e : (AF F ⊗[F] E) ≃+* (InfinitePlace E → ℂ) × FiniteAdeleRing (𝓞 E) E, Continuous e.symm ∧ (∀ x : E, e (inclR (F := F) (AF F) x) = (fun w : InfinitePlace E => w.embedding x, algebraMap E (FiniteAdeleRing (𝓞 E) E) x)) ∧ e (halfE F E).1 = (fun _ => 2⁻¹, 1) := by
  first | exact @GlobalTheory.Eis.Conv.AdeleCMSplit.exists_adele_split | exact GlobalTheory.Eis.Conv.AdeleCMSplit.exists_adele_split | (intros; apply GlobalTheory.Eis.Conv.AdeleCMSplit.exists_adele_split <;> assumption)

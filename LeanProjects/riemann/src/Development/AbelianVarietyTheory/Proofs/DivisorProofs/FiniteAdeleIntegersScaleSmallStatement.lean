import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleIntegersScaleSmall
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombineApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchPartFinIncl
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adele_integers_scale_small : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ U ∈ nhds (0 : AE F E), ∃ N : ℕ, 1 ≤ N ∧ ∀ y ∈ Formalism.MainNotions.S.IntAf F E, GlobalTheory.ArchFinSplit.finIncl F E ((N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * y) ∈ U := by
  first | exact @GlobalTheory.FinInclSmall.finIncl_small | exact GlobalTheory.FinInclSmall.finIncl_small | (intros; apply GlobalTheory.FinInclSmall.finIncl_small <;> assumption)

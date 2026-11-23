import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairInducedEquivProd
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_induced_equiv_prod : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (b' : Fin 2 → ℕ) (d : ℕ) (h : b' 0 + b' 1 = d) (μ : Fin 2 → kˣ →* ℂˣ),
    Nonempty (Representation.Equiv ((GlobalTheory.LeviBlockExponent.pairInd k b' h μ).comp (GlobalTheory.CuspBlock.glCast h))
      (GlobalTheory.SmGL.prod₂ (GlobalTheory.SmGL.detRep (Fin (b' 0)) (μ 0)) (GlobalTheory.SmGL.detRep (Fin (b' 1)) (μ 1)))) := by
  first | exact @GlobalTheory.PairIndProd.pairInd_equiv_prod₂ | exact GlobalTheory.PairIndProd.pairInd_equiv_prod₂ | (intros; apply GlobalTheory.PairIndProd.pairInd_equiv_prod₂ <;> assumption)

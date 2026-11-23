import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairInducedTwistEquiv
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
theorem _root_.GlobalTheory.T.pair_induced_twist_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (b' : Fin 2 → ℕ) (d : ℕ) (h : b' 0 + b' 1 = d) (μ : Fin 2 → kˣ →* ℂˣ) (ν : kˣ →* ℂˣ),
    GlobalTheory.SmGL.IsSmoothChar ν →
    Nonempty ((GlobalTheory.SmGL.twist (GlobalTheory.LeviBlockExponent.pairInd k b' h μ) (GlobalTheory.SmGL.detChar (Fin d) ν)).Equiv
      (GlobalTheory.LeviBlockExponent.pairInd k b' h (fun i => μ i * ν))) := by
  first | exact @GlobalTheory.LeviBlockExponent.twist_pairInd | exact GlobalTheory.LeviBlockExponent.twist_pairInd | (intros; apply GlobalTheory.LeviBlockExponent.twist_pairInd <;> assumption)

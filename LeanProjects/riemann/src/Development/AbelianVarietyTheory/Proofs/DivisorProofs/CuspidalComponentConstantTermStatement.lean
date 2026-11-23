import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalComponentConstantTerm
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
theorem _root_.GlobalTheory.T.cuspidal_component_constant_term : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K → ∀ (S : Finset (Fin r)) (φ ψ φc ψc : GAd σ J → ℂ),
      IsAut σ J K φ → IsAut σ J K ψ →
      GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K φ φc → GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K ψ ψc →
      (∀ a b : ℂ, GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K (a • φ + b • ψ) (a • φc + b • ψc)) ∧
      ∀ (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v),
        GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K (fun y => φ (y * emb σ J v x)) (fun y => φc (y * emb σ J v x)) := by
  first | exact @GlobalTheory.CuspCompLin.isCuspComp_linear_transl | exact GlobalTheory.CuspCompLin.isCuspComp_linear_transl | (intros; apply GlobalTheory.CuspCompLin.isCuspComp_linear_transl <;> assumption)

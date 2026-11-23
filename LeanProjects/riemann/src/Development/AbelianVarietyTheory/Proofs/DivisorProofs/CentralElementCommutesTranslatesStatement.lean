import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralElementCommutesTranslates
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_element_commutes_translates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)), IsDer σ J τ D →
    ∀ u ∈ Algebra.adjoin ℂ (Set.range D), (∀ X, D X * u = u * D X) → ∀ (a : GAd σ J) (f f' : SmG σ J),
      (f'.1 = fun x => f.1 (x * a)) → (u f').1 = fun x => (u f).1 (x * a) := by
  first | exact @GlobalTheory.LeviHC.RightTr.comm_rtr | exact GlobalTheory.LeviHC.RightTr.comm_rtr | (intros; apply GlobalTheory.LeviHC.RightTr.comm_rtr <;> assumption)

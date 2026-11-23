import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationsCommuteDistinctPlaces
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivations_commute_distinct_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)), IsDer σ J τ D →
    ∀ (w' : InfinitePlace F) (τ' : EmbOver E w') (D' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)),
    IsDer σ J τ' D' → w ≠ w' → ∀ X X', D X * D' X' = D' X' * D X := by
  first | exact @GlobalTheory.LeviHC.der_comm_of_ne | exact GlobalTheory.LeviHC.der_comm_of_ne | (intros; apply GlobalTheory.LeviHC.der_comm_of_ne <;> assumption)

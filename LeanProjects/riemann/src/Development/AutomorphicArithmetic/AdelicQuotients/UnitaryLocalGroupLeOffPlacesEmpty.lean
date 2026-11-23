import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.WeilBound.ThetaLifts.LatticeBasics.EulerProd
import Development.WeilBound.ThetaLifts.LatticeBasics.BadFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockScaledIntegralOfLocal
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExtensionEmbeddingEvInfRealAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcCompFinAwayPtOfNotMem

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP

private theorem evInf_realAd_one {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) :
    evInf F w (realAd F 1) = 1 := by
  apply (InfinitePlace.Completion.extensionEmbedding w).injective
  rw [GlobalTheory.CompanionTheory.RealAdeleComponent.extensionEmbedding_evInf_realAd, map_one]
  simp

theorem UpperTheory.unitaryLocalGroup_le_offPlaces_empty :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n} (v : Pl F), locGrp σ X v ≤ gOff σ X ∅ := by
  intro F E _ _ _ _ _ σ n X v
  refine (Subgroup.closure_le _).2 fun g hg => Subgroup.subset_closure ⟨fun w => ?_, by simp⟩
  have h0 : realAd F 1 • (mat g - 1) = 0 := hg _ (GlobalTheory.ThKTorus.IntegralOfAdic.evFin_realAd F v 1)
  ext i j
  have e := congrArg (fun M : Matrix (Fin n) (Fin n) (AE F E) => compInf F E w (M i j)) h0
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, map_zero] at e
  rw [GlobalTheory.AwayFix.Chart.compInf_smul_away, evInf_realAd_one, one_smul, map_sub, sub_eq_zero] at e
  rw [Matrix.map_apply, e, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

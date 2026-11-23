import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanLevelSubgroupClosedMul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_level_subgroup_closed_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W τ ∧ (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W τ, ∀ k' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W τ, k * k' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W τ) ∧ ∀ l ∈ GlobalTheory.ThKAdm.FinPt σ W, ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W τ, l * k = k * l := by
  first | exact @GlobalTheory.kInf_one_mul_commute_finPt | exact GlobalTheory.kInf_one_mul_commute_finPt | (intros; apply GlobalTheory.kInf_one_mul_commute_finPt <;> assumption)

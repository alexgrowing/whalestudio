import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSubgroupOpenNeighbourhood
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_subgroup_open_neighbourhood : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (L K : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)), GlobalTheory.ThKAdm.IsLevel W L → (∀ g ∈ K, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (GlobalTheory.AdelicU.evFin F v)) → (∃ O : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J), IsOpen O ∧ (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J) ∈ O ∧ ∀ g ∈ O, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (GlobalTheory.AdelicU.evFin F v) → g ∈ K) → GlobalTheory.ThKAdm.IsLevel W (Subgroup.closure ((K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)) ∪ {l | l ∈ L ∧ ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (GlobalTheory.AdelicU.evFin F v), l * h = h * l})) := by
  first | exact @GlobalTheory.isLevel_closure_at_place | exact GlobalTheory.isLevel_closure_at_place | (intros; apply GlobalTheory.isLevel_closure_at_place <;> assumption)

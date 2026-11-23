import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneRestriction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_adapted_plane_restriction : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d₁) (H' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → (∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∃ fa fb, GlobalTheory.ThK.Split2 W₁ H' X (G.M.I om Φ) fa fb) ∧ ∀ Φ' ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∃ fa fb, GlobalTheory.ThK.Split2 W₁ H' X (G.M'.I om' Φ') fa fb := by
  first | exact @GlobalTheory.ThKSplitEx.splitEx_exists | exact GlobalTheory.ThKSplitEx.splitEx_exists | (intros; apply GlobalTheory.ThKSplitEx.splitEx_exists <;> assumption)

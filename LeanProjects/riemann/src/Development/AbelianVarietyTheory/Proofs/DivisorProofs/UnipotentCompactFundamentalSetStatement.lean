import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCompactFundamentalSet
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_compact_fundamental_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ →
    ∃ K : Set (unip σ G.W H'), IsCompact K ∧ ∀ u : unip σ G.W H', ∃ γ ∈ (ratU σ G.W.J).subgroupOf (unip σ G.W H'), γ * u ∈ K := by
  first | exact @GlobalTheory.ThK.UnipCocompact.exists_compact_rat_mul_mem | exact GlobalTheory.ThK.UnipCocompact.exists_compact_rat_mul_mem | (intros; apply GlobalTheory.ThK.UnipCocompact.exists_compact_rat_mul_mem <;> assumption)

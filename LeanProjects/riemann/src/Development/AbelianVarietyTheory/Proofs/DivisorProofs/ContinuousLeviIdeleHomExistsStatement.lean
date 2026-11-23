import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeviIdeleHomExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_levi_idele_hom_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∃ mt : (AE F E)ˣ →* UA σ G.W.J, (∀ g, Continuous fun t => mt t * g) ∧ (∀ t, IsLevi (W₁ := W₁) H' t 1 (mt t)) ∧ (∀ x : Eˣ, mt (Units.map (inclR (F := F) (AF F)).toMonoidHom x) ∈ ratU σ G.W.J) ∧ ∀ t, ∀ u ∈ unip σ G.W H', mt t * u * (mt t)⁻¹ ∈ unip σ G.W H' := by
  first | exact @GlobalTheory.LeviIdeleHom.levi_hom | exact GlobalTheory.LeviIdeleHom.levi_hom | (intros; apply GlobalTheory.LeviIdeleHom.levi_hom <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviActionLocalGoodPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipAugLeJacKer
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_action_local_good_place : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ v, X.Good v → ∀ (t : (AE F E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' t 1 m → m ∈ UAt σ G.W (evFin F v) → ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ ψ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ ψ' ∈ SB (Fin a × Fin (a + a') → Fv F v), φ - ψ - ψ' ∈ GlobalTheory.JacquetLine.jacKer om H' v → ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, m)) φ φ₁ → ∃ ψ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∃ ψ₁' ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, m)) ψ ψ₁ ∧ Acts (evFin F v) (om (1, m)) ψ' ψ₁' ∧ φ₁ - ψ₁ - ψ₁' ∈ GlobalTheory.JacquetLine.jacKer om H' v := by
  first | exact @GlobalTheory.JacquetLevi.transport | exact GlobalTheory.JacquetLevi.transport | (intros; apply GlobalTheory.JacquetLevi.transport <;> assumption)

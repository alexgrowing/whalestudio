import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeInvariantVectorLocalSupport
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_invariant_vector_local_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d)) (v : Pl F)
      (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)),
      (∀ γ ∈ latAtV X W v, GlobalTheory.LatVac.psiAt B.ψ v ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2) = 1) →
      w ∈ (latAtV X W v).map (GlobalTheory.LatVac.locCo co v) := by
  first | exact @GlobalTheory.LatSelfDualCo.latAtV_selfDual_locCo | exact GlobalTheory.LatSelfDualCo.latAtV_selfDual_locCo | (intros; apply GlobalTheory.LatSelfDualCo.latAtV_selfDual_locCo <;> assumption)

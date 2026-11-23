import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallUnitaryPreservesSchwartzSupport
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_unitary_preserves_schwartz_support : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (M : Model σ X W)
    (Mo : AddSubgroup (Fin n × Fin d → Af F)) (K : Set (Fin n × Fin d → Af F)),
    IsOpen (Mo : Set (Fin n × Fin d → Af F)) → IsCompact K →
    ∀ᶠ k in 𝓝 (1 : UA σ W.J), (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 →
      ∀ w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F), (fun i => (w.1 i).2) ∈ K → (fun i => (w.2 i).2) ∈ K →
        (∀ i, ((M.co.e (actAB (cA σ) ((1 : UA σ X.J), k) (M.co.e.symm w)) - w).1 i).1 = 0 ∧
          ((M.co.e (actAB (cA σ) ((1 : UA σ X.J), k) (M.co.e.symm w)) - w).2 i).1 = 0) ∧
        (fun i => ((M.co.e (actAB (cA σ) ((1 : UA σ X.J), k) (M.co.e.symm w)) - w).1 i).2) ∈ Mo ∧
        (fun i => ((M.co.e (actAB (cA σ) ((1 : UA σ X.J), k) (M.co.e.symm w)) - w).2 i).2) ∈ Mo := by
  first | exact @GlobalTheory.WeilSmallAct.smallAct | exact GlobalTheory.WeilSmallAct.smallAct | (intros; apply GlobalTheory.WeilSmallAct.smallAct <;> assumption)

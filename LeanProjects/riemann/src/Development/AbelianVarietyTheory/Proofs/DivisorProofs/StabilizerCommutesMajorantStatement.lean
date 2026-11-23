import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCommutesMajorant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_commutes_majorant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n), X.L.IsLattice E →
    ∀ g : GAd σ X.Jᵀ, GlobalTheory.IwLine.ofGAd σ X.J g ∈ GlobalTheory.StabHaar.stabK (σ := σ) B X →
      (∀ w, Commute ((matHom w.Completion σ X.Jᵀ (projArch σ X.Jᵀ w g)).1.map (infEmb (B.emb w))) (X.θ w)) ∧
      ∀ v, proj σ X.Jᵀ v g ∈ stabLoc σ X.Jᵀ X.L v := by
  first | exact @GlobalTheory.KBridgeConv.local_of_ofGAd_mem_stabK | exact GlobalTheory.KBridgeConv.local_of_ofGAd_mem_stabK | (intros; apply GlobalTheory.KBridgeConv.local_of_ofGAd_mem_stabK <;> assumption)

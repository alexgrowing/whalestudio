import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormBaseChangeMatrix
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_form_base_change_matrix : ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S) {α α' β : Type} [Fintype α] [Fintype α'] [Fintype β]
    (JA : Matrix α α S) (JB : Matrix β β S) (P : Matrix α α' S) (z z' : Matrix α' β S),
    symp c ξ JA JB (P * z) (P * z') = symp c ξ (Pᵀ * JA * P.map c) JB z z' := by
  first | exact @GlobalTheory.symp_mul_left | exact GlobalTheory.symp_mul_left | (intros; apply GlobalTheory.symp_mul_left <;> assumption)

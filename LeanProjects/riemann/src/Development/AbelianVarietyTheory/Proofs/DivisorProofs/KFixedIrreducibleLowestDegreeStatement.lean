import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFixedIrreducibleLowestDegree
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.RealLift Formalism.BasicNotions.TH
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.k_fixed_irreducible_lowest_degree : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P Q R S : ℕ) (x : ι → ℚ), P ≤ R → Q ≤ S →
    (∀ w, ∃ k k' : ℕ, 0 < k ∧ 0 < k' ∧ x w - Formalism.BasicNotions.TH.cPair R S = k ∧ x w + Formalism.BasicNotions.TH.cPair R S = k') →
    ∀ m : ℕ, (∀ m' < m, GlobalTheory.KFixIrr.chiPart ι P Q R S x ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S m' = ⊥) →
    ∀ N : Submodule ℂ (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S),
      N ≤ GlobalTheory.KFixIrr.chiPart ι P Q R S x ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S m →
      (∀ w (Z : Formalism.BasicNotions.TH.Mat R S), Formalism.BasicNotions.TH.IsKC Z → ∀ T ∈ N,
        GlobalTheory.RealLift.atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (Formalism.BasicNotions.TH.fockAct2 P Q R S Z) T ∈ N) →
      N = ⊥ ∨ N = GlobalTheory.KFixIrr.chiPart ι P Q R S x ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S m := by
  first | exact @GlobalTheory.KFixIrr.lowest_irr | exact GlobalTheory.KFixIrr.lowest_irr | (intros; apply GlobalTheory.KFixIrr.lowest_irr <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralTraceDualRational
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiFinRat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical
open GlobalTheory.BoxLattice GlobalTheory.EvAdm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_trace_dual_rational : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ μ : κ → mixedEmbedding.mixedSpace F, (∀ l ∈ boxLat F κ a, ∃ k : ℤ, GlobalTheory.VacLn.trPair F κ l μ = k) →
      ∃ z : κ → F, μ = ratInf F κ z := by
  first | exact @GlobalTheory.BoxLattice.dual_rat | exact GlobalTheory.BoxLattice.dual_rat | (intros; apply GlobalTheory.BoxLattice.dual_rat <;> assumption)

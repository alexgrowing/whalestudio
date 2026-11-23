import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumCosetLattice
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
theorem _root_.GlobalTheory.T.theta_sum_coset_lattice : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ (r : κ → FiniteAdeleRing (𝓞 F) F) (ρ : κ → F), ratFin F κ ρ - r ∈ scaledInt F κ a →
    ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      thetaSum F (pureA F f (Set.indicator {y | y - r ∈ scaledInt F κ a} fun _ => (1 : ℂ))) =
        ∑' l : boxLat F κ a, f (ratInf F κ ρ + l) := by
  first | exact @GlobalTheory.ThetaCoset.thetaSum_coset | exact GlobalTheory.ThetaCoset.thetaSum_coset | (intros; apply GlobalTheory.ThetaCoset.thetaSum_coset <;> assumption)

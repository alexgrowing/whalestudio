import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxLatticeDualCharacter
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
theorem _root_.GlobalTheory.T.box_lattice_dual_character : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ a : F, a ≠ 0 → ∀ z : κ → F, (∀ l ∈ boxLat F κ a, ∃ k : ℤ, GlobalTheory.VacLn.trPair F κ l (ratInf F κ z) = k) →
      ∀ u ∈ scaledInt F κ a, ψ (pairA F 0 (u ⬝ᵥ ratFin F κ z)) = 1 := by
  first | exact @GlobalTheory.BoxLattice.psi_fin_scaledInt_dot | exact GlobalTheory.BoxLattice.psi_fin_scaledInt_dot | (intros; apply GlobalTheory.BoxLattice.psi_fin_scaledInt_dot <;> assumption)

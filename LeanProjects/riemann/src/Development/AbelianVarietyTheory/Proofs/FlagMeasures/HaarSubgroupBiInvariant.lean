import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularOfContracted

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.UnipUnimod

section General

open scoped Pointwise NNReal ENNReal

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem unimod_of_contract (N : Subgroup G) (hN : IsClosed (N : Set G)) {ν : Measure G}
    (h : IsHaarSub (N : Set G) ν) (a : ℝ → G) (h1 : ∀ s, ∀ m ∈ N, a s * m * (a s)⁻¹ ∈ N)
    (h2 : ∀ s, ∀ m ∈ N, (a s)⁻¹ * m * a s ∈ N)
    (h3 : ∀ m ∈ N, Filter.Tendsto (fun s => a s * m * (a s)⁻¹) Filter.atBot (nhds 1)) :
    (∀ m ∈ N, ν.map (fun x => x * m) = ν) ∧ ν.map (fun x => x⁻¹) = ν := by
  first
  | exact @_root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted
  | exact _root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted
  | (apply _root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted <;> assumption)
  | (intros; apply _root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted ..)

end General

theorem unimodular_NW : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → (∀ m ∈ NW ε W, ν.map (fun x => x * m) = ν) ∧ ν.map (fun x => x⁻¹) = ν := by
  intro n ε W ν hW hν
  obtain ⟨a, Hm, -, ha, -, h1, h3, -⟩ := GlobalTheory.T.isotropic_splitTorus_iwasawa_unitaryGroup n ε W hW
  have hinv : ∀ s, a (-s) = (a s)⁻¹ := fun s => by
    refine eq_inv_of_mul_eq_one_left (Subtype.ext (Units.ext ?_))
    change umat (a (-s)) * umat (a s) = 1
    rw [ha, ha, Complex.ofReal_neg, neg_smul,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl ((s : ℂ) • Hm)).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  refine unimod_of_contract (nwSub ε W) (isClosed_NW ε W) hν a (fun s m hm => (h1 s m hm).1)
    (fun s m hm => ?_) h3
  have := (h1 (-s) m hm).1
  rwa [hinv, inv_inv] at this

end GlobalTheory.UnipUnimod

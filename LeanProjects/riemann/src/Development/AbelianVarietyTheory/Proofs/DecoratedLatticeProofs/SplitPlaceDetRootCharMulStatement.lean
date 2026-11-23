import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDetRootCharMul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_detRootChar_mul : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle) (n : ℕ), Even n → ResEta D μ n → ∀ e, IsSplitIdem D e → ∀ (s g : GA D V), SuppAt e V s → ∀ x₀ x x₁, IsDetAt e V s x₀ → IsDetRoot V g x → IsDetRoot V (s * g) x₁ → μ x₁ = μ x₀ * μ x := by
  first | exact @GlobalTheory.SplitRootProd.mu_root_mul | exact GlobalTheory.SplitRootProd.mu_root_mul | (intros; apply GlobalTheory.SplitRootProd.mu_root_mul <;> assumption)

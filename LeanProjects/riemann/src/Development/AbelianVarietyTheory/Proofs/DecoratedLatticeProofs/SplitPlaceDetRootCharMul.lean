import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitRootProd

theorem mu_root_mul : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle) (n : ℕ), Even n → ResEta D μ n → ∀ e, IsSplitIdem D e → ∀ (s g : GA D V), SuppAt e V s → ∀ x₀ x x₁, IsDetAt e V s x₀ → IsDetRoot V g x → IsDetRoot V (s * g) x₁ → μ x₁ = μ x₀ * μ x := by
  intro D V μ n hn hres e he s g hs x₀ x x₁ h0 hx hx1
  have r0 : IsDetRoot V s x₀ := Formalism.L2.Theta.isDetAt_root he V s hs x₀ h0
  have r : IsDetRoot V (s * g) (x₀ * x) := GlobalTheory.Member.isDetRoot_mul V s g x₀ x r0 hx
  obtain ⟨a, ha⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 (s * g) (x₀ * x) x₁ r hx1
  obtain ⟨⟨η, hη⟩, hall⟩ := hres
  have hμ := hall η hη a
  obtain ⟨k, hk⟩ := hn
  rw [ha, map_mul, hμ, hk, ← two_mul, pow_mul, Formalism.L2.Theta.eta_sq hη a, one_pow, mul_one, map_mul]

end GlobalTheory.SplitRootProd

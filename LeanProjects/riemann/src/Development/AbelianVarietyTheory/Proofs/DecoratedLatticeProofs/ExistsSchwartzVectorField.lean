import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.CentreSchwartz

variable {D : D7} {θ : InfFam D} {V : HSp D} {n : ℕ} {τ : D.what₂.Tau}

def mulAt (τ : D.what₂.Tau) {m : ℕ} (n : ℕ) (Y : Matrix (Fin m) (Fin m) ℂ) :
    (D.what₂.Tau → Fin m → Fin n → ℂ) →ₗ[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ) where
  toFun z := fun τ' i j => if τ' = τ then ∑ k, Y i k * z τ' k j else 0
  map_add' z z' := by
    funext τ' i j
    by_cases h : τ' = τ <;> simp [h, mul_add, Finset.sum_add_distrib]
  map_smul' c z := by
    funext τ' i j
    by_cases h : τ' = τ <;> simp [h, Finset.mul_sum, mul_left_comm]

variable (θ V n) in

def Induced (T : (GA D V → ℂ) → GA D V → ℂ) : Prop :=
  ∀ Φ ∈ schwartzA θ V.rank n, ∃ Ψ ∈ schwartzA θ V.rank n,
    ∀ x : Mx D V.rank n, T (fun h => Φ (mt V h⁻¹ ⬝ x)) = fun h => Ψ (mt V h⁻¹ ⬝ x)

theorem Induced.sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (A : ι → (GA D V → ℂ) → GA D V → ℂ)
    (h : ∀ i, Induced θ V n (A i)) : Induced θ V n fun f => ∑ i ∈ s, c i • A i f := by
  intro Φ hΦ
  choose Ψ m e using fun i => h i Φ hΦ
  refine ⟨∑ i ∈ s, c i • Ψ i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (m i), fun x => ?_⟩
  funext g
  simp only [e, Finset.sum_apply, Pi.smul_apply]

end GlobalTheory.RegSch.CentreSchwartz

end

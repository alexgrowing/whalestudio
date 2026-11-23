import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalExactSequenceContinuityAllTheories

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

noncomputable section

open Formalism Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage GlobalTheory.FundCont Filter Topology

namespace GlobalTheory.ContDR

theorem cont_dR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ (k : ℕ) (x : Fin k → V ⊗[ℚ_[l]] P.R.BdR) (β : Fin k → ↥(GK K) → ℚ_[l]), (∀ i, Continuous (β i)) → ∀ (x' : V ⊗[ℚ_[l]] P.R.BdR) (f : ↥(GK K) → V), (∀ g, f g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = ∑ i, β i g • x i + (actVdR (P.PD K) ρ g x' - x')) → Continuous f := by
  intro l _ P AI T K V _ _ _ _ _ ρ hρ k x β hβ x' f hf
  have hV : ∀ φ : V →ₗ[ℚ_[l]] ℚ_[l], Continuous φ := fun φ =>
    IsModuleTopology.continuous_of_linearMap φ
  have key : ∀ φ : V →ₗ[ℚ_[l]] ℚ_[l], Continuous fun g => φ (f g) := by
    intro φ
    let Φ : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] P.R.BdR :=
      (TensorProduct.lid ℚ_[l] P.R.BdR).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id
    have hΦ : ∀ v b, Φ (v ⊗ₜ b) = qB P (φ v) * b := by
      intro v b
      simp [Φ, Algebra.smul_def]
    have h1 : ∀ (y : V ⊗[ℚ_[l]] P.R.BdR) (i : Fin k), LatCont AI fun g => Φ (β i g • y) := by
      intro y i
      induction y using TensorProduct.induction_on with
      | zero => simpa using latCont_const AI 0
      | tmul v b =>
        simp only [TensorProduct.smul_tmul', hΦ]
        simpa using latCont_orbit AI T b ((hV φ).comp ((hβ i).smul continuous_const))
          (γ := fun _ => 1) continuous_const
      | add y y' ih ih' =>
        simp only [smul_add, map_add]
        exact ih.add AI ih'
    have h2 : ∀ y : V ⊗[ℚ_[l]] P.R.BdR, LatCont AI fun g => Φ (actVdR (P.PD K) ρ g y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simpa using latCont_const AI 0
      | tmul v b =>
        have e : ∀ g : ↥(GK K), Φ (actVdR (P.PD K) ρ g (v ⊗ₜ b)) =
            qB P (φ (ρ g v)) * P.actQdR (g : GQ l) b := by
          intro g
          rw [← P.PD_actdR K g b, ← hΦ]
          rfl
        simp only [e]
        exact latCont_orbit AI T b ((hV φ).comp (hρ v)) continuous_subtype_val
      | add y y' ih ih' =>
        simp only [map_add]
        exact ih.add AI ih'
    apply continuous_of_latCont AI T
    have e : ∀ g, qB P (φ (f g)) =
        ∑ i, Φ (β i g • x i) + (Φ (actVdR (P.PD K) ρ g x') + -Φ x') := by
      intro g
      have := congrArg Φ (hf g)
      rwa [hΦ, mul_one, map_add, map_sum, map_sub, sub_eq_add_neg] at this
    simp only [e]
    exact (LatCont.sum AI _ _ fun i => h1 (x i) i).add AI ((h2 x').add AI (latCont_const AI _))
  let b := Module.finBasis ℚ_[l] V
  have : f = fun g => ∑ j, b.coord j (f g) • b j := by
    funext g
    simp [b.sum_repr]
  rw [this]
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  haveI : ContinuousSMul ℚ_[l] V := IsModuleTopology.toContinuousSMul ℚ_[l] V
  exact continuous_finset_sum _ fun j _ => (key (b.coord j)).smul continuous_const

end GlobalTheory.ContDR

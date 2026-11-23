import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusLatticeDegreeMulP
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LinearIndependentMapVec
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubDegreeMonoInjectiveHomStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubDegreeBotAndMaxExistsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactSubDegreeBoundStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DotDualSubDegreeAnnihilatorStatement

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.FrobEst

def dotOrth {K : Type} [Field K] {d : ℕ} (X : Submodule K (Fin d → K)) :
    Submodule K (Fin d → K) where
  carrier := {u | ∀ φ ∈ X, u ⬝ᵥ φ = 0}
  add_mem' := fun {a b} ha hb φ hφ => by rw [add_dotProduct, ha φ hφ, hb φ hφ, add_zero]
  zero_mem' := fun φ _ => zero_dotProduct φ
  smul_mem' := fun c u hu φ hφ => by rw [smul_dotProduct, hu φ hφ, smul_zero]

theorem frob_estimate : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]
    (O : Type) [CommRing O] [StarRing O] (d : ℕ) (D : ConjData C p O d), 2 < p →
    0 ≤ deg C (dotDual C D.lie) ∧
      ∀ W : Submodule K (Fin d → K),
        ((p : ℤ) - 2) * subDeg C D.lie W ≤ deg C (dotDual C D.lie) := by
  intro K _ C p _ _ O _ _ d D hp
  obtain ⟨h0, W₀, hW₀⟩ := GlobalTheory.T.sub_degree_bot_and_max_exists K C (Fin d → K) D.lie D.lie_bun
  have hp2 : (0 : ℤ) < (p : ℤ) - 2 := by
    have : (2 : ℤ) < (p : ℤ) := by exact_mod_cast hp
    linarith
  have hf := GlobalTheory.CompanionTheory.Ar.Crv.SubFrob.subDeg_frob K C p d D.lie W₀ D.lie_bun
  have h1 := GlobalTheory.T.sub_degree_mono_injective_hom K C (Fin d → K) ((Fin d → K) × (Fin d → K))
    (frobLat C p D.lie) D.H D.α (frobSub p W₀)
    (GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat K C p d D.lie D.lie_bun).1 D.H_bun D.conj.1
    (fun i x hx => (D.conj.2.2.2.1 i x).1 hx)
  have h2 := GlobalTheory.T.short_exact_sub_degree_bound K C (Fin d → K) ((Fin d → K) × (Fin d → K)) (Fin d → K)
    (dotDual C D.lie) D.H D.lie (LinearMap.inr K (Fin d → K) (Fin d → K))
    (LinearMap.fst K (Fin d → K) (Fin d → K)) (Submodule.map D.α (frobSub p W₀)) D.H_bun D.hodge
  have h3 := GlobalTheory.T.dot_dual_sub_degree_annihilator K C d D.lie
    (dotOrth (Submodule.comap (LinearMap.inr K (Fin d → K) (Fin d → K))
      (Submodule.map D.α (frobSub p W₀))))
    (Submodule.comap (LinearMap.inr K (Fin d → K) (Fin d → K))
      (Submodule.map D.α (frobSub p W₀))) D.lie_bun (fun u => Iff.rfl)
  have h4 := hW₀ (Submodule.map (LinearMap.fst K (Fin d → K) (Fin d → K))
    (Submodule.map D.α (frobSub p W₀)))
  have h5 := hW₀ (dotOrth (Submodule.comap (LinearMap.inr K (Fin d → K) (Fin d → K))
    (Submodule.map D.α (frobSub p W₀))))
  have hr : ((p : ℤ) - 2) * subDeg C D.lie W₀ = (p : ℤ) * subDeg C D.lie W₀ - 2 * subDeg C D.lie W₀ := by
    ring
  have key : ((p : ℤ) - 2) * subDeg C D.lie W₀ ≤ deg C (dotDual C D.lie) := by
    linarith
  have hμ : 0 ≤ subDeg C D.lie W₀ := by
    have := hW₀ ⊥
    linarith
  refine ⟨?_, fun W => ?_⟩
  · have := mul_nonneg hp2.le hμ
    linarith
  · have := mul_le_mul_of_nonneg_left (hW₀ W) hp2.le
    linarith

end GlobalTheory.CompanionTheory.Ar.Crv.FrobEst

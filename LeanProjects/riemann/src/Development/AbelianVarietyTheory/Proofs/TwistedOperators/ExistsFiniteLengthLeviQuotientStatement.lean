import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteLengthLeviQuotient
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RkSubSuccLe

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_length_levi_quotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (χ : GL (Fin n) k →* ℂˣ), IsOpen {g | χ g = 1} → ∀ (ρ t : ℕ) (h : ρ + t = m),
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
      (τ : Representation ℂ (GlobalTheory.SmGL.Levi k (GlobalTheory.SmGL.Two (Fin ρ) (Fin t))) W),
      GlobalTheory.PRep.IsSmooth τ ∧ GlobalTheory.SmGL.HasFiniteLength τ ∧
      ∃ f : GlobalTheory.SmGL.IndSpLower (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) τ →ₗ[ℂ] (Matrix (Fin n) (Fin m) k → ℂ),
        (∀ (g : GL (Fin m) k) (v : GlobalTheory.SmGL.IndSpLower (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) τ),
          f (GlobalTheory.SmGL.parIndLower (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) τ g v) -
              GlobalTheory.SplitWeil.om 1 g (1 : GL (Fin n) k) (f v) ∈
            GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m (ρ + 1)) ∧
        GlobalTheory.ThetaGLRank.rkSub k n m ρ ≤
          GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m (ρ + 1) ⊔ LinearMap.range f := by
  first | exact @GlobalTheory.ThetaGLCover.layer_cover | exact GlobalTheory.ThetaGLCover.layer_cover | (intros; apply GlobalTheory.ThetaGLCover.layer_cover <;> assumption)

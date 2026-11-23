import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeEqIffSameIntegralGLCoset
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackLattice_eq_iff_same_integralGL_coset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) → ∀ g g' : GLw n w, pullLat w B ψ g = pullLat w B ψ g' → g⁻¹ * g' ∈ GlobalTheory.LFun.KGL w n := by
  first | exact @GlobalTheory.KapOrb.PullInj.main | exact GlobalTheory.KapOrb.PullInj.main | (intros; apply GlobalTheory.KapOrb.PullInj.main <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_factorizable_restriction_finite : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl F)) (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w, w ∉ S → φ w = G.M'.vac w) →
    ∀ (m : ℕ) (f' : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ' : Fin m → ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ i w, φ' i w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ i w, w ∉ S → φ' i w = G.M'.vac w) →
    (∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), (∀ t : AF F, evI F t = 0 → (∀ w ∈ S, evFin F w t = 0) → t • u = 0) →
      ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → AF F) (borel _),
        @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        (@MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x =>
            (∑ i, pure (f' i) (φ' i)) x * starRingEnd ℂ (G.M'.co.rho B.ψ u (∑ i, pure (f' i) (φ' i)) x)) =
          @MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x => pure f φ x * starRingEnd ℂ (G.M'.co.rho B.ψ u (pure f φ) x)) →
    ∃ c : ℂ, ∑ i, pure (f' i) (φ' i) = c • pure f φ := by
  first | exact @GlobalTheory.SplitSvN.scalar_of_coeff | exact GlobalTheory.SplitSvN.scalar_of_coeff | (intros; apply GlobalTheory.SplitSvN.scalar_of_coeff <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDefiniteLieIndexIdealEqNormIdeal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmDefinite_lieIndex_ideal_eq_norm_ideal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∃ 𝔫 : Ideal (𝓞 E), 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {gP.det} ∧
      ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ →
          GlobalTheory.FlatCM.idx K p (FB.eigLat X.B.t.act τ) (GlobalTheory.FlatCM.subP FP FB MP τ) = 𝔫.map τ := by
  first | exact @GlobalTheory.FlatCM.IdealZero.idealSt_zero | exact GlobalTheory.FlatCM.IdealZero.idealSt_zero | (intros; apply GlobalTheory.FlatCM.IdealZero.idealSt_zero <;> assumption)

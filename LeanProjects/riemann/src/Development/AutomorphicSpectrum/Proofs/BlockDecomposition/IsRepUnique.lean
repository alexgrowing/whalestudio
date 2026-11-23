import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerToL

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp.RepUnique

theorem isRep_unique : ∀ {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b b' : Mat n → V) (y : Lp V 2 μ), ContinuousOn b (GLs n) → ContinuousOn b' (GLs n) → IsRep μ b y → IsRep μ b' y → ∀ x ∈ GLs n, b x = b' x := by
  intro n _ _ μ _ V _ _ b b' y hb hb' h h' x hx
  have hv : ∀ g : G n, g.val ∈ GLs n := fun g =>
    ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  have c1 : Continuous fun g : G n => b g.val := hb.comp_continuous Units.continuous_val hv
  have c2 : Continuous fun g : G n => b' g.val := hb'.comp_continuous Units.continuous_val hv
  have e : (fun g : G n => b g.val) =ᵐ[μ] fun g => b' g.val := h.symm.trans h'
  have hfun := (Continuous.ae_eq_iff_eq μ c1 c2).1 e
  exact congrFun hfun (Matrix.GeneralLinearGroup.mkOfDetNeZero x hx)

end GlobalTheory.CompanionTheory.WaveCp.RepUnique

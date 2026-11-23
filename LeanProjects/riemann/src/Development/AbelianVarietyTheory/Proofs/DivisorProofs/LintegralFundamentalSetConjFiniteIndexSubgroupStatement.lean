import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalSetConjFiniteIndexSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_fundamentalSet_conj_finiteIndex_subgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (hΨ : X'.Ψ = X.Ψ) (δ : GL (Fin r) E) (x0 : Frame X.Ψ r) (x0' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))) (Φ : Frame X.Ψ r → ℝ≥0∞), X'.Gm = X.Gm → X'.p0 = X.p0 → (∀ v w, herm X.Gm ((δ : Matrix (Fin r) (Fin r) E).mulVec v) ((δ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X.Gm v w) → X'.Γ.map (MulAut.conj δ).toMonoidHom ≤ X.Γ → (X'.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ ≠ 0 → IsOrth X x0 → IsOrth X' x0' → IsFundSet X x0 FF → IsFundSet X' x0' FF' → Measurable Φ → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Φ (lact γ x) = Φ x) → (∀ b ∈ Bor X.Ψ r, ∀ x ∈ X.dom, Φ (rmul x b) = Φ x) → ∫⁻ z in FF', Φ (lact δ (hΨ ▸ cpt X' x0' z)) ∂(muF X' x0') = ((X'.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ : ℝ≥0∞) * ∫⁻ z in FF, Φ (cpt X x0 z) ∂(muF X x0) := by
  first | exact @GlobalTheory.SubgroupUnfold.lintegral_fundSet_conj_subgroup | exact GlobalTheory.SubgroupUnfold.lintegral_fundSet_conj_subgroup | (intros; apply GlobalTheory.SubgroupUnfold.lintegral_fundSet_conj_subgroup <;> assumption)

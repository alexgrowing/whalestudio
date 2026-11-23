import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicCuspFormAutomorphicBoundedSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.ReadProofs
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_cuspForm_automorphic_bounded_square_integrable : ∀ (D : D7) (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hD : Dom a n), ∀ f ∈ T.cuspA j a n, (∀ γ ∈ GQ (T.V j σ), ∀ g, T.phiJ j σ a f (γ * g) = T.phiJ j σ a f g) ∧ (∀ k ∈ T.Kf j σ, ∀ g, T.phiJ j σ a f (g * k) = T.mu j σ k * T.phiJ j σ a f g) ∧ Continuous (T.phiJ j σ a f) ∧ (∃ C : ℝ, ∀ g, ‖T.phiJ j σ a f g‖ ≤ C) ∧ MemLp (onQ (T.V j σ) (T.phiJ j σ a f)) 2 (muQ1 (T.V j σ)) := by
  first | exact @GlobalTheory.AdelicCusp.phiJ_automorphic | exact GlobalTheory.AdelicCusp.phiJ_automorphic | (intros; apply GlobalTheory.AdelicCusp.phiJ_automorphic <;> assumption)

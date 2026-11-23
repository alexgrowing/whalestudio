import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSectionFamilyNoCommonZeroLargeWeightStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvalAtNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanLeStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.SmallWtSpan

theorem holSub0_le_span_cuspSec : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ w : WeightFamilies.Wt D j, w.LastPos → 0 < w.n → holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n)}) := by
  intro D T hT j hj σ hσ w hw hn P hP
  have hdom := dom_wtA w
  obtain ⟨b, m, N, t, hbm, ht, hunit, hprod⟩ := GlobalTheory.T.exists_section_family_no_common_zero_large_weight D T hT j hj σ hσ _ _ hdom
  have hP' := Submodule.mem_inf.mp hP
  have h2 := GlobalTheory.GlueSpan.span_of_products D T hT j hj σ hσ _ b _ m N t hdom hbm ht hunit P hP'.2
    (fun i => hprod P hP i)
  exact GlobalTheory.T.holomorphic_sections_span_le D T hT j hj σ hσ w hw hn (Submodule.mem_inf.mpr ⟨hP, h2⟩)

end GlobalTheory.SmallWtSpan

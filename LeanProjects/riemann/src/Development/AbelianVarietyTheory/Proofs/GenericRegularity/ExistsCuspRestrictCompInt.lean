import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIdempotentWeightZeroSectionOfComponent
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IdemMulMemCusp
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHoldStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_cusp_restrict_comp_int : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (h : GenFrEx Xo c) (Z : Comp Xo c) a n, ∀ g ∈ Formalism.L2.PjFree.cusp Xo c U a n, ∃ g' ∈ Formalism.L2.PjFree.cusp Xo c U a n, evC h Z g' = evC h Z g ∧ (∀ Z', Z' ≠ Z → evC h Z' g' = 0) ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), evI y g' = evI y g ∨ evI y g' = 0 := by
  intro E _ _ _ H Dw l Xo c r U hU h Z a n g hg
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c
  obtain ⟨χ, hχ, hidem, h1, h0⟩ := exists_idem_section E H Dw l Xo c hL h (hA h) Z

  have hm : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (f f' : Rul Xo c),
      evR Xo c (f * f') y = evR Xo c f y * evR Xo c f' y := by
    intro S _ _ y f f'
    unfold evR
    exact evalAt_mul _ _ f f' y
  refine ⟨χ * g, GlobalTheory.Reg.IdemCusp.idem_mul_mem_cusp E H Dw l Xo c r U hU χ hχ hidem a n g hg, ?_, ?_, ?_⟩
  · unfold evC at h1 ⊢
    rw [hm, h1, one_mul]
  · intro Z' hZ'
    have h0' := h0 Z' hZ'
    unfold evC at h0' ⊢
    rw [hm, h0', zero_mul]
  · intro T io y
    letI := io.toAlgebra
    unfold evI

    have hy : IsIdempotentElem (evR Xo c χ y.1) := by
      unfold IsIdempotentElem
      rw [← hm, hidem]
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hy with h' | h'
    · right
      rw [hm, h', zero_mul]
    · left
      rw [hm, h', one_mul]

end GlobalTheory.Reg

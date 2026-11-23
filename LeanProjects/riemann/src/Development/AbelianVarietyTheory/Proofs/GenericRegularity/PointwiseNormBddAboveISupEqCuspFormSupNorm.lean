import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormSectionEqFlagDomainNormStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm.SupNorm

theorem bdd_and_iSup_eq {α β : Type} (g : α → ℝ) (h : β → ℝ) (C : ℝ) (hC : 0 ≤ C) (hh : ∀ b, 0 ≤ h b)
    (h1 : ∀ a, ∃ b, g a = C * h b) (h2 : ∀ b, ∃ a, g a = C * h b)
    (hfin : (⨆ b, ENNReal.ofReal (h b)) ≠ ⊤) :
    BddAbove (Set.range g) ∧ (⨆ a, g a) = C * (⨆ b, ENNReal.ofReal (h b)).toReal := by
  have hle : ∀ b, h b ≤ (⨆ b, ENNReal.ofReal (h b)).toReal := fun b =>
    (ENNReal.ofReal_le_iff_le_toReal hfin).1 (le_iSup (fun b => ENNReal.ofReal (h b)) b)
  have hr : Set.range g = Set.range fun b => C * h b := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := h1 a
      exact ⟨b, hb.symm⟩
    · rintro ⟨b, rfl⟩
      exact h2 b
  refine ⟨⟨C * (⨆ b, ENNReal.ofReal (h b)).toReal, ?_⟩, ?_⟩
  · rw [hr]
    rintro _ ⟨b, rfl⟩
    exact mul_le_mul_of_nonneg_left (hle b) hC
  · rw [ENNReal.toReal_iSup (fun b => ENNReal.ofReal_ne_top), Real.mul_iSup_of_nonneg hC]
    unfold iSup
    rw [hr]
    simp only [ENNReal.toReal_ofReal (hh _)]

theorem supBdd_and_supR_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ a n, Dom a n → ∀ f ∈ Formalism.L2.PjFree.cusp Xo c U a n, SupBdd Xo c fn a n f ∧ ∀ σ, supR Xo c fn σ a n f = Formalism.L2.PjFree.supC Xo c U xR (Formalism.L2.PjFree.goodOf c σ) a n f := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn hx hfn a n hd f hf
  obtain ⟨-, htie, hconj⟩ := GlobalTheory.T.pointwise_norm_section_eq_flagDomain_norm E H Dw l Xo c r U hU xR fn hx hfn
  have hs : f ∈ sec Xo c a n := Formalism.L2.PjFree.cusp_le_sec Xo c U a n hf
  have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  let N : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → ℝ := fun σ =>
    ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f
  have hgood : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ →
      BddAbove (Set.range (N σ)) ∧ (⨆ y, N σ y) = Formalism.L2.PjFree.supC Xo c U xR σ a n f := by
    intro σ hσ
    refine bdd_and_iSup_eq (N σ)
      (fun p : Formalism.L2.PjFree.FPt (U σ).X =>
        ((U σ).X p.1).pnorm (Formalism.L2.PjFree.laU (U σ) a n p.1) (Formalism.L2.PjFree.rdU (U σ) f p.1) p.2)
      (Formalism.L2.PjFree.lieFac Dw xR a) (Formalism.L2.PjFree.lieFac_pos Dw xR a).le
      (fun p => mul_nonneg (norm_nonneg _) (Formalism.L2.PjFree.pnorm_fac_nonneg _ _ _)) (fun y => ?_) (fun p => ?_)
      (Formalism.L2.PjFree.supE_cusp_ne_top hσ hf)
    · obtain ⟨k, x, t, ht⟩ := (hU σ hσ).2.2.1 y
      exact ⟨⟨k, x⟩, htie σ hσ k x t y ht a n hd f hs⟩
    · exact ⟨(U σ).un p.1 p.2, htie σ hσ p.1 p.2 1 _
        ((GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)).1 _) a n hd f hs⟩
  have hsub : ∀ σ τ : c.F →+* ℂ, τ = (starRingEnd ℂ).comp σ → Set.range (N σ) ⊆ Set.range (N τ) := by
    rintro σ τ rfl _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c _ _ (conjAlg σ) y
    exact ⟨z, hconj σ y z hz a n f hs⟩
  have hr : ∀ σ : c.F →+* ℂ, Set.range (N σ) = Set.range (N (Formalism.L2.PjFree.goodOf c σ)) := by
    intro σ
    by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
    · have e : Formalism.L2.PjFree.goodOf c σ = σ := if_pos hσ
      exact (hsub _ _ rfl).trans (hsub _ _ (by rw [e]; ext x; simp)) |>.antisymm
        ((hsub _ _ rfl).trans (hsub _ _ (by rw [e]; ext x; simp)))
    · have e : Formalism.L2.PjFree.goodOf c σ = (starRingEnd ℂ).comp σ := if_neg hσ
      exact (hsub _ _ e).antisymm (hsub _ _ (by rw [e]; ext x; simp))
  refine ⟨fun σ => ?_, fun σ => ?_⟩
  · show BddAbove (Set.range (N σ))
    rw [hr σ]
    exact (hgood _ (Formalism.L2.PjFree.goodEmb_goodOf c σ)).1
  · show sSup (Set.range (N σ)) = _
    rw [hr σ]
    exact (hgood _ (Formalism.L2.PjFree.goodEmb_goodOf c σ)).2

end GlobalTheory.FrameNorm.SupNorm

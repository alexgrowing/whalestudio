import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFiniteIntegralChartCoverFlagSpace
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormBoundGoodPointsExtendsAllPoints
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupSetFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralAdjoinOfForallCdvrStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralValuesEqualCharacteristicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralFlagChartEnlargeContainingValueStatement

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspReg

theorem exists_cover_noPole : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∃ (J : Type) (_ : Finite J) (P : J → GlobalTheory.Reg.PChart Xo c (algebraMap (la.valuation c.F).valuationSubring c.F)), GlobalTheory.Reg.Covers P ∧ ∀ j, evR Xo c f (P j).yg ∈ Algebra.adjoin c.F ((P j).gens : Set (P j).Ω) := by
  intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hg a n f hd hf
  obtain ⟨hE, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hF := cusp_le_sec Xo c U a n hf
  have hev := GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hF
  have hY : ∃ Y : Model Xo c (algebraMap (la.valuation c.F).valuationSubring c.F),
      PushInvertible Y.t.G Y.t.PP.L := by
    by_cases hr : 1 ≤ Dw.p + Dw.q
    · obtain ⟨Y, hP, -⟩ := GlobalTheory.GoodTransfer.exists_model hr Xo c la p hp hpl hg
      exact ⟨Y, hP⟩
    · exact GlobalTheory.SupFinite.exists_model_rank_zero (Xo := Xo) (c := c) (by omega) _
  obtain ⟨Y, hP⟩ := hY
  obtain ⟨J, hJ, P, hC⟩ := GlobalTheory.Reg.exists_finite_pchart_cover GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c
    hE.bc (la.valuation c.F).valuationSubring Y hP
  have hmem : ∀ j, ∀ e ∈ (P j).es, evR Xo c f (P j).yg ∈ (P j).R e := fun j e he => by
    rw [(hev _).1 _ ((P j).R e).val _ _ ((P j).gen e he)]
    exact (evR Xo c f ((P j).y e he)).2
  have hint : ∀ j, IsIntegral (Algebra.adjoin c.F ((P j).gens : Set (P j).Ω)) (evR Xo c f (P j).yg) := by
    intro j
    refine GlobalTheory.T.isIntegral_adjoin_of_forall_dvr_map_mem c.F (P j).Ω (P j).gens (P j).frac _ fun T hT φ hK hgn => ?_
    obtain ⟨e, he⟩ := (P j).es_ne
    let io : c.F →+* T.Fr := φ.comp (algebraMap c.F (P j).Ω)
    letI := io.toAlgebra
    let ψ : (P j).R e →ₐ[c.F] T.Fr :=
      { toRingHom := φ.comp ((P j).R e).val.toRingHom, commutes' := fun k => rfl }
    obtain ⟨z, hz⟩ := hE.bc _ _ ψ ((P j).y e he)
    have hzI := (P j).int e he T io ψ (fun a => hK _) (fun g hg' => hgn _ hg') z hz
    have h1 := GlobalTheory.T.cuspForm_integral_values_equal_characteristic E H Dw l Xo c r U hU a n f hd hf T hT io hK ⟨z, hE.test _ z, hzI⟩
    have e1 : evR Xo c f z = ψ (evR Xo c f ((P j).y e he)) := (hev _).1 _ ψ _ _ hz
    have e2 : evR Xo c f (P j).yg = ((P j).R e).val (evR Xo c f ((P j).y e he)) :=
      (hev _).1 _ ((P j).R e).val _ _ ((P j).gen e he)
    rw [e2]
    change evR Xo c f z ∈ _ at h1
    rw [e1] at h1
    exact h1
  choose P' hP'1 hP'2 using fun j => GlobalTheory.T.exists_integralFlagChart_enlarge_containing_value E H Dw l Xo c (la.valuation c.F).valuationSubring f (P j) (hmem j) (hint j)
  refine ⟨J, hJ, P', fun L _ _ W hW y => ?_, hP'1⟩
  obtain ⟨j, hj⟩ := hC L W hW y
  exact ⟨j, hP'2 j L W hW y hj⟩

end GlobalTheory.CuspReg

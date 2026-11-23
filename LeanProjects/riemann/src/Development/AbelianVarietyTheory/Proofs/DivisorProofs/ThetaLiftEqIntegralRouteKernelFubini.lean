import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelIntegrableOnUnitaryQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AestronglyMeasurableKernelRouteBigVertexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelRouteBigVertexRationalLeftInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthIntegralNormKernelBigVertexRouteStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigRoute

theorem lift_eq_integral_kerBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hA : TotConv W M _ Θ F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    (∀ᵐ g ∂(M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1))),
      IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1)))) ∧
    liftT W M (routeBig t i j) Θ F g₁ = ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid (i + 1) (j + 1)),
      kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1)) ∂M.ν (.grid i (j + 1)) := by
  intro D T L sc G hWC hK hP μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hA g₁
  classical
  have hσ : ∀ X : Node, X.InRange D.R.m → SigmaFinite (M.ν X) := fun X hX => by
    obtain ⟨h1, h2, -⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D (G.V X)
    haveI := (hM.vtx X hX).haar_fund.1
    infer_instance
  haveI := hσ (.grid i (j + 1)) ⟨i.2.le, j.2⟩
  haveI := hσ (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩
  have hK1 : ∀ g, IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1))) := GlobalTheory.T.bigRoute_kernel_integrableOn_unitary_quotient hWC hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  have hmeas : AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
      kerBig W Θ p.1 g₁ p.2) (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod
        ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := GlobalTheory.T.aestronglyMeasurable_kernel_route_big_vertex hL W B ρ t i j M hM Θ Θ' hΘ g₁
  have hinv : ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g, kerBig W Θ (γ * g) g₁ = kerBig W Θ g g₁ := GlobalTheory.T.kernel_route_big_vertex_rational_left_invariant hL W B ρ t i j Θ Θ' hΘ g₁
  have hgrow : GlobalTheory.Grow.ModGrowth (G.V (.grid i (j + 1))) (fun g => ∫ u in M.fd (.grid (i + 1) (j + 1)),
      ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1))) := GlobalTheory.T.moderateGrowth_integral_norm_kernel_bigVertexRoute hWC hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  have hRD : GlobalTheory.Grow.RapidDec _ F := GlobalTheory.Grow.rapidDec_of_cuspForm (GlobalTheory.Grow.cuspRapidDecay_of_bound hP) W.θ_is hF hFc
  obtain ⟨hH, hfd⟩ := (hM.vtx (.grid i (j + 1)) ⟨i.2.le, j.2⟩).haar_fund
  have hkm : AEStronglyMeasurable (fun g => ((∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖
      ∂M.ν (.grid (i + 1) (j + 1)) : ℝ) : ℂ)) ((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hmeas.norm.integral_prod_right'
  obtain ⟨C, A, hCA⟩ := hgrow
  have hkb : ∀ g, ‖((∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1)) : ℝ) : ℂ)‖ ≤
      C * 2 ^ A * GlobalTheory.Grow.quotHeight _ g ^ A := fun g => by
    rw [Complex.norm_real]
    exact GlobalTheory.Grow.norm_le_quotHeight_pow (fun γ hγ g => by simp only [hinv γ hγ g]) hCA g
  have hkF := hRD.integrableOn_mul_of_le hH hfd hkm hkb
  have hJ : Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) => F p.1 * kerBig W Θ p.1 g₁ p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod
        ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := by
    have hFm : AEStronglyMeasurable F ((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))) :=
      hRD.continuous.aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
        F p.1 * kerBig W Θ p.1 g₁ p.2) (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod
          ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) :=
      hFm.comp_fst.mul hmeas
    refine (integrable_prod_iff hm2).2
      ⟨.of_forall fun g => (hK1 g).const_mul (F g), ?_⟩
    refine hkF.norm.congr (.of_forall fun g => ?_)
    simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, integral_const_mul]
    rw [abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), mul_comm]
  refine ⟨Filter.Eventually.of_forall hK1, ?_⟩
  have hpt : ∀ u, ∫ g in M.fd (.grid i (j + 1)), F g * kerBig W Θ g g₁ u ∂M.ν (.grid i (j + 1)) =
      Θ.sum fun d c => c * (W.kerA (.down t (i + 1) j) d.2 u g₁ *
        ∫ g in M.fd (.grid i (j + 1)), W.kerA (.right i (j + 1)) d.1.2 g u * F g ∂M.ν (.grid i (j + 1))) := by
    intro u
    have hint : ∀ d ∈ Θ.support, IntegrableOn (fun g => W.kerA (.right i (j + 1)) d.1.2 g u * F g)
        (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1))) := fun d hd => (hA d hd).1.2 u
    have e : ∀ g, F g * kerBig W Θ g g₁ u = ∑ d ∈ Θ.support,
        Θ d * (W.kerA (.down t (i + 1) j) d.2 u g₁ * (W.kerA (.right i (j + 1)) d.1.2 g u * F g)) := by
      intro g
      simp only [kerBig, Finsupp.sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    simp_rw [e]
    rw [integral_finset_sum _ fun d hd => ((hint d hd).const_mul _).const_mul _]
    simp only [integral_const_mul, Finsupp.sum]
  have hint2 : ∀ d ∈ Θ.support, Integrable (fun u => W.kerA (.down t (i + 1) j) d.2 u g₁ *
        ∫ g in M.fd (.grid i (j + 1)), W.kerA (.right i (j + 1)) d.1.2 g u * F g ∂M.ν (.grid i (j + 1)))
      ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1)))) := fun d hd => (hA d hd).2 g₁
  symm
  calc ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid (i + 1) (j + 1)), kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1))
        ∂M.ν (.grid i (j + 1))
      = ∫ g in M.fd (.grid i (j + 1)), ∫ u in M.fd (.grid (i + 1) (j + 1)), F g * kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1))
        ∂M.ν (.grid i (j + 1)) := by simp_rw [integral_const_mul]
    _ = ∫ u in M.fd (.grid (i + 1) (j + 1)), ∫ g in M.fd (.grid i (j + 1)), F g * kerBig W Θ g g₁ u
        ∂M.ν (.grid i (j + 1)) ∂M.ν (.grid (i + 1) (j + 1)) := integral_integral_swap hJ
    _ = ∫ u in M.fd (.grid (i + 1) (j + 1)), (Θ.sum fun d c => c * (W.kerA (.down t (i + 1) j) d.2 u g₁ *
        ∫ g in M.fd (.grid i (j + 1)), W.kerA (.right i (j + 1)) d.1.2 g u * F g ∂M.ν (.grid i (j + 1))))
        ∂M.ν (.grid (i + 1) (j + 1)) := by
        simp_rw [hpt]
    _ = _ := by
        simp only [Finsupp.sum]
        rw [integral_finset_sum _ fun d hd => (hint2 d hd).const_mul _]
        simp_rw [integral_const_mul]
        simp only [liftT, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rfl

end GlobalTheory.BigRoute

end

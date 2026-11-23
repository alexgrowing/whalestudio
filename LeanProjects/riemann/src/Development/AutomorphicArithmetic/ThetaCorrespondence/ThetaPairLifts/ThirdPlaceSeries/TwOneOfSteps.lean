import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistOfDiscreteSeries
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjTwOfOne
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatSmallGenStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TupAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FixAtHoldsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoefAtOfTwAdmStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjExpansionRationalStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TwConj
open GlobalTheory.ConjTwist
theorem normAt_alt : _root_.GlobalTheory.BigOn.Exp.TwConj.NormCondition := _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun _ _ _ _ p _ _ _ _ _ B ν ν' ⟨_, c, hc, n, hn, hνn⟩ ⟨_, c', hc', m, hm, hνm⟩ => by
  obtain ⟨k, hk, hkk⟩ := scale_pow_eq p.R p.v₀ B hc hc'
  refine ⟨n * m * k, Nat.mul_ne_zero (Nat.mul_ne_zero hn hm) hk, ?_⟩
  have e1 : ν' ^ (n * m * k) = (ν' ^ m) ^ (n * k) := by rw [← pow_mul]; ring_nf
  have e2 : ν ^ (n * m * k) = (ν ^ n) ^ (m * k) := by rw [← pow_mul]; ring_nf
  have e3 : c' ^ (n * m * k) = c ^ (n * m * k) := by
    rw [show n * m * k = k * (n * m) by ring, pow_mul c', pow_mul c, hkk]
  rw [e1, e2, hνm, hνn, ← pow_mul, ← pow_mul, mul_pow, mul_pow,
    show m * (n * k) = n * m * k by ring, show n * (m * k) = n * m * k by ring, e3]
theorem twOne_of_steps_alt (hA : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt) (hT : _root_.GlobalTheory.BigOn.Exp.TwConj.TupleCondition) (hF : _root_.GlobalTheory.BigOn.Exp.TwConj.FixedPointCondition) (hC : _root_.GlobalTheory.BigOn.Exp.TwConj.CoefficientCondition)
    (hE : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p _ j => ∀ τ : ℂ ≃+* ℂ,
      (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
      ∀ Φ Φ' : GA (Fm.D x i) (Wc (Fm.D x i) j) → ℂ, ConjFun (p.O j) (p.κ j) τ 1 Φ Φ' →
        ∃ (n : ℕ) (b : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
          Φ = ∑ k, b k • evW p.nexp p.v₀ j (g k).val ∧ ∑ k, τ (b k) • evW p.nexp p.v₀ j (g k).val = Φ') : _root_.GlobalTheory.BigOn.Exp.TwConj.TwistTrivialCondition := by
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hA hT) (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hF (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hC hE))) fun Fm x hx i p hr hm w _ j H => ?_
  obtain ⟨⟨a1, a2⟩, a3, a4, a5⟩ := H
  intro ρ ρ' ν hρ hρ' hp hS hL hAd hN h₀ P hP h hh τ hτ hcc
  obtain ⟨c, u, ξ, hc, hu, hξ, K⟩ := a4 ρ ν hρ hp hN
  obtain ⟨y, hy, hyy⟩ := K h₀ P hP
  obtain ⟨f1, f2⟩ := a3 ρ hρ hp hL τ hτ
  obtain ⟨g1, g2, -⟩ := GlobalTheory.TwistGood.tw_good _ _ _ ρ hρ _ j ((Fm.ex x hx i).nch.sd w) _ _ _ a1.1
  obtain ⟨g3, -, -⟩ := GlobalTheory.TwistGood.tw_good _ _ _ ρ' hρ' _ j ((Fm.ex x hx i).nch.sd w) _ _ _ a1.1
  obtain ⟨ζ, hζ, hcf⟩ := conjFun_gen (Fm.parT x hx i).nV_ge (a2 ρ ρ' hρ hρ' hp hS hAd) (hρ.base _ _ _) (hρ.weil_base _ _ _) g1 g3 g2
    (hcc.1.symm ▸ g2) (root_delta hρ _ _ _) (root_charOf _ _ a1.1.2.2.1) hc hu f1 f2 hcc hh (hyy τ hτ)
  have hcf1 := (GlobalTheory.ConjClassSum.conjFun_iff _ _ _ _ _ _).2
    (GlobalTheory.ConjGen.cf_one_of (root_ne hζ) ((GlobalTheory.ConjClassSum.conjFun_iff _ _ _ _ _ _).1 hcf))
  obtain ⟨n, b, g, e1, e2⟩ := a5 τ hτ _ _ hcf1
  have hsm : ∀ ψ, ν • genW (Fm.ex x hx i) w j ρ ψ h P =
      ξ • phs p j • genW (Fm.ex x hx i) w j ρ ψ h (p.R.ioP j (PiTensorProduct.tprod ℂ u) (c y)) := fun ψ =>
    smul_apply_of _ hy
  exact ⟨_, root_mul (root_mul (root_map τ hξ) (root_inv hζ)) (root_inv hξ), n, fun l => ξ * b l, g,
    rescale τ (root_ne hξ) (hsm _) (hsm _) e1 e2⟩
theorem conj_tw_of_prints : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.SerStd.SeriesRatS →
    _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.ConjugateTwist := fun h1 h2 h3 hD hW h4 hA hC =>
  _root_.GlobalTheory.BigOn.Exp.TwConj.conjTw_of_twAdm_latSmallGen_normAt_twOne hA _root_.GlobalTheory.T.latSmallGen' _root_.GlobalTheory.BigOn.Exp.TwConj.normAt_alt (_root_.GlobalTheory.BigOn.Exp.TwConj.twOne_of_steps_alt hA (_root_.GlobalTheory.T.twisted_conj_tuple_at' h1 h2 h3 hD hW hA hC) (_root_.GlobalTheory.T.twisted_conj_fix_at' h3 hA) (_root_.GlobalTheory.T.twisted_conj_coef_at' hA)
    (_root_.GlobalTheory.T.conjTwist_function_eq_sum_evaluations_alt h1 h2 h3 h4))
end GlobalTheory.BigOn.Exp.TwConj
end
end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetFockVacuumDatumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeLawsThetaHeisenbergStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarisationTwistLatticeSelfDualSameStabilisersStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomOntoModuloDepthIdealStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainRealParametersCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeChangeOfLatticeLawsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSupportedCoefficientCongruenceSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate

namespace GlobalTheory.CoreOnto.PreSteps

theorem preOK (hDF : DepFixed) : PreOK := by
  intro D hQ hS T L μ0 hL sc hc G W Mv hM i hi r r' hr hr' v M M'
  obtain ⟨hth, -, -, hbij, hmeas, hweil⟩ := GlobalTheory.T.adjointExchange_laws_thetaHeisenberg D W.ψ (G.V (.core i)) (G.V (.core (i + 1))) W.ψ_std
  have hom := W.om_is (.core i) (show i + 1 ≤ D.R.m by omega)
  obtain ⟨hcS, hcT⟩ := G.chr_core (i := i) (by omega)
  rw [hcS, hcT] at hom
  obtain ⟨ω, hω, hωx⟩ := hweil _ _ _ hom
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.exists_latticeHom_onto_modulo_depthIdeal D hQ T L μ0 hL sc G W Mv hM i hi
  obtain ⟨f, hvac, hsph, hcos⟩ := GlobalTheory.T.exists_cosetFockVacuumDatum D hQ T L μ0 hL sc G W Mv hM i hi r r' hr hr' _ _ (r.mod M) (r'.mod M') x₀ hx₀.1
  have hRL := (GlobalTheory.T.selfDualLattice_changeOfLattice_laws D).2.2 W.ψ (G.V (.core i)) (G.V (.core (i + 1))) r r'
  have hinj : Function.Injective (exch (G.V (.core i)) (G.V (.core (i + 1)))) := by
    intro F₁ F₂ h
    funext w
    obtain ⟨x, rfl⟩ := hbij.2 w
    exact congrFun h x
  refine ⟨ω, f, ⟨(hRL.2 _ _ ω).2 hω, fun τ => ?_, hvac, hsph, ?_, ?_⟩, hωx, fun φ => (hcos φ).1⟩
  · show GlobalTheory.EvenOnto.UpPair (sLen D - 1) (Node.par D sc.cGap (.core i) τ) (Node.par D sc.cGap (.core (i + 1)) τ)
      (-(cen D sc.cGap τ (D.R.m - i) : ℚ)) (-(cen D sc.cGap τ (D.R.m - i) : ℚ))
    rw [hc]
    exact GlobalTheory.T.coreChain_realParameters_correspond D hS i hi τ
  · intro φ κ hκ κ' hκ'
    have hD := (hcos φ).1
    have hthF := (hth _).2 hD.1
    exact hinj ((hωx _ hthF κ κ').symm.trans (hDF D hQ T L μ0 hL sc G W Mv hM i hi (.core i) (Or.inr rfl) _ hD κ hκ κ' hκ'))
  · intro m X hX φ g hg hgb
    by_contra hne
    apply hgb
    have hD := (hcos φ).1
    have hthF := (hth _).2 hD.1
    obtain ⟨m', X', hX', heq⟩ := hmeas m X hX
    have hne' : (∫ w in X', W.om (.core i) (1, g) (exch (G.V (.core i)) (G.V (.core (i + 1)))
        (GlobalTheory.Chain.ptOf (V := r.sp) (W := r'.sp) W.ψ W.θ (r.mod M) (r'.mod M') f φ)) w *
        conj (exch (G.V (.core i)) (G.V (.core (i + 1)))
          (GlobalTheory.Chain.ptOf (V := r.sp) (W := r'.sp) W.ψ W.θ (r.mod M) (r'.mod M') f φ) w) ∂m') ≠ 0 := by
      have h1 := hωx _ hthF g 1
      rw [map_one] at h1
      rw [h1, ← heq]
      exact hne
    have hsd := (G.sp.P_is i (by omega)).sd
    have hstab : ∀ w ∉ G.pl.S0, GlobalTheory.AdelicU.proj D.sp.cm.sig (G.V (.core i)).gram w g ∈
        GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (G.V (.core i)).gram (G.Λ (.core i)) w := by
      intro w hw
      have h0 := hg w hw
      have h1 : GlobalTheory.AdelicU.proj D.sp.cm.sig (G.V (.core i)).gram w g ∈
          GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (G.V (.core i)).gram (GlobalTheory.AdelicU.frameLat r.sp) w := h0
      have hΛ : GlobalTheory.AdelicU.frameLat r.sp = scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) (G.Λ (.core i)) := hr
      rw [hΛ, (GlobalTheory.T.polarisationTwist_lattice_selfDual_same_stabilisers D (G.V (.core i)) (G.Λ (.core i)) hsd i).2.1 w] at h1
      exact h1
    have hfin := GlobalTheory.T.cosetSupported_coefficient_congruenceSubgroup D hQ T L μ0 hL sc G W Mv hM i hi x₀ hx₀ _ (hcos φ) m' X' hX' g hstab hne'
    obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (G.V (.core i))).1 g
    refine ⟨⟨a, ha⟩, k, Subgroup.mem_inf.2 ⟨hk, ?_⟩, rfl⟩
    have ha' : Lev.finE (G.V (.core i)) a = 1 := by
      have h : finHom (G.V (.core i)) a = 1 := ha
      show Formalism.UG.bc (Lev.swapAE D) (finHom (G.V (.core i)) a) = 1
      rw [h, map_one]
    show Lev.finE (G.V (.core i)) k ∈ G.levCong (.core i)
    rw [map_mul, ha', one_mul] at hfin
    exact hfin

end GlobalTheory.CoreOnto.PreSteps

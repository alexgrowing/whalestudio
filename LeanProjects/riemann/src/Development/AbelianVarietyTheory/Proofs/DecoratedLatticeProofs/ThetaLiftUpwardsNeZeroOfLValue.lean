import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageRealDataConjValueMemCuspFormsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffSStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqSetIntegralFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageWittIndexLtAndPlacesTwoSplitStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightFunPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialNormalizingFactorProductAnalyticNeZeroStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PeterssonLiftSmulMeasure
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem sphFun_of_isParamFun : ∀ (D : D7) (V : HSp D) (Λ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Lat V) (Sf : Finset (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D)) (f : GA D V → ℂ)
    (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.LFun.IsParamFun D.sp.cm.sig V.gram Λ (Sf : Set (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D)) f B →
    GlobalTheory.Core.Rk.IP.SphFun V Λ Sf f := by
  intro D V Λ Sf f B hf v hv k hk g
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hx := (hf v (by simpa using hv) w hw).mem_fixed
  have := congrFun (hx ⟨k, hk⟩) g
  simpa [GlobalTheory.PRep.rightReg, LinearMap.funLeft] using this

theorem upNe_of_heckeForm : ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → MetEx D → LevFacts D → ZetaNe D → UpNe D := by
  intro D hHF _ _ hZ hgap c hc k hk s s' hs hs' p hp u B hB hL
  obtain ⟨mX, hmX⟩ : ∃ mX : Measure (WO s.V s'.V) × Set (WO s.V s'.V), IsCovolOne (ratL s'.V s.V) mX.1 mX.2 := by
    obtain ⟨ξ, f₀, hv⟩ := hp.vec
    exact hv.1.2.norm.1
  obtain ⟨φ, v, hvK, hZ'⟩ := hZ hgap c hc k hk s s' hs hs' p hp mX.1 mX.2 hmX
  refine ⟨φ, v, hvK, ?_⟩
  obtain ⟨hu0, hpar⟩ := hB
  obtain ⟨hI, hInt⟩ := hZ' u hu0
  have hF : PiLocalization₂.val u v ≠ 0 := by
    intro h0
    apply hI
    have : ∀ g, p.zint mX.1 mX.2 φ (PiLocalization₂.val u v) g = 0 := by
      intro g; simp [Step.zint, h0, PiLocalization₂.pet, Lift.pet, rTr]
    simp [this]
  have hparF := hpar v hF
  obtain ⟨cA, a, hcA, hcart, hJ, hmaj, hmaj_eq, hA0⟩ := GlobalTheory.T.thetaChainStage_realData_conj_value_mem_cuspForms D c hc k hk.le s hs
  obtain ⟨-, -, -, hcartB, -, -, -, -⟩ := GlobalTheory.T.thetaChainStage_realData_conj_value_mem_cuspForms D c hc (k + 1) hk s' hs'
  have hu1 : (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := hA0 u v hvK
  obtain ⟨hwitt, htwo⟩ := GlobalTheory.T.thetaChainStage_wittIndex_lt_and_places_two_split D c (k + 1) s' hk hs'
  obtain ⟨hfock, -, hunrT⟩ := GlobalTheory.T.thetaChainStep_fockVector_sphericalOffS D hgap c hc k hk s s' hs hs' p hp
  obtain ⟨-, -, hoff⟩ := GlobalTheory.T.doubledLatticeHeightFun_properties D s.V s.Λ a hs.selfDual hmaj
  have hmeas : MeasurableSet (intOff c s) := (hoff c.S).1.measurableSet
  have hr1 : 1 ≤ s.V.rank := by
    rw [hs.rank]; simp only [Ranks.rankY, Ranks.r]; have := D.R.two_le_m; omega
  have ht1 : 1 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
  have hrk : s'.V.rank = s.V.rank + D.R.t := by rw [hs'.rank, hs.rank]; simp only [Ranks.rankY]; ring
  have hPair : GlobalTheory.Core.Rk.IP.Pair c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) (cart s.M) (cart s'.M) D.R.t cA a p.ω
      mX.1 mX.2 :=
    { setting := ⟨hr1, ht1, hrk, hc.inf, hs.sigOK, hcA, hcart, hcartB, hJ⟩
      maj := hmaj
      maj_eq := hmaj_eq
      weil := hp.weil
      covol := hmX }
  have hUnr : GlobalTheory.Core.Rk.IP.Unram c.ψ s.V s'.V (c.chT (k + 1)) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) :=
    ⟨hs.selfDual, hs'.selfDual, fun w _ h2 => htwo w h2, hunrT, (hfock φ).2, (hfock φ).2⟩
  have hsph := sphFun_of_isParamFun D s.V s.Λ c.S _ B hparF
  set F := PiLocalization₂.val u v with hFdef
  have hAut : Formalism.L2.Theta.IsAutFunSm c.θ s.V (fun g => conj (F g)) := hu1.1.1
  have hFl : ∀ γ ∈ GQ s.V, ∀ g, F (γ * g) = F g := fun γ hγ g => by
    simpa using congrArg (starRingEnd ℂ) (hAut.left γ hγ g)
  have hFc : Continuous F := by simpa using hAut.cont.star
  have hΦ : IsThetaFunO c.ψ s.V s'.V (p.pt φ) := (hfock φ).1.1
  have hθl : ∀ h, ∀ γ ∈ GQ s.V, ∀ g, thetaKO p.ω (γ * g) h (p.pt φ) = thetaKO p.ω g h (p.pt φ) := by
    intro h γ hγ g
    have e : ((γ * g, h) : GA D s.V × GA D s'.V) = (γ, 1) * (g, h) := by simp
    simp only [thetaKO, e, map_mul, Module.End.mul_apply]
    exact hp.weil.om_aut γ hγ 1 (one_mem _) _ (hp.weil.om_pres _ _ hΦ)
  have hθc : ∀ h, Continuous fun g => thetaKO p.ω g h (p.pt φ) := fun h =>
    (hp.weil.om_cont _ hΦ 0).comp (continuous_id.prodMk continuous_const)
  have hrc : ∀ g, GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F x)) (fun x => conj (F x)) g = conj (s.pet (rTr s.V g F) F) := by
    intro g
    have := GlobalTheory.T.integral_quotient_eq_setIntegral_fundamentalDomain D s.V s.ν s.fd hs.haar hs.fund (fun x => conj (F (x * g)) * conj (conj (F x)))
      (fun γ hγ x => by simp only [mul_assoc, hFl γ hγ]) (by fun_prop)
    simp only [GlobalTheory.Core.Rk.IP.rcoef, PiLocalization₂.pet, Lift.pet, rTr]
    rw [← integral_conj]
    simp only [map_mul]
    exact this
  have hup : ∀ h, GlobalTheory.Core.Rk.IP.up p.ω s.ν (p.pt φ) (fun x => conj (F x)) h = conj (p.up φ F h) := by
    intro h
    have := GlobalTheory.T.integral_quotient_eq_setIntegral_fundamentalDomain D s.V s.ν s.fd hs.haar hs.fund (fun g => thetaKO p.ω g h (p.pt φ) * conj (F g))
      (fun γ hγ x => by simp only [hθl h γ hγ, hFl γ hγ]) (by have := hθc h; fun_prop)
    simp only [GlobalTheory.Core.Rk.IP.up, Step.up]
    rw [← integral_conj]
    simp only [map_mul, Complex.conj_conj]
    exact this
  have hsZ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V = (D.R.t : ℂ) / 2 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, hrk]; push_cast; ring
  have hwz : ∀ g, GlobalTheory.Core.Rk.IP.wcoef p.ω mX.1 mX.2 (p.pt φ) (p.pt φ) g *
      GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F x)) (fun x => conj (F x)) g = p.zint mX.1 mX.2 φ F g := by
    intro g; simp only [Step.zint, hrc]; rfl
  have hint : ∃ s₁ : ℝ, s₁ < (D.R.t : ℝ) / 2 ∧ IntegrableOn (GlobalTheory.Core.Rk.IP.integrand p.ω s.ν mX.1 mX.2 s.Λ a (p.pt φ)
      (p.pt φ) (fun x => conj (F x)) (fun x => conj (F x)) s₁) (GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S) s.ν := by
    obtain ⟨s₁, hs₁, hi⟩ := hInt a hmaj hmaj_eq
    refine ⟨s₁, hs₁, hi.congr_fun (fun g hg => ?_) hmeas⟩
    simp only [GlobalTheory.Core.Rk.IP.integrand, GlobalTheory.Doubling.npow, (hoff c.S).2 g hg, hsZ, hrc]
    simp only [Step.zint, coefW, GlobalTheory.Core.Rk.IP.wcoef, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, hgtS]
    ring
  obtain ⟨-, -, -, hval⟩ := hHF c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) (cart s.M) (cart s'.M) D.R.t cA a p.ω
    mX.1 mX.2 hPair (Or.inr hwitt) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) (hfock φ).1 (hfock φ).1 hUnr s.ν s'.ν hs.haar hs'.haar
    _ hu1 _ hu1 B hparF hsph hint
  obtain ⟨l, hl0, hlv⟩ := hL
  have key := hval l hlv
  intro hup0
  have hz : GlobalTheory.Core.Rk.IP.up p.ω s.ν (p.pt φ) (fun x => conj (F x)) = 0 := by
    funext h; rw [hup, hup0]; simp
  rw [hz] at key
  have hlhs : GlobalTheory.Cusp.petersson s'.V s'.ν (0 : GA D s'.V → ℂ) 0 = 0 := by
    simp [GlobalTheory.Cusp.petersson, GlobalTheory.AutomorphicL2Unitary.pet, GlobalTheory.AutomorphicL2Unitary.descend]
  rw [hlhs] at key
  have hvol : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν := by
    have := hs'.haar; exact GlobalTheory.RallisIP.Model.vol_pos s'.ν
  have hd : GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E (c.S : Set (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D)) s.V.rank s'.V.rank
      ((D.R.t : ℂ) / 2) ≠ 0 := by
    refine ((GlobalTheory.T.partialNormalizingFactorProduct_analytic_ne_zero D _ _ _).2 _ ?_).1
    simp only [Complex.div_ofNat_re, Complex.natCast_re]; positivity
  have hI' : ∫ g in GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S, GlobalTheory.Core.Rk.IP.wcoef p.ω mX.1 mX.2 (p.pt φ) (p.pt φ) g *
      GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F x)) (fun x => conj (F x)) g ∂s.ν ≠ 0 := by
    simp only [hwz]; exact hI
  have hvolC : ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hvol.ne'
  exact hI' (by
    have := key.symm
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hvolC
      · exact absurd h (div_ne_zero hl0 hd)
    · exact h)

end GlobalTheory.ChainOnto

end

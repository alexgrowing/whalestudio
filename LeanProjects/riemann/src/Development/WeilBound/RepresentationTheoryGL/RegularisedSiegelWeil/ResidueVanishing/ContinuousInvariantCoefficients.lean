import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.Leaves
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilDoubledSpaceOfStandardUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymmStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartSiegelLeviDetEqStatement
noncomputable section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.StdUnn PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace PositivityTheory.Rg.Rsw.Kplug

set_option maxHeartbeats 1000000 in
theorem continuation_through_chart : ContinuationThroughChart := by
  intro D ψ A B χ omh hW ν 𝓨 hν θ hθ μ hμ κ hκ omS hT lam hlam a ha p hp f hf hK Φ hΦ U d E hU hR hs hd hhol hc hi he
  obtain ⟨h0, hflat, hact⟩ := GlobalTheory.T.doubledFlatSection_eq_translate_standardSection D ψ A B χ omh hW ν 𝓨 hν θ hθ μ hμ κ hκ omS hT lam hlam a p f hf Φ hΦ
  have hIw := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  have hmem := GlobalTheory.SwSecMem.swSec_mem_degPS GlobalTheory.weilRepresentationUnitaryPair D ψ A B χ omh hW ν 𝓨 hν f hf a hK
  have hχ := GlobalTheory.T.isHeckeChar_restrictionEta_inv D χ B.rank hW.hecT hW.resT
  have hP' := GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D A μ hμ κ hκ
  have hG' := GlobalTheory.T.standardUnitaryChart_mem_rational_iff D A μ hμ κ hκ
  obtain ⟨hκc, hκc'⟩ := GlobalTheory.T.continuous_standardUnitaryChart_and_symm D A μ hμ κ hκ
  have hr : 0 < absA D (aP A p) := hom_pos _ _
  have hfs : ∀ z, fam (hgtStd A a κ p) (fun g => (omS g Φ).1 0) (sZero A B) z = sect omS (hgtStd A a κ p) Φ z := fun z => by
    funext g; simp only [fam, sect, h0]
  have hback : ∀ g : G D A.rank, κ (κ.symm g * (p : GA D (dblSp A))⁻¹ * p) = g := fun g => by simp
  have hone : ∀ z : ℂ, npow (absA D (aP A p)) (z - sZero A B) * npow (absA D (aP A p)) (sZero A B - z) = 1 := fun z => by
    rw [← npow_add hr]; simp
  have hsect : ∀ z g, sect omS (hgtStd A a κ p) Φ z g = npow (absA D (aP A p)) (z - sZero A B) *
      flat A a (swSec A B omh ν 𝓨 f) (sZero A B) z (κ.symm g * (p : GA D (dblSp A))⁻¹) := fun z g => by
    rw [hflat, hback, ← mul_assoc, hone, one_mul]
  have hL : ∀ z, LeftInv (P D A.rank ⊓ GF D A.rank) (sect omS (hgtStd A a κ p) Φ z) := fun z q hq g => by
    rw [hsect, hsect, map_mul, mul_assoc (κ.symm q)]
    congr 1
    exact GlobalTheory.Eis.leftInv_of_mem hχ.1 (GlobalTheory.Eis.flat_mem hIw hmem z) _
      ⟨(hP' _).2 (by simpa using hq.1), (hG' _).2 (by simpa using hq.2)⟩ _
  have h3 : ∀ (z : ℂ) (g : GA D (dblSp A)), GlobalTheory.Eis.eisSer A (flat A a (swSec A B omh ν 𝓨 f) (sZero A B)) g z =
      npow (absA D (aP A p)) (sZero A B - z) * eisS (fam (hgtStd A a κ p) (fun g => (omS g Φ).1 0) (sZero A B) z) (κ (g * p)) :=
    fun z g => by
      rw [hfs]
      exact ((GlobalTheory.T.cosetSum_along_mulEquiv_subgroups _ _ κ (siegel A) (GQ (dblSp A)) (P D A.rank) (GF D A.rank) hP' hG' _ _ _ _ (fun g => hflat z g) (hL z)).2 g).2
  refine ⟨?_, ⟨hU, hR, hs, hd, fun g => ?_, ?_, fun z hz γ hγ g => ?_, fun z hz g => ?_⟩, fun z _ g => h3 z g⟩
  · have e : (fun g => (omS g Φ).1 0) = fun g => swSec A B omh ν 𝓨 f (κ.symm g * (p : GA D (dblSp A))⁻¹) := by
      funext g
      have := hsect (sZero A B) g
      simpa [sect, h0, flatH_self] using this
    rw [e]
    exact (hmem.2.1 : Continuous _).comp (hκc'.mul continuous_const)
  · refine DifferentiableOn.mul ?_ (hhol _)
    simp only [npow_eq_exp hr]
    fun_prop
  · refine ContinuousOn.mul ?_ (hc.comp (f := fun y : ℂ × G D A.rank => (y.1, κ.symm y.2 * (p : GA D (dblSp A))⁻¹))
      (continuous_fst.prodMk ((hκc'.comp continuous_snd).mul continuous_const)).continuousOn fun y hy => ⟨hy.1, trivial⟩)
    simp only [npow_eq_exp hr]
    fun_prop
  · rw [map_mul, mul_assoc (κ.symm γ), hi z hz _ ((hG' _).2 (by simpa using hγ))]
  · rw [he z hz, h3, hback]
    linear_combination (d.eval z * eisS (fam (hgtStd A a κ p) (fun g => (omS g Φ).1 0) (sZero A B) z) g) * hone z

theorem mem_section_space : K0 := fun D ψ A B χ om hW ν 𝓨 hν a _ f hf hK =>
  GlobalTheory.SwSecMem.swSec_mem_degPS GlobalTheory.weilRepresentationUnitaryPair D ψ A B χ om hW ν 𝓨 hν f hf a hK

theorem continuation_chart_defined : KillingPolyConst := by
  intro D A μ hμ κ hκ a ha p hp
  have hI := GlobalTheory.Eis.isIwasawa_Khat (GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha)
  have hIw := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  obtain ⟨-, hκc'⟩ := GlobalTheory.T.continuous_standardUnitaryChart_and_symm D A μ hμ κ hκ
  haveI := t2Space_adeleRing' (F := D.host.F)
  have h1 : Continuous (hgt A a) := hIw.continuous_hgtH continuous_absE (isCompact_Khat A a)
  refine ⟨⟨(h1.comp (hκc'.mul continuous_const)).mul continuous_const, fun g => mul_pos (hgtH_pos _) (hom_pos _ _),
    fun q hq α hα g => ?_⟩, ?_⟩
  · have hq' : κ.symm q ∈ siegel A := (GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D A μ hμ κ hκ (κ.symm q)).2 (by simpa using hq)
    have hdet : aP A ⟨κ.symm q, hq'⟩ = Matrix.GeneralLinearGroup.det α :=
      GlobalTheory.T.standardUnitaryChart_siegelLeviDet_eq D A μ hμ κ hκ ⟨κ.symm q, hq'⟩ α (by simpa using hα)
    have e : hgt A a (κ.symm q * (κ.symm g * (p : GA D (dblSp A))⁻¹)) =
        absA D (aP A ⟨κ.symm q, hq'⟩) * hgt A a (κ.symm g * (p : GA D (dblSp A))⁻¹) := hI.iwAbs_left ⟨κ.symm q, hq'⟩ _
    simp only [hgtStd]
    rw [map_mul, mul_assoc (κ.symm q), e, hdet, mul_assoc]
  · haveI : Submodule.IsLattice D.host.E (stdLattice D.host.E (A.rank + A.rank)) := isLattice_stdLattice
    refine ⟨levelOpen D.sp.cm.sig (Jst D A.rank) (stdLattice D.host.E (A.rank + A.rank)), isOpen_levelOpen _ _ _,
      fun k hk hf g => ?_⟩
    have hkK : k ∈ K D A.rank := mem_levelAll.2 ⟨mem_levelOpen.1 hk, fun w => by
      rw [mem_finPts_iff_forall.1 hf w]; exact one_mem _⟩
    have hk' : (p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹ ∈ Khat A a := by
      rw [hp]; simpa [mul_assoc] using hkK
    have e : hgt A a (κ.symm g * (p : GA D (dblSp A))⁻¹ * ((p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹)) =
        hgt A a (κ.symm g * (p : GA D (dblSp A))⁻¹) := hI.iwAbs_right _ hk'
    simp only [hgtStd]
    rw [← e]; simp [mul_assoc]

theorem simple_pole_rescaling : SimplePoleRescaling := by
  intro h h' s₀ c r σ hr hc hp e
  have ha : AnalyticOnNhd ℂ (fun s => npow r (s₀ - s)) (rightOf (s₀.re - 1)) := by
    intro s _
    rw [funext fun s => npow_eq_exp hr (s₀ - s)]
    fun_prop
  have hg := holValueAt_self ha (s₀ := s₀) (by linarith)
  have h1 : npow r (s₀ - s₀) = 1 := by simp
  have hm := (hp.mul_hol (by simpa using hc) hg).2
  simp only [h1, mul_one] at hm
  exact CoeffAt.congr (by simpa using hm) ⟨σ, fun s hs => by rw [e s hs, mul_comm]⟩

theorem continuous_invariant_coefficients : ContinuousInvariantCoefficients := by
  intro D n H φ s₀ U d E σ hC ε hε k
  have hm : ∀ x : ℝ, circleMap s₀ ε x ∈ Metric.closedBall s₀ ε := fun x => circleMap_mem_closedBall s₀ hε.1.le x
  have hne : ∀ x : ℝ, d.eval (circleMap s₀ ε x) ≠ 0 := fun x => hε.2.2 _ (hm x) (circleMap_ne_center hε.1.ne')
  refine ⟨continuous_const.mul ?_, fun γ hγ g => ?_⟩
  · have hE : Continuous fun y : G D n × ℝ => E (circleMap s₀ ε y.2) y.1 :=
      hC.cont.comp_continuous (f := fun y : G D n × ℝ => (circleMap s₀ ε y.2, y.1))
        (((continuous_circleMap s₀ ε).comp continuous_snd).prodMk continuous_fst) fun y => ⟨hε.2.1 (hm y.2), trivial⟩
    have hc : Continuous fun y : G D n × ℝ => circleMap s₀ ε y.2 := (continuous_circleMap s₀ ε).comp continuous_snd
    simp only [circleIntegral, deriv_circleMap]
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      (f := fun (g : G D n) (x : ℝ) => (circleMap 0 ε x * Complex.I) •
        ((circleMap s₀ ε x - s₀) ^ (k - 1) * (E (circleMap s₀ ε x) g / d.eval (circleMap s₀ ε x)))) ?_ _ _
    exact (((continuous_circleMap 0 ε).comp continuous_snd).mul continuous_const).smul
      (((hc.sub continuous_const).pow _).mul (hE.div (d.continuous.comp hc) fun y => hne y.2))
  · simp only [cf, circleIntegral, hC.inv _ (hε.2.1 (hm _)) γ hγ g]

theorem theta_kernel_identity (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (A W : HSp D) (χ : (AE D)ˣ →* Circle)
    (omh : GA D (dblSp A) × GA D W →* Module.End ℂ (WO (dblSp A) W → ℂ)) (hW : IsWeilDatumO ψ (dblSp A) W 1 χ omh)
    (ν : Measure (WO A W)) (𝓨 : Set (WO A W)) (hν : IsCovolOne (ratL W A) ν 𝓨) (κ : GA D (dblSp A) ≃* G D A.rank)
    (omS : G D A.rank →* Module.End ℂ (schwartzA θ W.rank A.rank)) (hT : IsTransport ψ θ A W ν 𝓨 omh κ omS)
    (p : GA D (dblSp A)) (Ψ : schwartzA θ W.rank A.rank) :
    ∃ f, IsThetaFunO ψ (dblSp A) W f ∧ ∀ g h, theta omS Ψ (κ (g * p)) h = thetaKO omh g h f := by
  obtain ⟨f, hf, e⟩ := (GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ hW.std θ hθ A W ν 𝓨 hν).2.1 Ψ.1 Ψ.2
  refine ⟨omh (p, 1) f, hW.om_pres _ f hf, fun g h => ?_⟩
  rw [theta, hT (g * p) f hf Ψ e.symm, ← GlobalTheory.T.thetaKernel_eq_tsum_schrodingerFunction D ψ A W χ omh hW ν 𝓨 hν f hf (g * p) h]
  unfold thetaKO
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

end PositivityTheory.Rg.Rsw.Kplug

end

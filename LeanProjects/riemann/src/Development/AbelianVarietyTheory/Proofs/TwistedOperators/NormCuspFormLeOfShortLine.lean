import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormLeOfCuspidalVariationUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupTwoModelsRationalRealUnipotentDictio
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicPointExistsIsotropicReductionOfSmallSStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeastSizePowMulSqrtAbsNormLeProdNormsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInstanceFramesOfDiagonalFrameSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicPointRationalLatticeUnitaryModelIsoEqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalVectorNormAdelicPointTwoModelsEqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalCongruenceMemLatticeCongruenceLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LipschitzBoundRealUnipotentActionStatement
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ShortLineCusp

theorem sum_sqrt_le (ι : Type) [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∑ i, Real.sqrt (a i) ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, a i) := by
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => Real.sqrt (a i))
  simp only [one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, one_mul,
    Real.sq_sqrt (ha _)] at h1
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.le_sqrt_of_sq_le
  simpa [Real.sq_sqrt (ha _)] using h1

theorem sum_sqrt_add_le : ∀ (ι : Type) [Fintype ι] (a b : ι → ℝ), (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) → ∑ i, (Real.sqrt (a i) + Real.sqrt (b i)) ≤ Real.sqrt (Fintype.card ι) * (Real.sqrt (∑ i, a i) + Real.sqrt (∑ i, b i)) := by
  intro ι _ a b ha hb
  rw [Finset.sum_add_distrib, mul_add]
  exact add_le_add (sum_sqrt_le ι a ha) (sum_sqrt_le ι b hb)

theorem finrank_eq_card_and_rd : ∀ D : D7, Module.finrank ℚ D.host.F = Fintype.card D.what₂.Tau ∧ |(discr D.host.E : ℝ)| ^ ((1 : ℝ) / (2 * (Module.finrank ℚ D.host.F : ℝ))) = rdisc D := by
  intro D
  haveI := D.sp.cm.totReal
  refine ⟨?_, ?_⟩
  · rw [Fintype.card_congr (Formalism.L2.Host.tauPl D), ← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero,
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  · unfold rdisc
    rw [← Module.finrank_mul_finrank ℚ D.host.F D.host.E, D.sp.cm.deg2]
    congr 1
    push_cast
    ring

theorem least_nonneg : ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA), 0 ≤ GlobalTheory.Count.least I x := by
  intro I x
  unfold GlobalTheory.Count.least Formalism.HN.leastSize
  apply Real.sInf_nonneg
  rintro t ⟨R, -, -, rfl⟩
  unfold Formalism.HN.size Formalism.HN.ht Formalism.F.covol
  apply Real.rpow_nonneg
  apply mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (abs_nonneg _) _))
  split_ifs <;> positivity

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem norm_le_of_not_long : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (Λ : Lat V), IsSelfDualC V Λ → ∀ (g q : ℕ), 1 ≤ g → 1 ≤ q → 1 ≤ V.rank → (∀ τ, min (Finset.univ.filter fun a => A.ε τ a = true).card (Finset.univ.filter fun a => A.ε τ a = false).card ≤ q) → ∀ φ : GA D V → ℂ, IsAutFun V φ → IsCuspFun V φ → (∀ k ∈ Lev.levA V (congLev D.sp.cm V.gram Λ (Ideal.span {((g : ℕ) : 𝓞 D.host.E)})), ∀ x, φ (x * k) = φ x) → ∀ c : ℝ, 0 ≤ c → Lip θ A φ c → ∀ (x : GA D V) (s : ℝ), 0 < s → s ≤ 1 / 2 → ¬ Long θ A Λ x s → ‖φ x‖ ≤ c * ((V.rank : ℝ) ^ 2 * Fintype.card D.what₂.Tau * g * rdisc D * (2 * s) ^ ((1 : ℝ) / q)) := by
  intro D θ hθ V A Λ hΛ g q hg hq hn hrk φ hφ hcusp hlev c hc hlip x s hs hs2 hlong
  obtain ⟨fr, hfrΛ, hfr⟩ := GlobalTheory.T.exists_instanceFrames_of_diagonalFrame_selfDual D V A Λ hΛ
  subst hfrΛ
  obtain ⟨hfF, hrdE⟩ := finrank_eq_card_and_rd D
  have hfI : (Formalism.IndefR.Eqv.UI.instV fr).f = Fintype.card D.what₂.Tau := hfF
  have hrdI : (Formalism.IndefR.Eqv.UI.instV fr).rd = rdisc D := hrdE
  set x0 := (Formalism.IndefR.Eqv.UI.brg fr).symm x with hx0
  have hbx : Formalism.IndefR.Eqv.UI.brg fr x0 = x := by simp [hx0]
  have hl0 : 0 ≤ GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0 := least_nonneg _ x0
  have hlt : GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0 < s := by
    by_contra hge
    push_neg at hge
    apply hlong
    intro 𝔪 h𝔪 w hw hw0
    have hL := GlobalTheory.T.adelicPointRationalLattice_unitaryModelIso_eq D V fr x0
    rw [hbx] at hL
    rw [hL] at hw
    have h1 := GlobalTheory.T.leastSize_pow_mul_sqrt_absNorm_le_prod_norms (Formalism.IndefR.Eqv.UI.instV fr) x0 𝔪 h𝔪 w hw hw0
    rw [GlobalTheory.T.rationalVectorNorm_adelicPoint_twoModels_eq D θ hθ V A fr (fun τ => (hfr τ).2) x0 w, hbx, hfI] at h1
    exact le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.le hge _) (Real.sqrt_nonneg _)) h1
  have hrkI : ∀ v, GlobalTheory.Count.rkR ((Formalism.IndefR.Eqv.UI.instV fr).ε v) ≤ q := by
    intro (v : InfinitePlace D.host.F)
    have h := (hfr ((Formalism.L2.Host.tauPl D).symm v)).1
    have e : (Formalism.L2.Host.tauPl D) ((Formalism.L2.Host.tauPl D).symm v) = v := Equiv.apply_symm_apply _ _
    rw [e] at h
    show GlobalTheory.Count.rkR (fr.ε v) ≤ q
    rw [h]
    exact hrk _
  obtain ⟨W, hW, hmv⟩ := GlobalTheory.T.automorphicPoint_exists_isotropic_reduction_of_small_size (Formalism.IndefR.Eqv.UI.instV fr) x0 g q hg hq hn hrkI (hlt.trans_le hs2)
  obtain ⟨hGQ, -, hN⟩ := GlobalTheory.BridgeDict.bridge_dict D θ hθ V fr
  obtain ⟨r, C₀, hC₀, hNI⟩ := hN W hW
  apply GlobalTheory.CuspGeo.norm_le_of_unipRad_variation D V φ hφ hcusp r C₀ hC₀ x
  intro m hm
  have hm' : (Formalism.IndefR.Eqv.UI.brg fr).symm m ∈ (Formalism.IndefR.Eqv.UI.instV fr).NA W :=
    hNI _ (by simpa using hm)
  obtain ⟨γ, hγ, k, hk, u, Av, Z, hAZ, hu, heq, hbd⟩ := hmv _ hm'
  have hmx : m * x = Formalism.IndefR.Eqv.UI.brg fr γ * (x * Formalism.IndefR.Eqv.UI.brg fr (u, 1)) * Formalism.IndefR.Eqv.UI.brg fr (1, k) := by
    have h2 := congrArg (Formalism.IndefR.Eqv.UI.brg fr) heq
    have h3 : ((u, k) : (Formalism.IndefR.Eqv.UI.instV fr).GA) = (u, 1) * (1, k) := by simp
    rw [h3] at h2
    simp only [map_mul, hbx, ContinuousMulEquiv.apply_symm_apply] at h2
    rw [h2]; group
  rw [hmx, hlev _ (GlobalTheory.T.principalCongruence_mem_latticeCongruenceLevel D V fr g hg k hk), hφ.left _ ((hGQ γ).2 hγ)]
  have h6 := GlobalTheory.T.lipschitz_bound_real_unipotent_action D θ hθ V A fr (fun τ => (hfr τ).2) φ c hc hlip u Av Z hAZ hu x
  have h7 := sum_sqrt_add_le (InfinitePlace D.host.F) (fun v => Formalism.REAL.hs (Av v)) (fun v => Formalism.REAL.hs (Z v))
    (fun v => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
    (fun v => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hcard : Fintype.card (InfinitePlace D.host.F) = Fintype.card D.what₂.Tau :=
    Fintype.card_congr (Formalism.L2.Host.tauPl D).symm
  rw [hcard] at h7
  rw [hfI, hrdI] at hbd
  have hL : (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) ≤ (2 * s) ^ ((1 : ℝ) / q) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  have hL0 : 0 ≤ (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) := by positivity
  have hrd0 : 0 ≤ rdisc D := by unfold rdisc; positivity
  have hN : Real.sqrt (Fintype.card D.what₂.Tau) * Real.sqrt (Fintype.card D.what₂.Tau) = Fintype.card D.what₂.Tau :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hP : 0 ≤ (V.rank : ℝ) ^ 2 * (Fintype.card D.what₂.Tau : ℝ) * (g : ℝ) * rdisc D := by positivity
  have hbd' : Real.sqrt (Fintype.card D.what₂.Tau) *
      (Real.sqrt (∑ v, Formalism.REAL.hs (Av v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v))) ≤
      (V.rank : ℝ) ^ 2 * Fintype.card D.what₂.Tau * g * rdisc D * (2 * s) ^ ((1 : ℝ) / q) := by
    calc _ ≤ Real.sqrt (Fintype.card D.what₂.Tau) * ((V.rank : ℝ) ^ 2 * Real.sqrt (Fintype.card D.what₂.Tau) * g * rdisc D *
          (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) / 4) :=
          mul_le_mul_of_nonneg_left hbd (Real.sqrt_nonneg _)
      _ = (Real.sqrt (Fintype.card D.what₂.Tau) * Real.sqrt (Fintype.card D.what₂.Tau)) * ((V.rank : ℝ) ^ 2 * g * rdisc D *
          (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q)) / 4 := by ring
      _ = ((V.rank : ℝ) ^ 2 * Fintype.card D.what₂.Tau * g * rdisc D) *
          (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) / 4 := by rw [hN]; ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hL hP, mul_nonneg hP hL0]
  calc _ ≤ _ := h6
    _ ≤ c * (Real.sqrt (Fintype.card D.what₂.Tau) *
      (Real.sqrt (∑ v, Formalism.REAL.hs (Av v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v)))) := mul_le_mul_of_nonneg_left h7 hc
    _ ≤ _ := mul_le_mul_of_nonneg_left hbd' hc

end GlobalTheory.ShortLineCusp

end

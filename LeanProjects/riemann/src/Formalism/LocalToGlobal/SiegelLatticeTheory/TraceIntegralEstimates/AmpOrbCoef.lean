import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpNZFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpOrbClosed
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpTrans
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HzOfInWb

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.L2.S.Pv.AmpOrbCoef

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.AmpOrbPf

theorem fdegH_pos {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {μG : Measure (Mt k r)} (hlam : IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ)
    (hG : PI.BesselPeriodGGP.IsHaarOn (UH (Hpk k r)) μG) {w : H} (hw : ‖w‖ = 1) :
    0 < PI.BesselPeriodGGP.fdegH μG σ w := by
  obtain ⟨d, hd, hS⟩ := Formalism.FourierDecayAlt.P.schur_hermitian k r ε lam H σ μG hlam hσ hG
  obtain ⟨hint, heq⟩ := hS w w w w
  have hf : (fun x : Mt k r => ⟪w, σ (Matrix.of x) w⟫_ℂ * star ⟪w, σ (Matrix.of x) w⟫_ℂ) =
      fun x => (((‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 : ℝ)) : ℂ) := by
    funext x
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hf, integral_complex_ofReal] at heq
  have hww : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw]; simp
  rw [hww, one_mul] at heq
  have hI : ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = 1 / d := by
    have := congrArg Complex.re heq
    simp only [Complex.ofReal_re] at this
    rw [this]
    rw [show (1 : ℂ) / (d : ℂ) = ((1 / d : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
  unfold PI.BesselPeriodGGP.fdegH
  rw [hI, hw]
  simp only [one_pow, one_div, inv_inv]
  exact hd

theorem muS_conc {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)} [SigmaFinite μW] [SigmaFinite μN]
    (hW : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z) (hN : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r) :
    muS μW μN {x | Matrix.of x ∉ UH (Hpk k r)} = 0 := by
  have hm : Measurable (fun p : Mt k r × Mt k r => fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) := by
    apply Continuous.measurable
    exact continuous_pi fun i => continuous_pi fun j => (Continuous.matrix_mul continuous_fst continuous_snd).matrix_elem i j
  set m : Mt k r × Mt k r → Mt k r := fun p => fun i j => (Matrix.of p.1 * Matrix.of p.2) i j with hmdef
  have hmuS : muS μW μN = (μW.prod μN).map m := rfl
  have hset : {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)} = {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}ᶜ := rfl
  rw [hmuS, hset, Measure.map_apply hm (Formalism.MainNotions.BesselShellMomentBounds.measurableSet_UH k r).compl]
  have g1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := Measure.quasiMeasurePreserving_fst.ae hW
  have g2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := Measure.quasiMeasurePreserving_snd.ae hN
  have g : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 * Matrix.of p.2 ∈ UH (Hpk k r) := by
    filter_upwards [g1, g2] with p h1 h2
    exact WeylGroupFacts.uh_mul h1.1 h2.1
  rw [ae_iff] at g
  exact g

theorem B_ne {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [Nontrivial Wp]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {μG μW μN νS : Measure (Mt k r)}
    (hG : IsHaarOn (UH (Hpk k r)) μG) (hW : IsHaarOn (UWset k r z) μW) (hN : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r)
    [SigmaFinite μN] (hq : IsQuotMeas μG (muS μW μN) νS) {B : H → Wp} {v0 : H}
    (hv0 : v0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) {c : ℝ} (hc : 0 < c)
    (hl2 : l2SG νS (fun g => B (σ g v0)) = ENNReal.ofReal (c * Module.finrank ℂ Wp)) :
    ∃ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B x ≠ 0 := by
  have : SigmaFinite μW := hW.1
  have hWa : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := by rw [ae_iff]; simpa using hW.2.2.1
  have hS0 : muS μW μN ≠ 0 := by
    intro h0
    have e := hq 1 measurable_one
    rw [h0] at e
    simp at e
    exact hG.2.1 (by simpa using e)
  have hae0 : ∀ᵐ y ∂νS, Matrix.of y ∈ UH (Hpk k r) := by
    rw [ae_iff]; simpa using Formalism.MainNotions.S.Pv.AmpTrans.quot_meas_not_mem_UH_eq_zero hG hS0 (muS_conc hWa hN) hq
  by_contra hcon
  push_neg at hcon
  have hσU := Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hσ
  have hz0 : l2SG νS (fun g => B (σ g v0)) = 0 := by
    unfold l2SG
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hae0] with y hy
    show (‖B (σ (Matrix.of y) v0)‖₊ : ℝ≥0∞) ^ 2 = 0
    rw [hcon _ (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσU hv0 hy)]
    simp
  rw [hl2] at hz0
  have hm0 : 0 < c * (Module.finrank ℂ Wp : ℝ) := mul_pos hc (by exact_mod_cast Module.finrank_pos)
  exact (ENNReal.ofReal_pos.2 hm0).ne' hz0

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

theorem ampOrbCoefDD_of (hJ : PI.BesselMapUniq.BesselMapUniq) : Formalism.MainNotions.S.Pv.LemmaJ.AmpOrbCoefDD := by
  intro Cg cb Cu cT CT C0
  refine ⟨0, 1000, fun C' Cl _ hCl D large₂ hH τ w w' hTT θ W hW A hA hT hT' => ?_⟩
  have hI : Formalism.FourierDecayAlt.ThreeDimData.Inputs := Formalism.MainNotions.BridgeCS3dClosed.inputs_of Formalism.L2.SG.BesselDiscreteSeries.decInf hJ
  have hAt := Formalism.FourierDecayAlt.P.admissible_atomic_form_one
  have hl0 : l1dist (lamD D τ) (lamD D τ) ≤ 0 * D.R.k * (D.R.m : ℝ) ^ 3 := by unfold l1dist; simp
  obtain ⟨h, hg, hok, hcell⟩ :=
    Formalism.MainNotions.S.Pv.AmpDDPf.gap_of_hypotheses D large₂ C' Cl Cg cb Cu cT CT C0 0 hCl (by linarith) hH τ (lamD D τ) hl0
  set L := toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT' with hL
  set w0 : A.H := (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) with hw0def
  obtain ⟨l, l', hl1, hl1', hOP⟩ := ls_pair hI hAt hW hA hT hT' hg hok
  have hw0 : PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) A.σ w0 := lowest_K_type_unit hA
  have hKS : PI.KFinSmooth := hI.2.2.1
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  have hDDs : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp A.σ w0, x ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hKS hA.1 hA.2.1 hw0

  obtain ⟨⟨x, hx, y, hy, hxy⟩, ⟨x', hx', y', hy', hxy'⟩⟩ :=
    Formalism.L2.S.Pv.NonVacuity.nvHyp0 D large₂ C' Cl Cg cb Cu cT CT C0 (by linarith) hH τ w w' hTT θ W hW (lamD D τ) hl0 A hA hT hT'
      w0 hw0
  have hlx : l x ≠ 0 := by
    intro h0; apply hxy
    have e : Formalism.FourierDecayAlt.ThreeDimData.be W.z L.c W.π A.σ W.μW L.μN x y = (innerSL ℂ (l y)).smulRight (l x) :=
      hOP.1.2.2.2.2.2.1 x hx y hy
    rw [e, h0]; ext; simp
  have hlx' : l' x' ≠ 0 := by
    intro h0; apply hxy'
    have e : Formalism.FourierDecayAlt.ThreeDimData.be W.z' L.c W.π' A.σ W.μW' L.μN x' y' = (innerSL ℂ (l' y')).smulRight (l' x') :=
      hOP.1.2.2.2.2.2.2 x' hx' y' hy'
    rw [e, h0]; ext; simp

  have hB : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z (fun _ => L.c)) A.σ W.π A.B := by
    rw [psiGen_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).1 hA.2.2.1
  have hB' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z' (fun _ => L.c)) A.σ W.π' A.B' := by
    rw [psiGen_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).1 hA.2.2.2.1
  have hlG : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z (fun _ => L.c)) A.σ W.π l := by
    rw [psiGen_const]; exact hl1
  have hlG' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z' (fun _ => L.c)) A.σ W.π' l' := by
    rw [psiGen_const]; exact hl1'
  obtain ⟨c0, hc0⟩ := Formalism.MainNotions.S.Pv.AIsL.aIsL hJ hA.1 hA.2.1 L.hz.1 L.hz.2 (fun _ => c_ne_zero D) L.hπ hB hlG
    ⟨x, hDDs x hx, hlx⟩
  obtain ⟨c0', hc0'⟩ := Formalism.MainNotions.S.Pv.AIsL.aIsL hJ hA.1 hA.2.1 L.hz'.1 L.hz'.2 (fun _ => c_ne_zero D) L.hπ' hB' hlG'
    ⟨x', hDDs x' hx', hlx'⟩

  have hW' := hW
  obtain ⟨hc1, hc2, -, -, -, -, -, hUW, -, hUW', -, hNq, hq, hq'⟩ := hW'
  have hA' := hA
  obtain ⟨-, -, -, -, hv0s, hv0ne, -, hcN, hl2, hl2', -⟩ := hA'
  have hNa : ∀ᵐ x ∂W.μN, Matrix.of x ∈ Nset D.R.k D.R.rS := by
    rw [hNq]; exact Formalism.MainNotions.S.Pv.AmpDDPf.ae_mem_haarLieN _
  have hκtop : kapN D θ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hκ0 : kapN D θ ≠ 0 := Formalism.L2.SG.AmpOrbPf.kapN_ne_zero hW
  have : SigmaFinite W.μN := by
    have := (Formalism.MainNotions.BridgeCSB.haarLieN D.R.k D.R.rS _ hκ0 hκtop).1
    rw [hNq]; exact this
  have hNt : Nontrivial W.Wp := by obtain ⟨g, -, hU⟩ := hc1; exact hU.1
  have hNt' : Nontrivial W.Wq := by obtain ⟨g, -, hU⟩ := hc2; exact hU.1
  obtain ⟨xb, hxb, hBx⟩ := B_ne hA.2.1 hG hUW hNa hq hv0s hcN hl2
  obtain ⟨xb', hxb', hBx'⟩ := B_ne hA.2.1 hG hUW' hNa hq' hv0s hcN hl2'
  have hc0ne : c0 ≠ 0 := by
    intro e; apply hBx; have h1 := hc0 xb hxb; rw [e] at h1; rw [h1]; exact zero_smul ℂ _
  have hc0ne' : c0' ≠ 0 := by
    intro e; apply hBx'; have h1 := hc0' xb' hxb'; rw [e] at h1; rw [h1]; exact zero_smul ℂ _

  set t : ℂ := ((‖A.v0‖ : ℝ) : ℂ) with ht
  have hv0 : A.v0 = t • w0 := by
    rw [hw0def, ht, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0ne),
      Complex.ofReal_one, one_smul]
  have htne : t ≠ 0 := by rw [ht]; exact_mod_cast norm_ne_zero_iff.mpr hv0ne
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul _ hv0s
  have hΦ : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ g = (c0 * t) • l (A.σ g w0) := by
    intro g hg'
    show A.B (A.σ g A.v0) = _
    rw [hv0]
    exact orbit_mul hA.2.1 c0 hc0 hl1.2.1 hw0s t hg'
  have hΦ' : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ' g = (c0' * t) • l' (A.σ g w0) := by
    intro g hg'
    show A.B' (A.σ g A.v0) = _
    rw [hv0]
    exact orbit_mul hA.2.1 c0' hc0' hl1'.2.1 hw0s t hg'

  set s : ℂ := ⟪l x, l x⟫_ℂ * ⟪l' x', l' x'⟫_ℂ with hs
  have hs0 : s ≠ 0 := mul_ne_zero (inner_self_ne_zero.mpr hlx) (inner_self_ne_zero.mpr hlx')
  set dg : ℂ := (PI.BesselPeriodGGP.fdegH W.μG A.σ w0 : ℂ) with hdg
  have hdg0 : dg ≠ 0 := by
    rw [hdg]
    obtain ⟨-, -, hn1, -⟩ := hw0
    exact_mod_cast (fdegH_pos hA.1 hA.2.1 hG hn1).ne'
  set K1 : ℂ := ((A.cN : ℂ)⁻¹) * (c0 * t) * (starRingEnd ℂ) (c0' * t) with hK1
  have hK1ne : K1 ≠ 0 := by
    rw [hK1]
    refine mul_ne_zero (mul_ne_zero (inv_ne_zero (by exact_mod_cast hcN.ne')) (mul_ne_zero hc0ne htne)) ?_
    exact (map_ne_zero _).2 (mul_ne_zero hc0ne' htne)
  refine ⟨x, x', l x, l' x', l x, l' x', K1 * s⁻¹ * dg⁻¹,
    mul_ne_zero (mul_ne_zero hK1ne (inv_ne_zero hs0)) (inv_ne_zero hdg0), hDDs x hx, hDDs x' hx',
    hOP.1.2.2.2.2.2.1 x hx x hx, hOP.1.2.2.2.2.2.2 x' hx' x' hx', inner_self_ne_zero.mpr hlx,
    inner_self_ne_zero.mpr hlx', ?_⟩
  intro γ hγ hGf hMono hRel μR νR ν hRH hOQ hqR
  have hCD : Formalism.MainNotions.S.Pv.AmpDD.CellData L W.μG γ μR νR ν := ⟨hγ, hGf, hMono, hRel, hRH, hOQ, hqR⟩
  obtain ⟨b, hb0, hbm, hbi⟩ :=
    Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence _ _ L h W.μG γ μR νR ν ENNReal.ofReal_ne_top hok hcell hCD hMono
  have hAmp := Formalism.L2.SG.AmpOrbClosed.ampDD_thm hI _ _ L h W.μG w0 l l' hOP.1 γ μR νR ν hCD b hb0 (by linarith) hbi
    x hx x' hx' (l x) (l' x')
  have hae := ae_UH_conj hγ hG hRH hqR
  have hJ1 : A.J νR γ = K1 • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ :=
    ampJ_mul νR A.cN A.Φ _ A.Φ' _ (c0 * t) (c0' * t) γ hγ hΦ hΦ' hae
  have hJ2 : ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
      (s⁻¹ * dg⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L x x' (l x) (l' x')) γ ν := by
    have hAmp' : s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
        dg⁻¹ • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L x x' (l x) (l' x')) γ ν := hAmp
    have e1 : ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
        s⁻¹ • (s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ) := by
      rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [e1, hAmp']
    exact smul_smul s⁻¹ dg⁻¹ _
  rw [hJ1, hJ2]
  have hO := orbInt_smul L (K1 * s⁻¹ * dg⁻¹) (Formalism.MainNotions.S.Pv.AmpDD.coefF L x x' (l x) (l' x')) γ ν
  have e2 : K1 • ((s⁻¹ * dg⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L x x' (l x) (l' x')) γ ν) =
      (K1 * s⁻¹ * dg⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L x x' (l x) (l' x')) γ ν := by
    rw [smul_smul]
    congr 1
    ring
  exact e2.trans hO.symm

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

theorem amplitude_uniform_of_bessel_uniq (hJ : PI.BesselMapUniq.BesselMapUniq) (hKD : Formalism.MainNotions.S.Pv.AmpDD.KDense)
    (hRJ : Formalism.MainNotions.S.Pv.LemmaJ.RootJac) (hRH : Formalism.MainNotions.S.Pv.LemmaJ.RootHaar) (hOQ : Formalism.MainNotions.S.Pv.LemmaJ.OrbQuotEx)
    (hRA : Formalism.MainNotions.S.Pv.LemmaJ.RelAtPt) (hBI : Formalism.MainNotions.S.Pv.BetaCut.BetaInfCoefNZ) : Formalism.MainNotions.S.Pv.LemmaJ.AmpUnif :=
  Formalism.MainNotions.S.Pv.LemmaJ.amplitude_uniform_of_coefficients hJ hKD hRJ hRH hOQ hRA (ampOrbCoefDD_of hJ) hBI

end Formalism.L2.S.Pv.AmpOrbCoef

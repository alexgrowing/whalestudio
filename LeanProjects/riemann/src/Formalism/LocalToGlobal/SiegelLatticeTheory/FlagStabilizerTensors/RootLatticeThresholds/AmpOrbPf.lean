import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpOrbOfAmpDD
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AIsL
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothAdd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit

set_option linter.unusedVariables false

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.L2.SG.AmpOrbPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

theorem lowest_K_type_unit {D : D7} {W : LocW D.R.k D.R.rS} {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W}
    (hA : GoodS D lam A) :
    PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) := by
  obtain ⟨-, -, -, -, -, hne, ⟨P, hP, hmem⟩, -⟩ := hA
  refine ⟨P, hP, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)
  · exact Submodule.smul_mem _ _ hmem

theorem c_ne_zero (D : D7) :
    (((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ)) ≠ 0 := by
  have hrd : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.E)) _
  have hka : 0 < D.host.ka := by
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    exact div_pos Real.pi_pos (by linarith)
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  exact_mod_cast (div_pos (by linarith) (mul_pos hg0 hg1)).ne'

theorem kapN_ne_zero {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    (hW : GoodW D τ w w' θ W) : kapN D θ ≠ 0 := by
  intro h0
  obtain ⟨-, -, -, -, -, -, hG, -, -, -, -, hN, hq, -⟩ := hW
  have hN0 : W.μN = 0 := by rw [hN, h0]; simp [haarLie]
  have hq1 := hq (fun _ => 1) measurable_const
  simp [muS, hN0] at hq1
  exact hG.2.1 hq1

theorem muN_haar {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W} (hW : GoodW D τ w w' θ W) (hA : GoodS D lam A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') :
    IsHaarOn (Nset D.R.k D.R.rS) (toBessel D τ w w' θ W lam A hW hA hT hT').μN :=
  Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (kapN_ne_zero hW) ENNReal.ofReal_ne_top

theorem side_pair {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W} (hW : GoodW D τ w w' θ W) (hA : GoodS D lam A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') {h : ℝ} (hg : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h) :
    Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) lam h A.σ (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) W.z
              (toBessel D τ w w' θ W lam A hW hA hT hT').c (toBessel D τ w w' θ W lam A hW hA hT hT').u W.π W.μW
              (toBessel D τ w w' θ W lam A hW hA hT hT').μN W.μG W.νS ∧
      Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) lam h A.σ (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) W.z'
        (toBessel D τ w w' θ W lam A hW hA hT hT').c (toBessel D τ w w' θ W lam A hW hA hT hT').u' W.π' W.μW'
        (toBessel D τ w w' θ W lam A hW hA hT hT').μN W.μG W.νS' := by
  set L := toBessel D τ w w' θ W lam A hW hA hT hT' with hL
  have hN := muN_haar hW hA hT hT'
  have hc : L.c ≠ 0 := c_ne_zero D
  have hw0 := lowest_K_type_unit hA
  have hW2 := hW
  obtain ⟨-, -, -, -, -, -, hG, -, -, -, -, hWN, hq0, hq0'⟩ := hW2
  have hμN : W.μN = L.μN := hWN
  have hq : PI.BesselPeriodGGP.IsQuotMeas W.μG (Formalism.FourierDecayAlt.ThreeDimData.muSof W.μW L.μN) W.νS := by
    rw [← hμN]; exact hq0
  have hq' : PI.BesselPeriodGGP.IsQuotMeas W.μG (Formalism.FourierDecayAlt.ThreeDimData.muSof W.μW' L.μN) W.νS' := by
    rw [← hμN]; exact hq0'
  exact ⟨⟨hA.1, hA.2.1, hg, hok, hw0, L.hz.1, L.hz.2, hc, L.hπ, L.hμW.1, hN, hG, hq⟩,
    ⟨hA.1, hA.2.1, hg, hok, hw0, L.hz'.1, L.hz'.2, hc, L.hπ', L.hμW'.1, hN, hG, hq'⟩⟩

theorem ls_pair (hI : Formalism.FourierDecayAlt.ThreeDimData.Inputs) (hAt : Formalism.FourierDecayAlt.ThreeDimData.AtFormAdmOne)
    {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W} (hW : GoodW D τ w w' θ W) (hA : GoodS D lam A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') {h : ℝ} (hg : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h) :
    ∃ (l : A.H → W.Wp) (l' : A.H → W.Wq),
      PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
        (psi D.R.k D.R.rS W.z (toBessel D τ w w' θ W lam A hW hA hT hT').c) A.σ W.π l ∧
      PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
        (psi D.R.k D.R.rS W.z' (toBessel D τ w w' θ W lam A hW hA hT hT').c) A.σ W.π' l' ∧
      Formalism.MainNotions.S.Pv.AmpDD.OnePlaceKF (toBessel D τ w w' θ W lam A hW hA hT hT') h W.μG
        (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) l l' := by
  set L := toBessel D τ w w' θ W lam A hW hA hT hT' with hL
  obtain ⟨h1, h2⟩ := side_pair hW hA hT hT' hg hok
  obtain ⟨l, hl, hla, -⟩ := hAt hI _ _ _ _ h _ A.σ _ W.Wp _ _ _ _ _ _ _ _ h1
  obtain ⟨l', hl', hla', -⟩ := hAt hI _ _ _ _ h _ A.σ _ W.Wq _ _ _ _ _ _ _ _ h2
  have hKS : PI.KFinSmooth := hI.2.2.1
  have hw0 := lowest_K_type_unit hA
  have hDDs : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp A.σ (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0),
      x ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hKS hA.1 hA.2.1 hw0
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  refine ⟨l, l', hl, hl', ⟨⟨hg, hok, c_ne_zero D, hw0, hG, ?_, ?_⟩, ?_, ?_⟩⟩
  · intro x hx v hv
    exact (hla x (hDDs x hx) v (Or.inl hv)).2
  · intro x hx v hv
    exact (hla' x (hDDs x hx) v (Or.inl hv)).2
  · intro x hx v hv
    exact (hla x (hDDs x hx) v (Or.inr hv)).2
  · intro x hx v hv
    exact (hla' x (hDDs x hx) v (Or.inr hv)).2

theorem orbit_mul {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {B l : H → V} (c0 : ℂ)
    (hB : ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B v = c0 • l v)
    (hlin : ∀ (a : ℂ), ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, l (a • v) = a • l v)
    {w0 : H} (hw0 : w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) (t : ℂ)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    B (σ g (t • w0)) = (c0 * t) • l (σ g w0) := by
  have hs : σ g w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ :=
    Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_translate hσ hw0 hg
  rw [map_smul, hB _ (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul t hs), hlin t _ hs, smul_smul]

theorem ampJ_mul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (νR : Measure (Mt k r)) (cN : ℝ)
    (Φ L1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp)
    (Φ' L1' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wq) (a a' : ℂ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hγ : γ ∈ UH (Hpk k r))
    (hΦ : ∀ g ∈ UH (Hpk k r), Φ g = a • L1 g) (hΦ' : ∀ g ∈ UH (Hpk k r), Φ' g = a' • L1' g)
    (hae : ∀ᵐ x ∂νR, Matrix.of x ∈ UH (Hpk k r)) :
    ampJ νR cN Φ Φ' γ = (((cN : ℂ)⁻¹) * a * (starRingEnd ℂ) a') • ampJ νR 1 L1 L1' γ := by
  unfold ampJ
  have hcongr : (fun x : Mt k r => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) =ᵐ[νR]
      (fun x => (a * (starRingEnd ℂ) a') • (innerSL ℂ (L1' (Matrix.of x))).smulRight (L1 (γ * Matrix.of x))) := by
    filter_upwards [hae] with x hx
    have hγx : γ * Matrix.of x ∈ UH (Hpk k r) := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hγ hx
    rw [hΦ _ hγx, hΦ' _ hx]
    ext η
    simp [smul_smul, mul_comm]
    congr 1; ring
  rw [integral_congr_ae hcongr, integral_smul, smul_smul]
  simp only [Complex.ofReal_one, inv_one, one_smul]
  congr 1; ring

theorem psiGen_const {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    PI.BesselMapUniq.psiGen k r z (fun _ => c) = psi k r z c := by
  funext g
  unfold PI.BesselMapUniq.psiGen PI.BesselMapUniq.ellA psi ell
  rw [Finset.mul_sum]

theorem orbInt_smul {k r : ℕ} (L : LocBessel k r) (a : ℂ)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ν : Measure (PairSp k r)) :
    OrbInt L (fun g => a • F g) γ ν = a • OrbInt L F γ ν := by
  unfold OrbInt
  rw [← integral_smul]
  congr 1
  funext p
  unfold besselIntg
  rw [smul_comm]
  congr 1
  ext η
  simp

theorem kfin_coef {k r : ℕ} (L : LocBessel k r) (a : ℂ) (v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (hv : PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v) (hv' : PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v') :
    IsKFinCoefH L.σ (fun g => a • Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ' g) := by
  refine ⟨a • (innerSL ℂ v).smulRight ξ, (innerSL ℂ ξ').smulRight v', ?_, ?_, ?_⟩
  · intro η
    obtain ⟨S, hS, hvS, hSinv⟩ := hv'
    exact ⟨S, hS, S.smul_mem _ hvS, hSinv⟩
  · intro x
    have hadj : ContinuousLinearMap.adjoint (a • (innerSL ℂ v).smulRight ξ) x =
        ((starRingEnd ℂ) a * ⟪ξ, x⟫_ℂ) • v := by
      apply ext_inner_right ℂ
      intro y
      rw [ContinuousLinearMap.adjoint_inner_left]
      simp [inner_smul_left, inner_smul_right]
      ring
    rw [hadj]
    obtain ⟨S, hS, hvS, hSinv⟩ := hv
    exact ⟨S, hS, S.smul_mem _ hvS, hSinv⟩
  · intro g
    ext η
    simp [Formalism.MainNotions.S.Pv.AmpDD.coefF, smul_smul]

theorem ae_UH_conj {k r : ℕ} {μG μR νR : Measure (Mt k r)}
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r))
    (hG : IsHaarOn (UH (Hpk k r)) μG) (hR : IsHaarOn (RStab k r γ) μR)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR) :
    ∀ᵐ x ∂νR, Matrix.of x ∈ UH (Hpk k r) := by
  have hc : Continuous (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j) := by
    have h1 : Continuous (fun x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => γ⁻¹ * x * γ) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact h1
  have hf : Measurable (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j) := hc.measurable
  have hUm : MeasurableSet {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)} :=
    Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet
  refine Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 ?_ ?_ hq
  · intro h0
    exact hR.2.1 ((Measure.map_eq_zero_iff hf.aemeasurable).1 h0)
  · rw [Measure.map_apply hf hUm]
    refine measure_mono_null (fun x hx => ?_) hR.2.2.1
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢
    intro hxR
    exact hx hxR.2.1

theorem amplitudeOrbit_of_local (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) :
    Formalism.MainNotions.S.Pv.AmpDD.AmpOrbOfAmpDD D large₂ C' Cl Cg cb Cu cT CT C0 Cn := by
  intro hI hDD hAt hKD hNz hAKF hCC hGap hNV
  intro hH hCl hCn τ w w' hTT θ W hW lam' hl A hA hT hT'
  obtain ⟨h, hg, hok, hcell⟩ := hGap hCl hCn hH τ lam' hl
  set L := toBessel D τ w w' θ W lam' A hW hA hT hT' with hL
  set w0 : A.H := (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) with hw0def
  obtain ⟨l, l', hl1, hl1', hOP⟩ := ls_pair hI hAt hW hA hT hT' hg hok
  have hw0 : PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam' A.σ w0 := lowest_K_type_unit hA
  have hKS : PI.KFinSmooth := hI.2.2.1
  have hJ : PI.BesselMapUniq.BesselMapUniq := hI.2.2.2
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  have hDDs : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp A.σ w0, x ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hKS hA.1 hA.2.1 hw0

  obtain ⟨⟨x, hx, y, hy, hxy⟩, ⟨x', hx', y', hy', hxy'⟩⟩ :=
    hNV hH τ w w' hTT θ W hW lam' hl A hA hT hT' w0 hw0
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

  obtain ⟨v, hvK, hlv⟩ := hNz hKD hKS _ _ _ _ _ A.σ w0 W.Wp W.z L.c W.π hA.1 hA.2.1 hw0 l hl1 ⟨x, hx, hlx⟩
  obtain ⟨v', hvK', hlv'⟩ := hNz hKD hKS _ _ _ _ _ A.σ w0 W.Wq W.z' L.c W.π' hA.1 hA.2.1 hw0 l' hl1' ⟨x', hx', hlx'⟩

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

  set t : ℂ := ((‖A.v0‖ : ℝ) : ℂ) with ht
  have hv0ne : A.v0 ≠ 0 := hA.2.2.2.2.2.1
  have hv0 : A.v0 = t • w0 := by
    rw [hw0def, ht, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0ne),
      Complex.ofReal_one, one_smul]
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul _ hA.2.2.2.2.1
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

  set s : ℂ := ⟪l v, l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ with hs
  have hs0 : s ≠ 0 := mul_ne_zero (inner_self_ne_zero.mpr hlv) (inner_self_ne_zero.mpr hlv')
  set dg : ℂ := (PI.BesselPeriodGGP.fdegH W.μG A.σ w0 : ℂ) with hdg
  set K1 : ℂ := ((A.cN : ℂ)⁻¹) * (c0 * t) * (starRingEnd ℂ) (c0' * t) with hK1
  refine ⟨fun g => (K1 * s⁻¹ * dg⁻¹) • Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' (l v) (l' v') g,
    kfin_coef L _ v v' _ _ hvK hvK', ?_⟩
  intro γ hγ hGf hMono hRel μR νR ν hRH hOQ hqR
  have hCD : Formalism.MainNotions.S.Pv.AmpDD.CellData L W.μG γ μR νR ν := ⟨hγ, hGf, hMono, hRel, hRH, hOQ, hqR⟩
  obtain ⟨b, hb0, hbm, hbi⟩ := hCC _ _ L h W.μG γ μR νR ν ENNReal.ofReal_ne_top hok hcell hCD hMono
  have hAmp := hAKF hI _ _ L h W.μG w0 l l' hOP γ μR νR ν hCD b hb0 hbm hbi v v' hvK hvK' (l v) (l' v')
  have hae := ae_UH_conj hγ hG hRH hqR
  have hJ1 : A.J νR γ = K1 • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ :=
    ampJ_mul νR A.cN A.Φ _ A.Φ' _ (c0 * t) (c0' * t) γ hγ hΦ hΦ' hae
  have hJ2 : ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
      (s⁻¹ * dg⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' (l v) (l' v')) γ ν := by
    have hAmp' : s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
        dg⁻¹ • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' (l v) (l' v')) γ ν := hAmp
    have e1 : ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
        s⁻¹ • (s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ) := by
      rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [e1, hAmp']
    exact smul_smul s⁻¹ dg⁻¹ _
  rw [hJ1, hJ2]
  have hO := orbInt_smul L (K1 * s⁻¹ * dg⁻¹) (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' (l v) (l' v')) γ ν
  have e2 : K1 • ((s⁻¹ * dg⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' (l v) (l' v')) γ ν) =
      (K1 * s⁻¹ * dg⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' (l v) (l' v')) γ ν := by
    rw [smul_smul]
    congr 1
    ring
  exact e2.trans hO.symm

end Formalism.L2.SG.AmpOrbPf

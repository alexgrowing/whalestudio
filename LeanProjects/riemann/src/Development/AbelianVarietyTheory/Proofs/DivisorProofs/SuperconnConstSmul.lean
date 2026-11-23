import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnFormSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnectionContDiffOnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnectionIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnectionSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnectionFibreGaugeStatement

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm.Gauge
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm.Gauge

open GlobalTheory.TorsionForm

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}

theorem superconn_congr (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ)
    {s₁ s₂ : Pt E g → Ext (n + n + g)} {P : Pt E g} (hs : s₁ =ᶠ[𝓝 P] s₂) :
    superconn τ h β u s₁ =ᶠ[𝓝 P] superconn τ h β u s₂ := by
  filter_upwards [hs.eventuallyEq_nhds] with Q hQ
  have hf : fderiv ℝ s₁ Q = fderiv ℝ s₂ Q := hQ.fderiv_eq
  have h0 : s₁ Q = s₂ Q := hQ.eq_of_nhds
  simp only [superconn, nablaE, pointDifference, d10, d01, dbarV, dbarAdj, hf, h0]

theorem superconn_const_smul (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E)
    (u : ℝ) {s : Pt E g → Ext (n + n + g)} {P : Pt E g} (hs : DifferentiableAt ℝ s P) (c : ℂ) :
    superconn τ h β u (fun Q => c • s Q) P = c • superconn τ h β u s P := by
  have hd : fderiv ℝ (fun Q => c • s Q) P = c • fderiv ℝ s P := fderiv_const_smul hs c
  have h10 : ∀ v, d10 (fun Q => c • s Q) P v = c • d10 s P v := fun v => by
    simp only [d10, hd, ContinuousLinearMap.smul_apply]; module
  have h01 : ∀ v, d01 (fun Q => c • s Q) P v = c • d01 s P v := fun v => by
    simp only [d01, hd, ContinuousLinearMap.smul_apply]; module
  simp only [superconn, nablaE, pointDifference, dbarV, dbarAdj, h10, h01, connForm_smul, wedge_smul,
    contr_smul, Finset.smul_sum, smul_add, smul_neg, smul_comm c, ← wedge_smul, ← contr_smul,
    wedge_add, contr_add]

theorem phi_contDiffOn [FiniteDimensional ℂ E] {B : Set E} {φ : Pt E g → ℂ} (hB : IsOpen B)
    (hφ : DifferentiableOn ℂ φ (cov B g)) : ContDiffOn ℝ ∞ φ (cov B g) :=
  (GlobalTheory.SCV.contDiffOn_of_differentiableOn (hB.prod isOpen_univ) hφ _).restrict_scalars ℝ

theorem phi_slice_contDiff [FiniteDimensional ℂ E] {B : Set E} {φ : Pt E g → ℂ} (hB : IsOpen B)
    {b : E} (hb : b ∈ B) (hφ : DifferentiableOn ℂ φ (cov B g)) :
    ContDiff ℝ ∞ (fun y : Fin g → ℂ => φ (b, y)) :=
  contDiffOn_univ.1 ((phi_contDiffOn hB hφ).comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun _ _ => ⟨hb, trivial⟩))

end GlobalTheory.TorsionForm.Gauge

namespace GlobalTheory.TorsionForm.Gauge

open GlobalTheory.TorsionForm

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ}

theorem curv_const_smul {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {h : Pt E g → ℝ}
    (hτ : IsPeriodMap B τ) (hh : ContDiffOn ℝ ∞ h (cov B g)) (hh0 : ∀ P ∈ cov B g, 0 < h P)
    (β : Fin n → E) (u : ℝ) {b : E} (hb : b ∈ B) {f : (Fin g → ℂ) → Ext (n + n + g)}
    (hf : ContDiff ℝ ∞ f) (c : ℂ) (z : Fin g → ℂ) :
    curv τ h β b u (fun y => c • f y) z = c • curv τ h β b u f z := by
  have hcov : IsOpen (cov B g) := hτ.1.prod isOpen_univ
  have hP : ((b, z) : Pt E g) ∈ cov B g := ⟨hb, trivial⟩
  have hS : ContDiff ℝ ∞ (fun P : Pt E g => f P.2) := hf.comp contDiff_snd
  have e : superconn τ h β u (fun P : Pt E g => c • f P.2) =
      fun Q => c • superconn τ h β u (fun P : Pt E g => f P.2) Q :=
    funext fun Q => superconn_const_smul τ h β u ((hS.differentiable (by simp)) Q) c
  unfold curv
  rw [e]
  exact superconn_const_smul τ h β u
    (((GlobalTheory.T.superconnection_contDiffOn E g n B τ h β u _ hτ hh hh0 hS.contDiffOn).differentiableOn (by simp) _ hP).differentiableAt
      (hcov.mem_nhds hP)) c

theorem curv_gauge {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {h h' : Pt E g → ℝ}
    {φ : Pt E g → ℂ} (hτ : IsPeriodMap B τ) (hh : ContDiffOn ℝ ∞ h (cov B g))
    (hh0 : ∀ P ∈ cov B g, 0 < h P) (hh' : ContDiffOn ℝ ∞ h' (cov B g))
    (hh'0 : ∀ P ∈ cov B g, 0 < h' P) (hφ : DifferentiableOn ℂ φ (cov B g))
    (hφ0 : ∀ P ∈ cov B g, φ P ≠ 0) (hisom : IsIsometry B h h' φ) (β : Fin n → E) (u : ℝ) {b : E}
    (hb : b ∈ B) {f : (Fin g → ℂ) → Ext (n + n + g)} (hf : ContDiff ℝ ∞ f) (z : Fin g → ℂ) :
    curv τ h' β b u (fun y => φ (b, y) • f y) z = φ (b, z) • curv τ h β b u f z := by
  have hB : IsOpen B := hτ.1
  have hcov : IsOpen (cov B g) := hB.prod isOpen_univ
  have hP : ((b, z) : Pt E g) ∈ cov B g := ⟨hb, trivial⟩
  have hS : ContDiff ℝ ∞ (fun P : Pt E g => f P.2) := hf.comp contDiff_snd
  have hφs : ContDiffOn ℝ ∞ φ (cov B g) := phi_contDiffOn hB hφ
  have hψ : ContDiff ℝ ∞ (fun P : Pt E g => φ (b, P.2)) :=
    (phi_slice_contDiff hB hb hφ).comp contDiff_snd
  have hρ : ContDiffOn ℝ ∞ (fun P : Pt E g => φ (b, P.2) / φ P) (cov B g) :=
    (hψ.contDiffOn.mul (hφs.inv hφ0)).congr fun P _ => by simp [div_eq_mul_inv]
  have hρ1 : ∀ y, (fun P : Pt E g => φ (b, P.2) / φ P) (b, y) = 1 := fun y =>
    div_self (hφ0 _ ⟨hb, trivial⟩)
  have hφS : ContDiffOn ℝ ∞ (fun Q : Pt E g => φ Q • f Q.2) (cov B g) := hφs.smul hS.contDiffOn
  have hdh : ∀ Q ∈ cov B g, DifferentiableAt ℝ h Q := fun Q hQ =>
    (hh.differentiableOn (by simp) Q hQ).differentiableAt (hcov.mem_nhds hQ)
  have e1 : (fun Q : Pt E g => φ (b, Q.2) • f Q.2) =ᶠ[𝓝 (b, z)]
      fun Q => (φ (b, Q.2) / φ Q) • (φ Q • f Q.2) := by
    filter_upwards [hcov.mem_nhds hP] with Q hQ
    rw [smul_smul, div_mul_cancel₀ _ (hφ0 Q hQ)]
  have e2 : superconn τ h' β u (fun Q : Pt E g => φ Q • f Q.2) =ᶠ[𝓝 (b, z)]
      fun Q => φ Q • superconn τ h β u (fun P : Pt E g => f P.2) Q := by
    filter_upwards [hcov.mem_nhds hP] with Q hQ
    exact GlobalTheory.T.superconnection_isometry E g n B τ h h' φ β u _ Q hB hQ hφ hφ0 hh0 (hdh Q hQ) hisom
      ((hS.differentiable (by simp)) Q)
  have hl := GlobalTheory.T.superconnection_fibre_gauge E g n B τ h' β u _ _ hτ hh' hh'0 hρ hφS b hb hρ1 z
  have e3 : superconn τ h' β u (fun Q => (φ (b, Q.2) / φ Q) • (φ Q • f Q.2)) =ᶠ[𝓝 (b, z)]
      fun Q => (φ (b, Q.2) / φ Q) • superconn τ h' β u (fun Q : Pt E g => φ Q • f Q.2) Q +
        commOp τ β u (fun P : Pt E g => φ (b, P.2) / φ P) Q (φ Q • f Q.2) := by
    filter_upwards [hcov.mem_nhds hP] with Q hQ
    exact GlobalTheory.T.superconnection_smul E g n τ h' β u _ _ Q
      ((hρ.differentiableOn (by simp) Q hQ).differentiableAt (hcov.mem_nhds hQ))
      ((hφS.differentiableOn (by simp) Q hQ).differentiableAt (hcov.mem_nhds hQ))
  have hL2 := GlobalTheory.T.superconnection_contDiffOn E g n B τ h β u _ hτ hh hh0 hS.contDiffOn
  unfold curv
  show superconn τ h' β u (superconn τ h' β u fun Q : Pt E g => φ (b, Q.2) • f Q.2) (b, z) = _
  rw [(superconn_congr τ h' β u (superconn_congr τ h' β u e1)).eq_of_nhds,
    (superconn_congr τ h' β u e3).eq_of_nhds, hl, (superconn_congr τ h' β u e2).eq_of_nhds]
  exact GlobalTheory.T.superconnection_isometry E g n B τ h h' φ β u _ _ hB hP hφ hφ0 hh0 (hdh _ hP) hisom
    ((hL2.differentiableOn (by simp) _ hP).differentiableAt (hcov.mem_nhds hP))

end GlobalTheory.TorsionForm.Gauge

namespace GlobalTheory.TorsionForm.Gauge

open GlobalTheory.TorsionForm

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ}

theorem heatKernel_transfer {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    {M : Submodule ℤ (Fl g)} {j j' : Fl g → Pt E g → ℂ} {h h' : Pt E g → ℝ} {φ : Pt E g → ℂ}
    (hd : IsDatum B τ M j h) (hd' : IsDatum B τ M j' h') (hiso : IsBundleIso B τ M j j' φ)
    (hisom : IsIsometry B h h' φ) (β : Fin n → E) {b : E} (hb : b ∈ B) {u : ℝ}
    {D : Set (Fl g)}
    {K : ℝ → (Fin g → ℂ) → (Fin g → ℂ) → Ext (n + n + g) →L[ℂ] Ext (n + n + g)}
    (hK : IsHeatKernel τ M j h β b u D K) :
    IsHeatKernel τ M j' h' β b u D (fun t z z' => (φ (b, z) * (φ (b, z'))⁻¹) • K t z z') := by
  obtain ⟨hτ, -, hj, hh⟩ := hd
  obtain ⟨-, -, hj', hh'⟩ := hd'
  have hB : IsOpen B := hτ.1
  have hc : ∀ y, ((b, y) : Pt E g) ∈ cov B g := fun y => ⟨hb, trivial⟩
  have hφ0 : ∀ y, φ (b, y) ≠ 0 := fun y => hiso.2.1 _ (hc y)
  have hφs : ContDiff ℝ ∞ (fun y => φ (b, y)) := phi_slice_contDiff hB hb hiso.1
  have hφi : ContDiff ℝ ∞ (fun y => (φ (b, y))⁻¹) := hφs.inv hφ0
  have hφl : ∀ l ∈ M, ∀ y, φ (b, y + per (τ b) l) * j l (b, y) = j' l (b, y) * φ (b, y) :=
    fun l hl y => hiso.2.2 l hl _ (hc y)
  obtain ⟨hK1, hK2, hK3, hK4⟩ := hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fun a : ℝ × (Fin g → ℂ) × (Fin g → ℂ) =>
        φ (b, a.2.1) * (φ (b, a.2.2))⁻¹) :=
      (hφs.comp (contDiff_fst.comp contDiff_snd)).mul (hφi.comp (contDiff_snd.comp contDiff_snd))
    exact h1.contDiffOn.smul hK1
  · intro t ht l hl z z'
    obtain ⟨e1, e2⟩ := hK2 t ht l hl z z'
    have hj'0 : j' l (b, z') ≠ 0 := (hj'.1 l hl).2 _ (hc z')
    have hA : φ (b, z' + per (τ b) l) ≠ 0 := hφ0 _
    have k1 := hφl l hl z
    have k2 := hφl l hl z'
    constructor
    · simp only [e1, smul_smul]
      congr 1
      linear_combination (φ (b, z'))⁻¹ * k1
    · show j' l (b, z') • ((φ (b, z) * (φ (b, z' + per (τ b) l))⁻¹) • K t z (z' + per (τ b) l)) =
        (φ (b, z) * (φ (b, z'))⁻¹) • K t z z'
      rw [← e2]
      simp only [smul_smul]
      congr 1
      have hinv : (φ (b, z' + per (τ b) l))⁻¹ = j l (b, z') * (j' l (b, z') * φ (b, z'))⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq₀ (mul_ne_zero hj'0 (hφ0 z')), ← k2, inv_mul_cancel_left₀ hA]
      rw [hinv]
      field_simp
  · intro t ht z z' w
    have hKt : ContDiff ℝ ∞ (fun y => K t y z' w) := by
      have : ContDiffOn ℝ ∞ (fun y : Fin g → ℂ => K t y z') univ :=
        hK1.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)).contDiffOn
          (fun y _ => ⟨ht, trivial⟩)
      exact ((ContinuousLinearMap.apply ℂ (Ext (n + n + g)) w).restrictScalars ℝ).contDiff.comp
        (contDiffOn_univ.1 this)
    have hkey := curv_gauge hτ hh.1 hh.2.1 hh'.1 hh'.2.1 hiso.1 hiso.2.1 hisom β u hb
      (f := fun y => (φ (b, z'))⁻¹ • K t y z' w) (hKt.const_smul _) z
    have hlin := curv_const_smul hτ hh.1 hh.2.1 β u hb hKt (φ (b, z'))⁻¹ z
    have hd3 := (hK3 t ht z z' w).const_smul (φ (b, z) * (φ (b, z'))⁻¹)
    simp only [ContinuousLinearMap.smul_apply]
    rw [show (fun y => (φ (b, y) * (φ (b, z'))⁻¹) • K t y z' w) =
        fun y => φ (b, y) • ((φ (b, z'))⁻¹ • K t y z' w) from funext fun y => (smul_smul _ _ _).symm,
      hkey, hlin]
    have e4 : -(φ (b, z) • (φ (b, z'))⁻¹ • curv τ h β b u (fun y => K t y z' w) z) =
        (φ (b, z) * (φ (b, z'))⁻¹) • -curv τ h β b u (fun y => K t y z' w) z := by
      rw [smul_neg, smul_smul]
    rw [e4]
    exact hd3
  · intro f hf
    set f₀ : (Fin g → ℂ) → Ext (n + n + g) := fun y => (φ (b, y))⁻¹ • f y with hf₀def
    have hf₀ : IsSec τ M j b f₀ := by
      refine ⟨hφi.smul hf.1, fun l hl z => ?_⟩
      simp only [hf₀def, hf.2 l hl z, smul_smul]
      congr 1
      have hA : φ (b, z + per (τ b) l) ≠ 0 := hφ0 _
      rw [inv_mul_eq_iff_eq_mul₀ hA, ← mul_assoc, hφl l hl z, mul_assoc, mul_inv_cancel₀ (hφ0 z),
        mul_one]
    have hT := hK4 f₀ hf₀
    have e : (fun t z => ∫ x in D, ((φ (b, z) * (φ (b, per (τ b) x))⁻¹) • K t z (per (τ b) x))
        (f (per (τ b) x))) = fun t z => φ (b, z) • ∫ x in D, K t z (per (τ b) x) (f₀ (per (τ b) x)) := by
      funext t z
      rw [← integral_smul]
      congr 1
      funext x
      simp [hf₀def, smul_smul, map_smul]
    have ef : f = fun z => φ (b, z) • f₀ z := by
      funext z; simp [hf₀def, smul_smul, mul_inv_cancel₀ (hφ0 z)]
    show TendstoLocallyUniformly (fun t z => ∫ x in D, ((φ (b, z) * (φ (b, per (τ b) x))⁻¹) •
      K t z (per (τ b) x)) (f (per (τ b) x))) f (𝓝[>] 0)
    rw [e]
    conv => enter [2]; rw [ef]
    have hc0 : TendstoLocallyUniformly (fun (_ : ℝ) (z : Fin g → ℂ) => φ (b, z))
        (fun z => φ (b, z)) (𝓝[>] 0) :=
      fun s hs x => ⟨univ, univ_mem, .of_forall fun _ _ _ => refl_mem_uniformity hs⟩
    exact hc0.smul₀ hT hφs.continuous hf₀.1.continuous

theorem isometryInv_holds : GlobalTheory.TorsionForm.IsometryInv := by
  intro E _ _ _ g n B τ M j j' h h' φ hd hd' hiso hisom β b hb T hT
  obtain ⟨F, ⟨D, hD, hK⟩, hM⟩ := hT
  refine ⟨F, ⟨D, hD, fun u hu => ?_⟩, hM⟩
  obtain ⟨K, hK, hF⟩ := hK u hu
  refine ⟨_, heatKernel_transfer hd hd' hiso hisom β hb hK, ?_⟩
  rw [hF]
  congr 2
  funext x
  simp [mul_inv_cancel₀ (hiso.2.1 _ (⟨hb, trivial⟩ : ((b, per (τ b) x) : Pt E g) ∈ cov B g))]

end GlobalTheory.TorsionForm.Gauge

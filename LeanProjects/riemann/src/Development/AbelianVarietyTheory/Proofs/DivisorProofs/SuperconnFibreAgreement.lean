import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DBaseApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnSuperconnOfPeriodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnectionBaseFunctionLeibnizStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnectionWedgeAnticommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseDifferentialDualBasisCancelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVanishingLocalProductDecompositionStatement

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff

namespace GlobalTheory.TorsionForm.Fibrewise

open GlobalTheory.TorsionForm.Pullback

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}

theorem L1 (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ)
    (ψ : E → ℂ) (r : Pt E g → Ext (n + n + g)) (P : Pt E g) (hψ : DifferentiableAt ℝ ψ P.1)
    (hr : DifferentiableAt ℝ r P) :
    superconn τ h β u (fun Q => ψ Q.1 • r Q) P =
      ψ P.1 • superconn τ h β u r P + dBase β ψ P.1 (r P) :=
  GlobalTheory.T.superconnection_base_function_leibniz τ h β u ψ r P hψ hr

theorem L2 (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ)
    (k : Fin (n + n + g)) (r : Pt E g → Ext (n + n + g)) (P : Pt E g) (hk : ∀ a, k ≠ dzb n a)
    (hr : DifferentiableAt ℝ r P) :
    superconn τ h β u (fun Q => wedge k (r Q)) P = -wedge k (superconn τ h β u r P) :=
  GlobalTheory.T.superconnection_wedge_anticommute τ h β u k r P hk hr

theorem L3 (β : Fin n → E) (ψ : E → ℂ) (b : E) (w : Ext (n + n + g)) (hψ : ContDiff ℝ 2 ψ) :
    ∑ i, (dBase β (fun b' => d10 ψ b' (β i)) b (wedge (dt g i) w) +
      dBase β (fun b' => d01 ψ b' (β i)) b (wedge (dtb g i) w)) = 0 :=
  GlobalTheory.T.base_differential_dual_basis_cancel β ψ b w hψ

theorem L4 [FiniteDimensional ℂ E] {m : ℕ}
    (B : Set E) (r : Pt E g → Ext m) (hB : IsOpen B) (hr : ContDiffOn ℝ ∞ r (cov B g))
    (b : E) (hb : b ∈ B) (h0 : ∀ z, r (b, z) = 0) (z : Fin g → ℂ) :
    ∃ (N : ℕ) (ψ : Fin N → E → ℂ) (q : Fin N → Pt E g → Ext m), (∀ k, ContDiff ℝ ∞ (ψ k)) ∧
      (∀ k, ψ k b = 0) ∧ (∀ k, ContDiff ℝ ∞ (q k)) ∧
      r =ᶠ[𝓝 (b, z)] fun Q => ∑ k, ψ k Q.1 • q k Q :=
  GlobalTheory.T.smooth_vanishing_local_product_decomposition B r hB hr b hb h0 z

theorem isOpen_cov {B : Set E} (hB : IsOpen B) : IsOpen (cov B g) := hB.prod isOpen_univ

theorem superconn_zero (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E)
    (u : ℝ) (P : Pt E g) : superconn τ h β u (fun _ => (0 : Ext (n + n + g))) P = 0 := by
  simp [superconn, nablaE, dbarV, dbarAdj, pointDifference, d10, d01, connForm_zero, wedge_zero, contr_zero]

theorem superconn_sum (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E)
    (u : ℝ) {ι : Type} (t : Finset ι) (F : ι → Pt E g → Ext (n + n + g)) (P : Pt E g)
    (hF : ∀ k ∈ t, DifferentiableAt ℝ (F k) P) :
    superconn τ h β u (fun Q => ∑ k ∈ t, F k Q) P = ∑ k ∈ t, superconn τ h β u (F k) P := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using superconn_zero τ h β u P
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    have hd : DifferentiableAt ℝ (fun Q => ∑ k ∈ t, F k Q) P :=
      DifferentiableAt.fun_sum fun k hk => hF k (Finset.mem_insert_of_mem hk)
    have e := superconn_add τ h β u (hF a (Finset.mem_insert_self a t)) hd
    beta_reduce at e
    rw [e, ih fun k hk => hF k (Finset.mem_insert_of_mem hk)]

theorem differentiableAt_wedge {m : ℕ} (k : Fin m) {r : Pt E g → Ext m} {P : Pt E g}
    (hr : DifferentiableAt ℝ r P) : DifferentiableAt ℝ (fun Q => wedge k (r Q)) P := by
  unfold wedge
  refine differentiableAt_pi.2 fun S => ?_
  by_cases hk : k ∈ S
  · simp only [hk, if_true]
    exact (differentiableAt_pi.1 hr _).const_mul _
  · simp only [hk, if_false]
    exact differentiableAt_const _

theorem contDiff_d10 (ψ : E → ℂ) (hψ : ContDiff ℝ ∞ ψ) (v : E) :
    ContDiff ℝ ∞ (fun b => d10 ψ b v) := by
  have hf : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
  simp only [d10]
  exact ((hf.clm_apply contDiff_const).sub ((contDiff_const (𝕜 := ℝ) (c := Complex.I)).smul (hf.clm_apply contDiff_const))).const_smul _

theorem contDiff_d01 (ψ : E → ℂ) (hψ : ContDiff ℝ ∞ ψ) (v : E) :
    ContDiff ℝ ∞ (fun b => d01 ψ b v) := by
  have hf : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
  simp only [d01]
  exact ((hf.clm_apply contDiff_const).add ((contDiff_const (𝕜 := ℝ) (c := Complex.I)).smul (hf.clm_apply contDiff_const))).const_smul _

theorem differentiableAt_smul_base {ψ : E → ℂ} {r : Pt E g → Ext (n + n + g)} {P : Pt E g}
    (hψ : DifferentiableAt ℝ ψ P.1) (hr : DifferentiableAt ℝ r P) :
    DifferentiableAt ℝ (fun Q => ψ Q.1 • r Q) P :=
  (hψ.comp P differentiableAt_fst).smul hr

theorem superconn_dBase {B : Set E} (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ)
    (β : Fin n → E) (u : ℝ) (ψ : E → ℂ) (r : Pt E g → Ext (n + n + g)) (P : Pt E g)
    (hψ : ContDiff ℝ ∞ ψ) (hr : DifferentiableAt ℝ r P) :
    superconn τ h β u (fun Q => dBase β ψ Q.1 (r Q)) P =
      -dBase β ψ P.1 (superconn τ h β u r P) +
        ∑ i, (dBase β (fun b' => d10 ψ b' (β i)) P.1 (wedge (dt g i) (r P)) +
          dBase β (fun b' => d01 ψ b' (β i)) P.1 (wedge (dtb g i) (r P))) := by
  have c1 : ∀ j, DifferentiableAt ℝ (fun b => d10 ψ b (β j)) P.1 := fun j =>
    (contDiff_d10 ψ hψ (β j)).differentiable (by simp) _
  have c2 : ∀ j, DifferentiableAt ℝ (fun b => d01 ψ b (β j)) P.1 := fun j =>
    (contDiff_d01 ψ hψ (β j)).differentiable (by simp) _
  have w1 : ∀ j, DifferentiableAt ℝ (fun Q => wedge (dt g j) (r Q)) P := fun j =>
    differentiableAt_wedge _ hr
  have w2 : ∀ j, DifferentiableAt ℝ (fun Q => wedge (dtb g j) (r Q)) P := fun j =>
    differentiableAt_wedge _ hr
  have hdt : ∀ j a, dt g j ≠ dzb n a := fun j a e => by
    have := congrArg Fin.val e; simp [dt, dzb] at this; omega
  have hdtb : ∀ j a, dtb g j ≠ dzb n a := fun j a e => by
    have := congrArg Fin.val e; simp [dtb, dzb] at this; omega
  have e0 := superconn_sum τ h β u Finset.univ
    (fun j Q => d10 ψ Q.1 (β j) • wedge (dt g j) (r Q) + d01 ψ Q.1 (β j) • wedge (dtb g j) (r Q)) P
    (fun j _ => (differentiableAt_smul_base (c1 j) (w1 j)).add (differentiableAt_smul_base (c2 j) (w2 j)))
  rw [show (fun Q => dBase β ψ Q.1 (r Q)) = fun Q => ∑ j, (d10 ψ Q.1 (β j) • wedge (dt g j) (r Q) +
      d01 ψ Q.1 (β j) • wedge (dtb g j) (r Q)) from rfl, e0, dBase_apply β ψ P.1]
  have e1 : ∀ j, superconn τ h β u
      (fun Q => d10 ψ Q.1 (β j) • wedge (dt g j) (r Q) + d01 ψ Q.1 (β j) • wedge (dtb g j) (r Q)) P =
      (d10 ψ P.1 (β j) • -wedge (dt g j) (superconn τ h β u r P) +
        dBase β (fun b' => d10 ψ b' (β j)) P.1 (wedge (dt g j) (r P))) +
      (d01 ψ P.1 (β j) • -wedge (dtb g j) (superconn τ h β u r P) +
        dBase β (fun b' => d01 ψ b' (β j)) P.1 (wedge (dtb g j) (r P))) := by
    intro j
    have e := superconn_add τ h β u (differentiableAt_smul_base (c1 j) (w1 j))
      (differentiableAt_smul_base (c2 j) (w2 j))
    beta_reduce at e
    rw [e, L1 τ h β u _ _ P (c1 j) (w1 j), L1 τ h β u _ _ P (c2 j) (w2 j),
      L2 τ h β u _ r P (hdt j) hr, L2 τ h β u _ r P (hdtb j) hr]
  simp only [e1, smul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  abel

theorem superconn_sq_smul_base {B : Set E} [FiniteDimensional ℂ E] (τ : E → Matrix (Fin g) (Fin g) ℂ)
    (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) (ψ : E → ℂ) (r : Pt E g → Ext (n + n + g))
    (hτ : IsPeriodMap B τ) (hh : ContDiffOn ℝ ∞ h (cov B g)) (hpos : ∀ P ∈ cov B g, 0 < h P)
    (hψ : ContDiff ℝ ∞ ψ) (hr : ContDiffOn ℝ ∞ r (cov B g)) {P : Pt E g} (hP : P ∈ cov B g) :
    superconn τ h β u (superconn τ h β u (fun Q => ψ Q.1 • r Q)) P =
      ψ P.1 • superconn τ h β u (superconn τ h β u r) P := by
  have hO : IsOpen (cov B g) := isOpen_cov hτ.1
  have dr : ∀ Q ∈ cov B g, DifferentiableAt ℝ r Q := fun Q hQ =>
    (hr.contDiffAt (hO.mem_nhds hQ)).differentiableAt (by simp)
  have hBr : ContDiffOn ℝ ∞ (superconn τ h β u r) (cov B g) := GlobalTheory.T.contDiffOn_superconn_of_period B τ h β u r hτ hh hpos hr
  have dBr : DifferentiableAt ℝ (superconn τ h β u r) P :=
    (hBr.contDiffAt (hO.mem_nhds hP)).differentiableAt (by simp)
  have dψ : ∀ b, DifferentiableAt ℝ ψ b := fun b => hψ.differentiable (by simp) b
  have e1 : superconn τ h β u (fun Q => ψ Q.1 • r Q) =ᶠ[𝓝 P]
      fun Q => ψ Q.1 • superconn τ h β u r Q + dBase β ψ Q.1 (r Q) := by
    filter_upwards [hO.mem_nhds hP] with Q hQ
    exact L1 τ h β u ψ r Q (dψ _) (dr Q hQ)
  have dD : DifferentiableAt ℝ (fun Q => dBase β ψ Q.1 (r Q)) P := by
    simp only [dBase_apply]
    exact DifferentiableAt.fun_sum fun j _ =>
      (differentiableAt_smul_base (((contDiff_d10 ψ hψ (β j)).differentiable (by simp)) _)
        (differentiableAt_wedge (dt g j) (dr P hP))).add
      (differentiableAt_smul_base (((contDiff_d01 ψ hψ (β j)).differentiable (by simp)) _)
        (differentiableAt_wedge (dtb g j) (dr P hP)))
  have e2 := superconn_add τ h β u (differentiableAt_smul_base (dψ P.1) dBr) dD
  beta_reduce at e2
  rw [superconn_congr τ h β u e1, e2, L1 τ h β u ψ _ P (dψ _) dBr,
    superconn_dBase (B := B) τ h β u ψ r P hψ (dr P hP), L3 β ψ P.1 (r P) (hψ.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)))]
  abel

theorem main {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) (s s' : Pt E g → Ext (n + n + g)) (hτ : IsPeriodMap B τ) (hh : ContDiffOn ℝ ∞ h (cov B g)) (hpos : ∀ P ∈ cov B g, 0 < h P) (hs : ContDiffOn ℝ ∞ s (cov B g)) (hs' : ContDiffOn ℝ ∞ s' (cov B g)) (b : E) (hb : b ∈ B) (hss : ∀ z, s (b, z) = s' (b, z)) (z : Fin g → ℂ) : superconn τ h β u (superconn τ h β u s) (b, z) = superconn τ h β u (superconn τ h β u s') (b, z) := by
  set P : Pt E g := (b, z) with hPdef
  have hO : IsOpen (cov B g) := isOpen_cov hτ.1
  have hP : P ∈ cov B g := ⟨hb, trivial⟩
  set r : Pt E g → Ext (n + n + g) := fun Q => s Q - s' Q with hrdef
  have hr : ContDiffOn ℝ ∞ r (cov B g) := hs.sub hs'
  have dAt : ∀ {f : Pt E g → Ext (n + n + g)}, ContDiffOn ℝ ∞ f (cov B g) → ∀ Q ∈ cov B g,
      DifferentiableAt ℝ f Q := fun hf Q hQ =>
    (hf.contDiffAt (hO.mem_nhds hQ)).differentiableAt (by simp)
  have sm : ∀ {f : Pt E g → Ext (n + n + g)}, ContDiffOn ℝ ∞ f (cov B g) →
      ContDiffOn ℝ ∞ (superconn τ h β u f) (cov B g) := fun hf =>
    GlobalTheory.T.contDiffOn_superconn_of_period B τ h β u _ hτ hh hpos hf
  have hsplit : s = fun Q => s' Q + r Q := by funext Q; simp [hrdef]
  have eB : superconn τ h β u s =ᶠ[𝓝 P] fun Q => superconn τ h β u s' Q + superconn τ h β u r Q := by
    filter_upwards [hO.mem_nhds hP] with Q hQ
    rw [hsplit]
    exact superconn_add τ h β u (dAt hs' Q hQ) (dAt hr Q hQ)
  have e2 := superconn_add τ h β u (P := P) (dAt (sm hs') P hP) (dAt (sm hr) P hP)
  beta_reduce at e2
  rw [superconn_congr τ h β u eB, e2]
  suffices H : superconn τ h β u (superconn τ h β u r) P = 0 by rw [H, add_zero]
  obtain ⟨N, ψ, q, hψ, hψb, hq, hrq⟩ := L4 B r hτ.1 hr b hb (fun z => by simp [hrdef, hss]) z
  have eBr : superconn τ h β u r =ᶠ[𝓝 P] superconn τ h β u (fun Q => ∑ k, ψ k Q.1 • q k Q) := by
    filter_upwards [hrq.eventuallyEq_nhds] with Q hQ
    exact superconn_congr τ h β u hQ
  have dk : ∀ k Q, DifferentiableAt ℝ (fun Q => ψ k Q.1 • q k Q) Q := fun k Q =>
    differentiableAt_smul_base ((hψ k).differentiable (by simp) _) ((hq k).differentiable (by simp) _)
  have eS : superconn τ h β u (fun Q => ∑ k, ψ k Q.1 • q k Q) =
      fun Q => ∑ k, superconn τ h β u (fun Q => ψ k Q.1 • q k Q) Q := by
    funext Q
    exact superconn_sum τ h β u Finset.univ (fun k Q => ψ k Q.1 • q k Q) Q fun k _ => dk k Q
  have ck : ∀ k, ContDiff ℝ ∞ (fun Q : Pt E g => ψ k Q.1 • q k Q) := fun k =>
    ((hψ k).comp contDiff_fst).smul (hq k)
  rw [superconn_congr τ h β u eBr, eS, superconn_sum τ h β u Finset.univ
    (fun k => superconn τ h β u (fun Q => ψ k Q.1 • q k Q)) P fun k _ =>
    dAt (sm (ck k).contDiffOn) P hP]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [superconn_sq_smul_base τ h β u (ψ k) (q k) hτ hh hpos (hψ k) (hq k).contDiffOn hP]
  simp [hPdef, hψb k]

end GlobalTheory.TorsionForm.Fibrewise

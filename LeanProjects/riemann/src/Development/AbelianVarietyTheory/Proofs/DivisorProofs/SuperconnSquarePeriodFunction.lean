import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothDifferencePeriodDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnBaseSmulLeibnizStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnWedgeAnticommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseCurvatureTermsSumZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnSuperconnStatement

set_option autoImplicit false

noncomputable section

open Matrix Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm.CurvExt

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}

theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top

theorem superconn_zero (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ)
    (P : Pt E g) : superconn τ h β u (fun _ => (0 : Ext (n + n + g))) P = 0 := by
  have e := superconn_add τ h β u (s₁ := fun _ => (0 : Ext (n + n + g)))
    (s₂ := fun _ => (0 : Ext (n + n + g))) (P := P) (differentiableAt_const _) (differentiableAt_const _)
  simp only [add_zero] at e
  exact left_eq_add.mp e

theorem superconn_sum (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ)
    {ι : Type} (s : Finset ι) {F : ι → Pt E g → Ext (n + n + g)} {P : Pt E g}
    (hF : ∀ k ∈ s, DifferentiableAt ℝ (F k) P) :
    superconn τ h β u (fun Q => ∑ k ∈ s, F k Q) P = ∑ k ∈ s, superconn τ h β u (F k) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using superconn_zero τ h β u P
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [superconn_add τ h β u (hF a (Finset.mem_insert_self a s))
      (DifferentiableAt.fun_sum fun k hk => hF k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hF k (Finset.mem_insert_of_mem hk)]

theorem baseD_eq (β : Fin n → E) (φ : E → ℂ) (b : E) (w : Ext (n + n + g)) :
    baseD β φ b w = ∑ i, (d10 φ b (β i) • wedge (dt g i) w + d01 φ b (β i) • wedge (dtb g i) w) := by
  simp only [baseD, wedge_smul]

theorem differentiableAt_wedge {m : ℕ} (k : Fin m) {σ : Pt E g → Ext m} {P : Pt E g}
    (hσ : DifferentiableAt ℝ σ P) : DifferentiableAt ℝ (fun Q => wedge k (σ Q)) P :=
  (((wedgeL k).restrictScalars ℝ).differentiableAt).comp P hσ

theorem differentiableAt_d10 {φ : E → ℂ} {b : E} (hφ : ContDiffAt ℝ 2 φ b) (v : E) :
    DifferentiableAt ℝ (fun b' => d10 φ b' v) b := by
  have hD : DifferentiableAt ℝ (fderiv ℝ φ) b :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold d10
  have h1 : DifferentiableAt ℝ (fun b' => fderiv ℝ φ b' v) b := hD.clm_apply (differentiableAt_const v)
  have h2 : DifferentiableAt ℝ (fun b' => fderiv ℝ φ b' (Complex.I • v)) b :=
    hD.clm_apply (differentiableAt_const _)
  exact (h1.sub (h2.const_smul Complex.I)).const_smul (1 / 2 : ℂ)

theorem differentiableAt_d01 {φ : E → ℂ} {b : E} (hφ : ContDiffAt ℝ 2 φ b) (v : E) :
    DifferentiableAt ℝ (fun b' => d01 φ b' v) b := by
  have hD : DifferentiableAt ℝ (fderiv ℝ φ) b :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold d01
  have h1 : DifferentiableAt ℝ (fun b' => fderiv ℝ φ b' v) b := hD.clm_apply (differentiableAt_const v)
  have h2 : DifferentiableAt ℝ (fun b' => fderiv ℝ φ b' (Complex.I • v)) b :=
    hD.clm_apply (differentiableAt_const _)
  exact (h1.add (h2.const_smul Complex.I)).const_smul (1 / 2 : ℂ)

theorem differentiableAt_baseD (β : Fin n → E) {φ : E → ℂ} {σ : Pt E g → Ext (n + n + g)} {P : Pt E g}
    (hφ : ContDiffAt ℝ 2 φ P.1) (hσ : DifferentiableAt ℝ σ P) :
    DifferentiableAt ℝ (fun Q => baseD β φ Q.1 (σ Q)) P := by
  simp only [baseD_eq]
  refine DifferentiableAt.fun_sum fun i _ => ?_
  exact ((differentiableAt_d10 hφ (β i)).comp P differentiableAt_fst).smul
      (differentiableAt_wedge _ hσ) |>.add
    (((differentiableAt_d01 hφ (β i)).comp P differentiableAt_fst).smul (differentiableAt_wedge _ hσ))

end GlobalTheory.TorsionForm.CurvExt

namespace GlobalTheory.TorsionForm.CurvExt

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}

theorem superconn_baseD (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ)
    {φ : E → ℂ} {σ : Pt E g → Ext (n + n + g)} {P : Pt E g}
    (hφ : ContDiffAt ℝ 2 φ P.1) (hσ : DifferentiableAt ℝ σ P) :
    superconn τ h β u (fun Q => baseD β φ Q.1 (σ Q)) P = -baseD β φ P.1 (superconn τ h β u σ P) := by
  have h10 : ∀ i, DifferentiableAt ℝ (fun Q : Pt E g => d10 φ Q.1 (β i)) P := fun i =>
    (differentiableAt_d10 hφ (β i)).comp P differentiableAt_fst
  have h01 : ∀ i, DifferentiableAt ℝ (fun Q : Pt E g => d01 φ Q.1 (β i)) P := fun i =>
    (differentiableAt_d01 hφ (β i)).comp P differentiableAt_fst
  have ef : (fun Q : Pt E g => baseD β φ Q.1 (σ Q)) = fun Q => ∑ i,
      (d10 φ Q.1 (β i) • wedge (dt g i) (σ Q) + d01 φ Q.1 (β i) • wedge (dtb g i) (σ Q)) := by
    funext Q; exact baseD_eq β φ Q.1 (σ Q)
  rw [ef, superconn_sum τ h β u _ (F := fun i Q => d10 φ Q.1 (β i) • wedge (dt g i) (σ Q) +
      d01 φ Q.1 (β i) • wedge (dtb g i) (σ Q)) fun i _ =>
    ((h10 i).smul (differentiableAt_wedge _ hσ)).add ((h01 i).smul (differentiableAt_wedge _ hσ))]
  have hterm : ∀ i, superconn τ h β u (fun Q => d10 φ Q.1 (β i) • wedge (dt g i) (σ Q) +
        d01 φ Q.1 (β i) • wedge (dtb g i) (σ Q)) P =
      (baseD β (fun b' => d10 φ b' (β i)) P.1 (wedge (dt g i) (σ P)) +
        baseD β (fun b' => d01 φ b' (β i)) P.1 (wedge (dtb g i) (σ P))) -
      (d10 φ P.1 (β i) • wedge (dt g i) (superconn τ h β u σ P) +
        d01 φ P.1 (β i) • wedge (dtb g i) (superconn τ h β u σ P)) := by
    intro i
    rw [superconn_add τ h β u (s₁ := fun Q => d10 φ Q.1 (β i) • wedge (dt g i) (σ Q))
      (s₂ := fun Q => d01 φ Q.1 (β i) • wedge (dtb g i) (σ Q)) ((h10 i).smul (differentiableAt_wedge _ hσ))
      ((h01 i).smul (differentiableAt_wedge _ hσ))]
    rw [GlobalTheory.T.superconn_base_smul_leibniz τ h β u (φ := fun b' => d10 φ b' (β i)) (σ := fun Q => wedge (dt g i) (σ Q))
        (differentiableAt_d10 hφ (β i)) (differentiableAt_wedge _ hσ),
      GlobalTheory.T.superconn_base_smul_leibniz τ h β u (φ := fun b' => d01 φ b' (β i)) (σ := fun Q => wedge (dtb g i) (σ Q))
        (differentiableAt_d01 hφ (β i)) (differentiableAt_wedge _ hσ)]
    rw [show dt g i = (i.castAdd n).castAdd g from rfl, show dtb g i = (i.natAdd n).castAdd g from rfl,
      GlobalTheory.T.superconn_wedge_anticomm τ h β u (i.castAdd n) hσ, GlobalTheory.T.superconn_wedge_anticomm τ h β u (i.natAdd n) hσ]
    simp only [smul_neg]
    abel
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, GlobalTheory.T.base_curvature_terms_sum_zero β hφ (σ P),
    zero_sub, baseD_eq]

end GlobalTheory.TorsionForm.CurvExt

namespace GlobalTheory.TorsionForm.CurvExt

theorem superconn_sq_shift : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}
    [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ →
    ∀ {h : Pt E g → ℝ}, ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) →
    ∀ (β : Fin n → E) (u : ℝ) {ψ : E → Fin g → ℂ}, ContDiffOn ℝ ∞ ψ B → ∀ {b : E}, b ∈ B →
    ∀ {f : (Fin g → ℂ) → Ext (n + n + g)}, ContDiff ℝ ∞ f → ∀ (z : Fin g → ℂ),
    superconn τ h β u (superconn τ h β u fun P => f (P.2 + ψ P.1)) (b, z) =
      superconn τ h β u (superconn τ h β u fun P => f (P.2 + ψ b)) (b, z) := by
  intro E _ _ g n _ B τ hτ h hh hpos β u ψ hψ b hb f hf z
  have hU : IsOpen (cov B g) := hτ.1.prod isOpen_univ
  have hP0 : ((b, z) : Pt E g) ∈ cov B g := Set.mk_mem_prod hb (Set.mem_univ z)
  obtain ⟨φ, σ, hk, hdec⟩ := GlobalTheory.T.smooth_difference_period_decomposition (n := n) hτ.1 hψ hb hf
  have hφb : ∀ k, φ k b = 0 := fun k => (hk k).2.1
  have hφ2 : ∀ k, ContDiffAt ℝ 2 (φ k) b := fun k =>
    ((hk k).1.contDiffAt (hτ.1.mem_nhds hb)).of_le two_le_infty
  have hφd : ∀ k, ∀ b' ∈ B, DifferentiableAt ℝ (φ k) b' := fun k b' hb' =>
    ((hk k).1.contDiffAt (hτ.1.mem_nhds hb')).differentiableAt (by simp)
  have hσd : ∀ k, ∀ P ∈ cov B g, DifferentiableAt ℝ (σ k) P := fun k P hP =>
    ((hk k).2.2.contDiffAt (hU.mem_nhds hP)).differentiableAt (by simp)
  have hsb : ContDiff ℝ ∞ (fun P : Pt E g => f (P.2 + ψ b)) := hf.comp (contDiff_snd.add contDiff_const)
  have hSσ : ∀ k, DifferentiableAt ℝ (superconn τ h β u (σ k)) (b, z) := fun k =>
    ((GlobalTheory.T.contDiffOn_superconn' hτ hh hpos β u (hk k).2.2).contDiffAt (hU.mem_nhds hP0)).differentiableAt (by simp)
  have hSsb : DifferentiableAt ℝ (superconn τ h β u fun P => f (P.2 + ψ b)) (b, z) :=
    ((GlobalTheory.T.contDiffOn_superconn' hτ hh hpos β u hsb.contDiffOn).contDiffAt (hU.mem_nhds hP0)).differentiableAt
      (by simp)
  have inner : ∀ P ∈ cov B g, superconn τ h β u (fun P => f (P.2 + ψ P.1)) P =
      superconn τ h β u (fun P => f (P.2 + ψ b)) P +
        ∑ k, (φ k P.1 • superconn τ h β u (σ k) P + baseD β (φ k) P.1 (σ k P)) := by
    intro P hP
    have e : (fun P : Pt E g => f (P.2 + ψ P.1)) =ᶠ[𝓝 P]
        fun Q => f (Q.2 + ψ b) + ∑ k, φ k Q.1 • σ k Q :=
      Filter.eventually_of_mem (hU.mem_nhds hP) fun Q hQ => by
        show f (Q.2 + ψ Q.1) = f (Q.2 + ψ b) + _
        rw [← hdec Q hQ]; abel
    rw [superconn_congr τ h β u e,
      superconn_add τ h β u (s₁ := fun Q => f (Q.2 + ψ b)) (s₂ := fun Q => ∑ k, φ k Q.1 • σ k Q)
        (hsb.differentiable (by simp) P)
        (DifferentiableAt.fun_sum fun k _ =>
          ((hφd k P.1 hP.1).comp P differentiableAt_fst).smul (hσd k P hP)),
      superconn_sum τ h β u _ (F := fun k Q => φ k Q.1 • σ k Q)
        (fun k _ => ((hφd k P.1 hP.1).comp P differentiableAt_fst).smul (hσd k P hP))]
    congr 1
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.T.superconn_base_smul_leibniz τ h β u (hφd k P.1 hP.1) (hσd k P hP)
  have d1 : ∀ k, DifferentiableAt ℝ (fun Q : Pt E g => φ k Q.1 • superconn τ h β u (σ k) Q) (b, z) :=
    fun k => ((hφd k b hb).comp (b, z) differentiableAt_fst :
      DifferentiableAt ℝ (fun Q : Pt E g => φ k Q.1) (b, z)).smul (hSσ k)
  have d2 : ∀ k, DifferentiableAt ℝ (fun Q : Pt E g => baseD β (φ k) Q.1 (σ k Q)) (b, z) :=
    fun k => differentiableAt_baseD β (hφ2 k) (hσd k _ hP0)
  have e2 : superconn τ h β u (fun P => f (P.2 + ψ P.1)) =ᶠ[𝓝 ((b, z) : Pt E g)]
      fun Q => superconn τ h β u (fun P => f (P.2 + ψ b)) Q +
        ∑ k, (φ k Q.1 • superconn τ h β u (σ k) Q + baseD β (φ k) Q.1 (σ k Q)) :=
    Filter.eventually_of_mem (hU.mem_nhds hP0) inner
  rw [superconn_congr τ h β u e2,
    superconn_add τ h β u (s₁ := superconn τ h β u fun P => f (P.2 + ψ b))
      (s₂ := fun Q => ∑ k, (φ k Q.1 • superconn τ h β u (σ k) Q + baseD β (φ k) Q.1 (σ k Q)))
      hSsb (DifferentiableAt.fun_sum fun k _ => (d1 k).add (d2 k)),
    superconn_sum τ h β u _
      (F := fun k Q => φ k Q.1 • superconn τ h β u (σ k) Q + baseD β (φ k) Q.1 (σ k Q))
      (fun k _ => (d1 k).add (d2 k))]
  rw [Finset.sum_eq_zero fun k _ => ?_, add_zero]
  rw [superconn_add τ h β u (s₁ := fun Q => φ k Q.1 • superconn τ h β u (σ k) Q)
      (s₂ := fun Q => baseD β (φ k) Q.1 (σ k Q)) (d1 k) (d2 k),
    GlobalTheory.T.superconn_base_smul_leibniz τ h β u (hφd k b hb) (hSσ k),
    superconn_baseD τ h β u (hφ2 k) (hσd k _ hP0)]
  simp [hφb k]

end GlobalTheory.TorsionForm.CurvExt

import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_JA_LocLemmas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjCont
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfExhaustOfAvgCutoff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableGerm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGCut

open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem theta_transfer_on_function : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (D : RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ) (F : Mat k r → (Wq →L[ℂ] Wp)) (Θ : DiffOp k r Wp Wq)
    (UU : Set (Mat k r)), UU ⊆ Om k r D.z D.z' → opOrder Θ ≤ m → Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A m → InCC A m F →
    (∀ p, D.inSS p → ∀ g ∈ UU, opApply Θ (rho D p F) g = rho D p (opApply Θ F) g) →
    ∀ g ∈ UU, opApply Θ (JF D F) g = JF D (opApply Θ F) g := by
  intro k r Wp Wq _ _ _ _ _ _ D A m F Θ UU hUU ho hT hF hC g hgU
  have hg : g ∈ Om k r D.z D.z' := hUU hgU
  have hW := Formalism.FourierDecayAlt.P.WeakDominationWordBounds.orbital_derivative_words_weak
  have hR := Formalism.FourierDecayAlt.P.rewrite_rho_action
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  have hgG : g ∈ GV k r := hg.1
  have key : ∀ T ∈ Θ, Integrable (fun p => xiP D p • Rw T.word (rho D p F) g) D.μSS ∧
      Rw T.word (JF D F) g = ∫ p, xiP D p • Rw T.word (rho D p F) g ∂D.μSS := by
    intro T hT'
    have hvl : T.word.length ≤ m := (B5.len_le_order Θ hT').trans ho
    set v' := T.word.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X with hv'
    have hv'u : ∀ X ∈ v', unitLie k r X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact B4.nrm_unit (x := (false, Y)) (T.word_lie Y hY)
    have hv'l : v'.length ≤ m := by rw [hv', List.length_map]; exact hvl
    obtain ⟨hI, hE⟩ := (hW k r Wp Wq D A m F hT hF).2 [] v' (by simp) hv'u (by simpa using hv'l) g hg
    simp only [List.map_nil] at hI hE
    have hae : (fun p => xiP D p • rho D p (dLR [] (v'.map (AdR p)) F) g) =ᵐ[D.μSS]
        fun p => xiP D p • Rw v' (rho D p F) g := by
      filter_upwards [B5.ae_inSS D] with p hp
      have := hR k r Wp Wq D m F p hp hCk [] v' (by simp) (fun X hX => (hv'u X hX).1) (by simpa using hv'l) g hgG
      simp only [List.map_nil] at this
      rw [← this]
      rfl
    have hI' : Integrable (fun p => xiP D p • Rw v' (rho D p F) g) D.μSS := hI.congr hae
    have hfun : (fun p => xiP D p • Rw T.word (rho D p F) g) =
        fun p => (B4.pn (B4.lr [] T.word) : ℝ) • (xiP D p • Rw v' (rho D p F) g) := by
      funext p
      rw [WordIntegralScaling.rw_scale T.word (rho D p F), Pi.smul_apply, smul_comm]
    refine ⟨?_, ?_⟩
    · rw [hfun]; exact hI'.smul (B4.pn (B4.lr [] T.word))
    · rw [WordIntegralScaling.rw_scale T.word (JF D F), Pi.smul_apply, hfun, integral_smul]
      congr 1
      rw [← integral_congr_ae hae]
      exact hE
  have hCo : CkOn (opOrder Θ : ℕ∞) (GV k r) F := B5.ckOn_mono (by exact_mod_cast ho) hCk
  have hRHS : JF D (opApply Θ F) g = ∫ p, xiP D p • opApply Θ (rho D p F) g ∂D.μSS := by
    show (∫ p, xiP D p • rho D p (opApply Θ F) g ∂D.μSS) = _
    refine integral_congr_ae ?_
    filter_upwards [B5.ae_inSS D] with p hp
    rw [hC p hp g hgU]
  rw [hRHS]
  unfold opApply
  simp only [WordIntegralScaling.smul_list]
  obtain ⟨_, hsum⟩ := WordIntegralScaling.int_list D.μSS Θ (fun T => T.coef g)
    (fun T p => xiP D p • Rw T.word (rho D p F) g) fun T hT' => (key T hT').1
  rw [hsum]
  congr 1
  refine List.map_congr_left fun T hT' => ?_
  rw [(key T hT').2]

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.CutMP.JA.LT

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section adj

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem opAdj_local (Θ : B.DiffOp k r Wp Wq) {U : Set (B.Mat k r)} (hU : IsOpen U) {f f' : B.Mat k r → (Wq →L[ℂ] Wp)}
    (he : ∀ x ∈ U, x ∈ B.GV k r → f x = f' x) : ∀ g ∈ U, g ∈ B.GV k r → B.opAdj Θ f g = B.opAdj Θ f' g := by
  intro g hg hgG
  unfold B.opAdj
  congr 1
  refine List.map_congr_left fun T _ => ?_
  rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.rw_local T.word.reverse (fun X hX => T.word_lie X (List.mem_reverse.1 hX)) hU
    (f := fun x => T.coefAdj x (f x)) (f' := fun x => T.coefAdj x (f' x))
    (fun x hx hxG => by simp only [he x hx hxG]) g hg hgG]

theorem adjComm_at (hAC : Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AdjComm) (D : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq)
    (hSC : B.SmoothCoef (B.GPos D) Θ) (hC : B.Commutes D (B.GPos D) Θ) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hF : B.CkOn ⊤ (B.GV k r) F) (p : B.SS k r) (hp : D.inSS p) (g : B.Mat k r) (hg : g ∈ B.GPos D) :
    B.opAdj Θ (B.rho D p F) g = B.rho D p (B.opAdj Θ F) g := by
  set y := B.sgs p g with hy
  have hyG : y ∈ B.GV k r := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_GV D hp hg.1
  have hyP : 0 < Gf k r D.z D.z' y := by
    rw [hy, Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC.gf_sgs D hp g]; exact hg.2
  have hWo : IsOpen {x : B.Mat k r | 0 < Gf k r D.z D.z' x} := isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.BetaSesquilinearity.Gf_cont _ _)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hWo y hyP
  have hbx : ∃ b : ContDiffBump y, b.rIn = ε / 4 ∧ b.rOut = ε / 2 := ⟨⟨ε / 4, ε / 2, by positivity, by linarith⟩, rfl, rfl⟩
  obtain ⟨b, hbi, hbo⟩ := hbx
  set f₁ : B.Mat k r → (Wq →L[ℂ] Wp) := fun x => ((b x : ℝ) : ℂ) • F x with hf₁
  have hbc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ((b x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hf₁C : B.CkOn ⊤ (B.GV k r) f₁ := Formalism.FourierDecayAlt.P.CutMP.JA.gcut_ckOn_smul hbc hF
  have hf₁cs : HasCompactSupport f₁ := by
    have h0 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) := b.hasCompactSupport.comp_left Complex.ofReal_zero
    exact h0.smul_right
  have hf₁S : B.SuppIn (B.GPos D) f₁ := by
    have hcl : IsClosed (Metric.closedBall y (ε / 2) ∩ B.GV k r) := Metric.isClosed_closedBall.inter Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_closed
    refine (closure_minimal (fun x (hx : x ∈ B.GV k r ∧ f₁ x ≠ 0) => ?_) hcl).trans ?_
    · refine ⟨?_, hx.1⟩
      by_contra hxb
      apply hx.2
      have : b x = 0 := by
        apply b.zero_of_le_dist
        rw [Metric.mem_closedBall, not_le] at hxb
        rw [hbo]; exact hxb.le
      simp [hf₁, this]
    · intro x hx
      refine ⟨hx.2, hball ?_⟩
      have := hx.1
      rw [Metric.mem_closedBall] at this
      rw [Metric.mem_ball]
      linarith
  have hmain := hAC k r Wp Wq D Θ hSC hC f₁ hf₁C hf₁cs hf₁S p hp g hg
  have hone : ∀ x ∈ Metric.ball y (ε / 4), f₁ x = F x := by
    intro x hx
    have : b x = 1 := b.one_of_mem_closedBall (by rw [hbi]; exact Metric.ball_subset_closedBall hx)
    simp [hf₁, this]
  have hL : B.opAdj Θ (B.rho D p f₁) g = B.opAdj Θ (B.rho D p F) g := by
    have hgV : g ∈ B.sgs p ⁻¹' Metric.ball y (ε / 4) := by
      rw [Set.mem_preimage, ← hy]; exact Metric.mem_ball_self (by positivity)
    have hVo : IsOpen (B.sgs p ⁻¹' Metric.ball y (ε / 4)) :=
      Metric.isOpen_ball.preimage (Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC.sgs_continuous p)
    refine opAdj_local Θ hVo (fun x hx _ => ?_) g hgV hg.1
    have hx' : B.sgs p x ∈ Metric.ball y (ε / 4) := hx
    unfold B.rho
    rw [hone _ hx']
  have hR : B.opAdj Θ f₁ y = B.opAdj Θ F y :=
    opAdj_local Θ Metric.isOpen_ball (fun x hx _ => hone x hx) y (Metric.mem_ball_self (by positivity)) hyG
  rw [← hL, hmain]
  unfold B.rho
  rw [← hy, hR]

end adj

theorem thetaJ_apply {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hT : Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A (B.opOrder Θ)) (hC : B.Commutes Bs (B.GPos Bs) Θ) (hFA : B.InCC A (B.opOrder Θ) F) :
    ∀ g ∈ JF.Om k r Bs.z Bs.z', B.opApply Θ (B.JF Bs F) g = B.JF Bs (B.opApply Θ F) g := by
  have hOmG : JF.Om k r Bs.z Bs.z' ⊆ B.GPos Bs := jdc_om_sub_gpos Bs
  have hCOm : B.Commutes Bs (JF.Om k r Bs.z Bs.z') Θ := fun p hp f' hf' g hg => hC p hp f' hf' g (hOmG hg)
  exact fun g hg => Formalism.FourierDecayAlt.P.orbital_commutes_on_open_set _ _ _ _ Bs A (B.opOrder Θ) F Θ _ subset_rfl le_rfl hT hFA hCOm g hg

theorem theta_transfer_apply_holds : ThetaJApply := by
  intro k r Wp Wq _ _ _ _ _ _ Bs Θ A F hT _hS hC _hF hI
  exact thetaJ_apply Bs Θ A F hT hC hI

theorem thetaJ_of_adjComm (hAC : Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AdjComm) : ThetaJ := by
  intro k r Wp Wq _ _ _ _ _ _ Bs Θ A F UU hT hSC hC hF hFA hUU _hCk
  have hOmG : JF.Om k r Bs.z Bs.z' ⊆ B.GPos Bs := jdc_om_sub_gpos Bs
  have hCOm : B.Commutes Bs (JF.Om k r Bs.z Bs.z') Θ := fun p hp f' hf' g hg => hC p hp f' hf' g (hOmG hg)
  refine ⟨fun g hg => Formalism.FourierDecayAlt.P.orbital_commutes_on_open_set _ _ _ _ Bs A (B.opOrder Θ) F Θ _ subset_rfl le_rfl hT hFA hCOm g hg, ?_⟩
  intro g hgU
  have hg : g ∈ JF.Om k r Bs.z Bs.z' := hUU hgU
  have hSCo : B.SmoothCoef (JF.Om k r Bs.z Bs.z') Θ := fun T hT' =>
    ⟨Formalism.FourierDecayAlt.P.JFxI.ckOn_sub hOmG (hSC T hT').1, Formalism.FourierDecayAlt.P.JFxI.ckOn_sub hOmG (hSC T hT').2⟩
  obtain ⟨Θ', hord, hrep⟩ := Formalism.FourierDecayAlt.P.adjoint_leibniz_expansion k r Wp Wq Bs Θ hSCo
  have hsub := Formalism.FourierDecayAlt.P.JFxI.om_sub_gv (k := k) (r := r) Bs.z Bs.z'
  have hFm : B.CkOn (B.opOrder Θ : ℕ∞) (JF.Om k r Bs.z Bs.z') F :=
    Formalism.FourierDecayAlt.P.JFxI.ckOn_sub hsub (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF)
  have e1 : B.JF Bs (B.opAdj Θ F) g = B.JF Bs (B.opApply Θ' F) g := by
    change ∫ p, JF.xiP Bs p • B.rho Bs p (B.opAdj Θ F) g ∂Bs.μSS = ∫ p, JF.xiP Bs p • B.rho Bs p (B.opApply Θ' F) g ∂Bs.μSS
    apply integral_congr_ae
    filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
    have hx' := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om Bs hp hg
    unfold B.rho
    rw [hrep F hFm _ hx']
  have hCF : ∀ p, Bs.inSS p → ∀ x ∈ JF.Om k r Bs.z Bs.z',
      B.opApply Θ' (B.rho Bs p F) x = B.rho Bs p (B.opApply Θ' F) x := by
    intro p hp x hx
    have hρ : B.CkOn (B.opOrder Θ : ℕ∞) (JF.Om k r Bs.z Bs.z') (B.rho Bs p F) :=
      Formalism.FourierDecayAlt.P.JFxI.ckOn_sub hsub (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top (Formalism.FourierDecayAlt.P.B5.ckOn_rho Bs hp hF))
    rw [hrep _ hρ x hx, adjComm_at hAC Bs Θ hSC hC F hF p hp x (hOmG hx)]
    have hx' := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om Bs hp hx
    unfold B.rho
    rw [hrep F hFm _ hx']
  have e2 := Formalism.FourierDecayAlt.P.theta_transfer_on_function k r Wp Wq Bs A (B.opOrder Θ) F Θ' _ subset_rfl (le_of_eq hord) hT hFA hCF g hg
  have hW := (Formalism.FourierDecayAlt.P.WeakDominationWordBounds.orbital_derivative_words_weak k r Wp Wq Bs A (B.opOrder Θ) F hT hFA).1
  have hJck : B.CkOn (B.opOrder Θ : ℕ∞) (JF.Om k r Bs.z Bs.z') (B.JF Bs F) := by
    intro g₀ hg₀
    obtain ⟨U, F', a, b, c, d⟩ := hW g₀ ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g₀).2 hg₀.1, hg₀.2⟩
    exact ⟨U, F', a, b, by exact_mod_cast c, fun x hx hxG => d x hx ((Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 x).2 hxG)⟩
  rw [e1, ← e2, hrep _ hJck g hg]

end Formalism.FourierDecayAlt.P.CutMP.JA.LT

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftCapelliOperators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations

namespace GlobalTheory.HatNF.SmoothLift

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF MeasureTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem opApply_JF (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (Θ : B.DiffOp k r Wp Wq) (ho : B.opOrder Θ ≤ m) (hT : TransportedAlt k r A m) (hF : B.InCC A m F)
    (g : B.Mat k r) (hg : g ∈ Om k r D.z D.z')
    (hC : ∀ p, D.inSS p → opApply Θ (rho D p F) g = rho D p (opApply Θ F) g) :
    B.opApply Θ (B.JF D F) g = B.JF D (B.opApply Θ F) g := by
  have hW := jacquet_derivative_formula
  have hR := rewrite_rho_action
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
  have hRHS : JF D (opApply Θ F) g = ∫ p, xiP D p • opApply Θ (rho D p F) g ∂D.μSS := by
    show (∫ p, xiP D p • rho D p (opApply Θ F) g ∂D.μSS) = _
    refine integral_congr_ae ?_
    filter_upwards [B5.ae_inSS D] with p hp
    rw [hC p hp]
  rw [hRHS]
  unfold opApply
  simp only [WordIntegralScaling.smul_list]
  obtain ⟨_, hsum⟩ := WordIntegralScaling.int_list D.μSS Θ (fun T => T.coef g)
    (fun T p => xiP D p • Rw T.word (rho D p F) g) fun T hT' => (key T hT').1
  rw [hsum]
  congr 1
  refine List.map_congr_left fun T hT' => ?_
  rw [(key T hT').2]

theorem polyLift_of_smooth_comm (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (o κ : ℕ)
    (Θ : B.DiffOp P.k P.r Wp Wq) (a : RA P Bs) (hP : CutMP.PolyOp o κ Θ)
    (hC : ∀ p, Bs.inSS p → ∀ f : B.Mat P.k P.r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV P.k P.r) f →
      ∀ g ∈ B.GPos Bs, B.opApply Θ (B.rho Bs p f) g = B.rho Bs p (B.opApply Θ f) g)
    (hres : ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Q.OmPlus P.k P.r Bs.z Bs.z'),
      ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = Q.resG P.k P.r (Fin.last P.r) J x.1 x.2) →
      ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', (a.1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
        Q.resG P.k P.r (Fin.last P.r) (B.opApply Θ J) x.1 x.2) :
    PolyLift P Bs o κ a := by
  refine ⟨Θ, hP, fun F hF Φ hΦ x hx => ?_⟩
  obtain ⟨ε, hε, hN⟩ := (compact_support_facts P.k P.r Wp Wq Bs F hF).1
  have hJ := bessel_function_finite_class P.k P.r Wp Wq Bs F ε hε hN
  rw [hres _ hJ Φ hΦ x hx]
  have hom : Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2 ∈ Om P.k P.r Bs.z Bs.z' :=
    ⟨TLB.wCell_gv Bs hx, P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hx.1 hx.2.1 hx.2.2⟩
  simp only [Q.resG]
  rw [opApply_JF Bs _ (B.opOrder Θ) F Θ le_rfl (JFxG.thr_big P.k P.r (B.opOrder Θ)) (hN.2.1 _ _) _ hom
    (fun p hp => hC p hp F hF.1 _ ⟨hom.1, hom.2.2⟩)]

end GlobalTheory.HatNF.SmoothLift

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionPullbackDifferentiableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaPieceSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarPlusAdjointSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorialPullbackDifferentiableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorialFormPullbackSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondDerivativeHolomorphicSymmStatement

set_option autoImplicit false

noncomputable section

open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff

namespace GlobalTheory.TorsionForm.PullbackMain

theorem slice_contDiff {m g : ℕ} {K : ℝ → (Fin g → ℂ) → (Fin g → ℂ) → Ext m →L[ℂ] Ext m}
    (hK : ContDiffOn ℝ ∞ (fun a : ℝ × (Fin g → ℂ) × (Fin g → ℂ) => K a.1 a.2.1 a.2.2) (Ioi 0 ×ˢ univ))
    {t : ℝ} (ht : 0 < t) (z' : Fin g → ℂ) (w : Ext m) : ContDiff ℝ ∞ (fun y => K t y z' w) := by
  have h1 : ContDiff ℝ ∞ (fun y : Fin g → ℂ => K t y z') :=
    hK.comp_contDiff (f := fun y : Fin g → ℂ => ((t, y, z') : ℝ × (Fin g → ℂ) × (Fin g → ℂ)))
      (by fun_prop) (fun y => ⟨ht, trivial⟩)
  exact ((ContinuousLinearMap.apply ℂ (Ext m) w).restrictScalars ℝ).contDiff.comp h1

theorem curv_pullback {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E'] {g n : ℕ} {B : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ} {h : Pt E g → ℝ}
    (hτ : IsPeriodMap B τ) (hh : ContDiffOn ℝ ∞ h (cov B g)) (hpos : ∀ P ∈ cov B g, 0 < h P)
    {B' : Set E'} {φ : E' → E} (hB' : IsOpen B') (hφ : DifferentiableOn ℂ φ B') (hmap : MapsTo φ B' B)
    (β : Fin n → E') {b : E'} (hb : b ∈ B') (u : ℝ) {f : (Fin g → ℂ) → Ext (n + n + g)}
    (hf : ContDiff ℝ ∞ f) (z : Fin g → ℂ) :
    curv (τ ∘ φ) (fun P => h (φ P.1, P.2)) β b u f z =
      curv τ h (fun i => fderiv ℂ φ b (β i)) (φ b) u f z := by
  classical
  set β'' : Fin n → E := fun i => fderiv ℂ φ b (β i) with hβ''
  set s0 : Pt E g → Ext (n + n + g) := fun Q => f Q.2 with hs0def
  set s1 := superconn τ h β'' u s0 with hs1def
  set R : Pt E' g → Ext (n + n + g) := fun P =>
    ∑ i, nabPiece τ h s0 (φ P.1, P.2) i (fderiv ℂ φ P.1 (β i) - fderiv ℂ φ b (β i)) with hRdef
  have hopen : IsOpen (cov B g) := hτ.1.prod isOpen_univ
  have hmem : ∀ P : Pt E' g, P.1 ∈ B' → ((φ P.1, P.2) : Pt E g) ∈ cov B g :=
    fun P hP => ⟨hmap hP, trivial⟩
  have hτd : ∀ c ∈ B, ∀ i j, DifferentiableAt ℂ (fun b => τ b i j) c :=
    fun c hc i j => (hτ.2.1 i j).differentiableAt (hτ.1.mem_nhds hc)
  have hφd : ∀ c ∈ B', DifferentiableAt ℂ φ c := fun c hc => hφ.differentiableAt (hB'.mem_nhds hc)
  have hdiff : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {F : Pt E g → W},
      ContDiffOn ℝ ∞ F (cov B g) → ∀ Q ∈ cov B g, DifferentiableAt ℝ F Q :=
    fun hF Q hQ => (hF.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hQ)
  have hs0 : ContDiffOn ℝ ∞ s0 (cov B g) := (hf.comp contDiff_snd).contDiffOn
  have hs1 : ContDiffOn ℝ ∞ s1 (cov B g) := by
    have e : s1 = fun Q => ∑ i, nabPiece τ h s0 Q i (β'' i) +
        (Real.sqrt u : ℂ) • (dbarV s0 Q + dbarAdj τ h s0 Q) := rfl
    rw [e]
    exact (ContDiffOn.sum fun i _ => GlobalTheory.T.nabla_piece_smooth B τ h s0 hτ hh hpos hs0 i (β'' i)).add
      ((GlobalTheory.T.dbar_plus_adjoint_smooth B τ h s0 hτ hh hpos hs0).const_smul _)
  have step1 : ∀ P : Pt E' g, P.1 ∈ B' →
      superconn (τ ∘ φ) (fun P => h (φ P.1, P.2)) β u (fun P => f P.2) P = s1 (φ P.1, P.2) + R P := by
    intro P hP
    have := GlobalTheory.T.connection_pullback_differentiable τ h φ β u s0 P (hφd _ hP) (hτd _ (hmap hP)) (hdiff hh _ (hmem P hP))
      (hpos _ (hmem P hP)).ne' (hdiff hs0 _ (hmem P hP))
    rw [show (fun P : Pt E' g => f P.2) = fun Q => s0 (φ Q.1, Q.2) from rfl, this]
    have e : (fun i => fderiv ℂ φ P.1 (β i)) =
        fun i => β'' i + (fderiv ℂ φ P.1 (β i) - fderiv ℂ φ b (β i)) := by
      funext i; simp [β'']
    rw [e, superconn_add_vec]
  have hev : superconn (τ ∘ φ) (fun P => h (φ P.1, P.2)) β u (fun P => f P.2) =ᶠ[𝓝 (b, z)]
      fun P => s1 (φ P.1, P.2) + R P := by
    filter_upwards [(hB'.prod isOpen_univ).mem_nhds
      (show (b, z) ∈ B' ×ˢ (univ : Set (Fin g → ℂ)) from ⟨hb, trivial⟩)] with P hP using step1 P hP.1
  have hφev : ∀ᶠ c in 𝓝 b, DifferentiableAt ℂ φ c := by
    filter_upwards [hB'.mem_nhds hb] with c hc using hφd c hc
  have hC1 := GlobalTheory.T.tensorial_pullback_differentiable (fun i Q v => nabPiece τ h s0 Q i v) φ β b z
    (fun i Q => isLinearMap_nabPiece τ h s0 Q i)
    (fun i v => hdiff (GlobalTheory.T.nabla_piece_smooth B τ h s0 hτ hh hpos hs0 i v) _ (hmem (b, z) hb)) hφev
  have hRd : DifferentiableAt ℝ R (b, z) := hC1.1
  have hRf : ∀ w : Pt E' g, fderiv ℝ R (b, z) w = ∑ i, (wedge (dt g i)
      (nabHol τ h s0 (φ b, z) (fderiv ℂ (fun c => fderiv ℂ φ c (β i)) b w.1)) +
      wedge (dtb g i) (nabAnti τ s0 (φ b, z) (fderiv ℂ (fun c => fderiv ℂ φ c (β i)) b w.1))) :=
    hC1.2
  have hR0 : R (b, z) = 0 := by simp [R, nabPiece_zero]
  have hΦ : DifferentiableAt ℝ (fun P : Pt E' g => ((φ P.1, P.2) : Pt E g)) (b, z) :=
    (((hφd b hb).restrictScalars ℝ).comp _ differentiableAt_fst).prodMk differentiableAt_snd
  have hs1Φ : DifferentiableAt ℝ (fun P : Pt E' g => s1 (φ P.1, P.2)) (b, z) :=
    DifferentiableAt.comp (g := s1) (f := fun P : Pt E' g => ((φ P.1, P.2) : Pt E g)) (b, z)
      (hdiff hs1 _ (hmem (b, z) hb)) hΦ
  have hψ : ∀ i k, fderiv ℂ (fun c => fderiv ℂ φ c (β i)) b (β k) =
      fderiv ℂ (fun c => fderiv ℂ φ c (β k)) b (β i) := fun i k => GlobalTheory.T.second_derivative_holomorphic_symm φ b (β i) (β k) hφev
  unfold curv
  rw [superconn_congr _ _ _ _ hev, superconn_add _ _ _ _ hs1Φ hRd,
    GlobalTheory.T.connection_pullback_differentiable τ h φ β u s1 (b, z) (hφd _ hb) (hτd _ (hmap hb)) (hdiff hh _ (hmem _ hb))
      (hpos _ (hmem _ hb)).ne' (hdiff hs1 _ (hmem _ hb)),
    GlobalTheory.T.tensorial_form_pullback_split (τ ∘ φ) (fun P => h (φ P.1, P.2)) β u R (b, z) (nabHol τ h s0 (φ b, z))
      (nabAnti τ s0 (φ b, z)) (fun i => fderiv ℂ (fun c => fderiv ℂ φ c (β i)) b)
      (nabHol_add τ h s0 _) (nabHol_I τ h s0 _) (nabAnti_add τ s0 _) (nabAnti_I τ s0 _) hψ hR0 hRf,
    add_zero]

theorem baseChange : BaseChange := by
  intro E E' _ _ _ _ _ _ g n B τ M j h hD B' φ hB' hφ hmap β b hb T
  have key : ∀ u D K, IsHeatKernel (τ ∘ φ) M (fun l P => j l (φ P.1, P.2))
      (fun P => h (φ P.1, P.2)) β b u D K ↔
      IsHeatKernel τ M j h (fun i => fderiv ℂ φ b (β i)) (φ b) u D K := by
    intro u D K
    have hc : ∀ t, 0 < t → ∀ z' w z, ContDiffOn ℝ ∞
        (fun a : ℝ × (Fin g → ℂ) × (Fin g → ℂ) => K a.1 a.2.1 a.2.2) (Ioi 0 ×ˢ univ) →
        curv (τ ∘ φ) (fun P => h (φ P.1, P.2)) β b u (fun y => K t y z' w) z =
          curv τ h (fun i => fderiv ℂ φ b (β i)) (φ b) u (fun y => K t y z' w) z :=
      fun t ht z' w z hK => curv_pullback hD.1 hD.2.2.2.1 hD.2.2.2.2.1 hB' hφ hmap β hb u
        (slice_contDiff hK ht z' w) z
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, fun t ht z z' w => by rw [← hc t ht z' w z h1]; exact h3 t ht z z' w, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, fun t ht z z' w => by rw [hc t ht z' w z h1]; exact h3 t ht z z' w, h4⟩
  unfold IsTorsionForm IsHeatTrace
  simp only [key]
  exact Iff.rfl

end GlobalTheory.TorsionForm.PullbackMain

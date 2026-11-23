import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousCosSqAngleFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLinePullbackForm
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CosSqSmooth

open TopologicalSpace Filter Topology
open scoped ComplexOrder ContDiff

def ratio (M : Fin 2 → Fin 2 → ℂ) : ℝ := ‖M 0 1‖ ^ 2 / ((M 1 1).re * (M 0 0).re)

theorem contDiffAt_ratio {M : Fin 2 → Fin 2 → ℂ} (hM : (M 1 1).re * (M 0 0).re ≠ 0) :
    ContDiffAt ℝ ∞ ratio M := by
  have a : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun N : Fin 2 → Fin 2 → ℂ => N i j) := fun i j =>
    (contDiff_apply ℝ ℂ j).comp (contDiff_apply ℝ (Fin 2 → ℂ) i)
  have re : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun N : Fin 2 → Fin 2 → ℂ => (N i j).re) := fun i j =>
    Complex.reCLM.contDiff.comp (a i j)
  exact ((contDiff_norm_sq ℝ).comp (a 0 1)).contDiffAt.div
    ((re 1 1).mul (re 0 0)).contDiffAt hM

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem vInfAt_of_isCosSq {V L L' : X.Modules} {r : ℕ} {m : Met p σ V r} (H : m.IsCInf)
    {l : L ⟶ V} {l' : L' ⟶ V} {v : CxPts p σ → ℝ} (hv : CurveDens.IsCosSq m l l' v)
    {U₁ U₂ : X.Opens} (t₁ : Γ(L, U₁)) (t₂ : Γ(L', U₂)) {y : CxPts p σ}
    (hy₁ : y ∈ ptsIn p σ U₁) (hy₂ : y ∈ ptsIn p σ U₂)
    (hp₁ : 0 < (m.form (l.app U₁ t₁) (l.app U₁ t₁) y).re)
    (hp₂ : 0 < (m.form (l'.app U₂ t₂) (l'.app U₂ t₂) y).re) :
    VInfAt v y ∧ 0 ≤ v y ∧ v y ≤ 1 := by
  have hy : y ∈ ptsIn p σ (U₁ ⊓ U₂) := mem_ptsIn_inf.2 ⟨hy₁, hy₂⟩
  set u₁ := Twist.resM _ (inf_le_left : U₁ ⊓ U₂ ≤ U₁) t₁
  set u₂ := Twist.resM _ (inf_le_right : U₁ ⊓ U₂ ≤ U₂) t₂
  set s₁ := l.app _ u₁
  set s₂ := l'.app _ u₂
  have e₁ : m.form s₁ s₁ y = m.form (l.app U₁ t₁) (l.app U₁ t₁) y := by
    simp only [s₁, u₁]; rw [Twist.app_resM, m.form_resM _ _ _ hy]
  have e₂ : m.form s₂ s₂ y = m.form (l'.app U₂ t₂) (l'.app U₂ t₂) y := by
    simp only [s₂, u₂]; rw [Twist.app_resM, m.form_resM _ _ _ hy]
  have q₁ : 0 < (m.form s₁ s₁ y).re := by rw [e₁]; exact hp₁
  have q₂ : 0 < (m.form s₂ s₂ y).re := by rw [e₂]; exact hp₂
  have hG := H.gram ![s₂, s₁] hy
  have c₁ : ContinuousAt (fun z => (m.form s₁ s₁ z).re) y :=
    Complex.continuous_re.continuousAt.comp (hG 1 1).continuousAt
  have c₂ : ContinuousAt (fun z => (m.form s₂ s₂ z).re) y :=
    Complex.continuous_re.continuousAt.comp (hG 0 0).continuousAt
  have key : v =ᶠ[𝓝 y] fun z => ratio (fun a b => m.gram ![s₂, s₁] z a b) := by
    filter_upwards [(isOpen_ptsIn _).mem_nhds hy, c₁.eventually (lt_mem_nhds q₁),
      c₂.eventually (lt_mem_nhds q₂)] with z hz h₁ h₂
    have e := hv _ u₁ u₂ z hz
    show v z = ‖m.form s₂ s₁ z‖ ^ 2 / ((m.form s₁ s₁ z).re * (m.form s₂ s₂ z).re)
    rw [e, mul_assoc, mul_div_cancel_right₀ _ (mul_pos h₁ h₂).ne']
  have hT : IsOpen {M : Fin 2 → Fin 2 → ℂ | (M 1 1).re * (M 0 0).re ≠ 0} :=
    isOpen_ne_fun (((Complex.continuous_re.comp ((continuous_apply 1).comp (continuous_apply 1))).mul
      (Complex.continuous_re.comp ((continuous_apply 0).comp (continuous_apply 0))))) continuous_const
  have hmem : m.gram ![s₂, s₁] y ∈ {M : Fin 2 → Fin 2 → ℂ | (M 1 1).re * (M 0 0).re ≠ 0} := by
    show (m.form s₁ s₁ y).re * (m.form s₂ s₂ y).re ≠ 0
    exact (mul_pos q₁ q₂).ne'
  refine ⟨(hG.comp (Ψ := ratio) hT hmem fun M hM => contDiffAt_ratio hM).congr key, ?_⟩
  have e := hv _ u₁ u₂ y hy
  have cs := CurveDens.normSq_form_le m s₂ s₁ y
  have hn : 0 ≤ ‖m.form s₂ s₁ y‖ ^ 2 := sq_nonneg _
  change ‖m.form s₂ s₁ y‖ ^ 2 = v y * (m.form s₁ s₁ y).re * (m.form s₂ s₂ y).re at e
  have hpp := mul_pos q₁ q₂
  constructor
  · by_contra hneg
    push_neg at hneg
    nlinarith
  · by_contra hbig
    push_neg at hbig
    nlinarith

theorem cosSq_smooth : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    (∀ y, 0 ≤ v y ∧ v y ≤ 1) ∧ Continuous v ∧ (hY.atlas σ).SmoothOn Set.univ (fun y => (v y : ℂ)) := by
  intro k _ B Y _ _ q p d _ hY π w E h H flB fl _ _ σ v hv
  have Hm : ((h.pull π w).met σ).IsCInf := H.pull π w σ
  have loc : ∀ y, VInfAt v y ∧ 0 ≤ v y ∧ v y ≤ 1 := fun y => by
    obtain ⟨U₁, t₁, hy₁, hp₁⟩ := CosSqMeas.exists_sec_form_pos ((h.pull π w).met σ) (fl.ι 1)
      (fl.isVB 1) (fl.isSubbundle 1) y
    obtain ⟨U₂, t₂, hy₂, hp₂⟩ := CosSqMeas.exists_sec_form_pos ((h.pull π w).met σ)
      ((Scheme.Modules.pullback π).map (flB.ι 1)) ((flB.isVB 1).pullback π)
      (SubPull.isSubbundle_pullback B Y π _ E (flB.ι 1) 1 (flB.isVB 1) (flB.isSubbundle 1)) y
    exact vInfAt_of_isCosSq Hm hv t₁ t₂ hy₁ hy₂ hp₁ hp₂
  refine ⟨fun y => (loc y).2, continuous_iff_continuousAt.2 fun y => (loc y).1.continuousAt, ?_⟩
  exact hY.smoothOn (G := fun z (_ _ : Unit) => (v z : ℂ))
    (fun y _ _ _ => (loc y).1.comp_contDiff Complex.ofRealCLM.contDiff) () ()

end GlobalTheory.CosSqSmooth

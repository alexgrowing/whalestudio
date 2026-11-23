import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CosSqMeas

open TopologicalSpace Filter Topology
open scoped ComplexOrder

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem exists_sec_form_pos {E F : X.Modules} {n : ℕ} (h : Met p σ E n) (ι : F ⟶ E)
    (hF : IsVB F 1) (hι : IsSubbundle ι) (y : CxPts p σ) :
    ∃ (U : X.Opens) (t : Γ(F, U)), y ∈ ptsIn p σ U ∧
      0 < (h.form (ι.app U t) (ι.app U t) y).re := by
  obtain ⟨hm, s, hs⟩ := hι
  let S : ShortComplex X.Modules := ShortComplex.mk ι (Limits.cokernel.π ι) (Limits.cokernel.condition ι)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ι, mono_f := hm }
  have : Nonempty X := ⟨y.1 (IsLocalRing.closedPoint ℂ)⟩
  obtain ⟨h₂, -⟩ := VBExt.isVB_and_cls_det_of_shortExact X S 1 s hS hF hs
  obtain rfl : n = 1 + s := h.isVB.rank_unique h₂
  obtain ⟨a, hy⟩ := Met.exists_adapted (p := p) hS hF hs y
  have hpos := (h.posDef_gram_frame (S := S) hS a hy).diag_pos (i := Sum.inl 0)
  refine ⟨a.U, a.e 0, hy, (Complex.pos_iff.1 hpos).1⟩

theorem continuousAt_form {E : X.Modules} {n : ℕ} {h : Met p σ E n} (H : h.IsCInf) {U : X.Opens}
    (s t : Γ(E, U)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    ContinuousAt (fun z => h.form s t z) y :=
  (H.gram ![s, t] hy 0 1).continuousAt

end GlobalTheory.CosSqMeas

namespace GlobalTheory.CosSqMeas

open TopologicalSpace Filter Topology
open scoped ComplexOrder

theorem measurable_cosSq : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    Measurable v := by
  intro k _ B Y _ _ q p d _ _ π w E h H flB fl _ _ σ v hv
  have Hm : ((h.pull π w).met σ).IsCInf := H.pull π w σ
  refine Continuous.measurable (continuous_iff_continuousAt.2 fun y => ?_)
  obtain ⟨U₁, t₁, hy₁, hp₁⟩ := exists_sec_form_pos ((h.pull π w).met σ) (fl.ι 1) (fl.isVB 1)
    (fl.isSubbundle 1) y
  obtain ⟨U₂, t₂, hy₂, hp₂⟩ := exists_sec_form_pos ((h.pull π w).met σ)
    ((Scheme.Modules.pullback π).map (flB.ι 1)) ((flB.isVB 1).pullback π)
    (SubPull.isSubbundle_pullback B Y π _ E (flB.ι 1) 1 (flB.isVB 1) (flB.isSubbundle 1)) y
  have hy : y ∈ ptsIn p σ (U₁ ⊓ U₂) := mem_ptsIn_inf.2 ⟨hy₁, hy₂⟩
  set m := (h.pull π w).met σ
  set l := fl.ι 1
  set l' := (Scheme.Modules.pullback π).map (flB.ι 1)
  set u₁ := Twist.resM _ (inf_le_left : U₁ ⊓ U₂ ≤ U₁) t₁
  set u₂ := Twist.resM _ (inf_le_right : U₁ ⊓ U₂ ≤ U₂) t₂
  have e₁ : m.form (l.app _ u₁) (l.app _ u₁) y = m.form (l.app U₁ t₁) (l.app U₁ t₁) y := by
    rw [Twist.app_resM, m.form_resM _ _ _ hy]
  have e₂ : m.form (l'.app _ u₂) (l'.app _ u₂) y = m.form (l'.app U₂ t₂) (l'.app U₂ t₂) y := by
    rw [Twist.app_resM, m.form_resM _ _ _ hy]
  have c₁ := Complex.continuous_re.continuousAt.comp (continuousAt_form Hm (l.app _ u₁) (l.app _ u₁) hy)
  have c₂ := Complex.continuous_re.continuousAt.comp (continuousAt_form Hm (l'.app _ u₂) (l'.app _ u₂) hy)
  have c₃ := (continuousAt_form Hm (l'.app _ u₂) (l.app _ u₁) hy).norm.pow 2
  have hp₁' : 0 < (m.form (l.app _ u₁) (l.app _ u₁) y).re := by rw [e₁]; exact hp₁
  have hp₂' : 0 < (m.form (l'.app _ u₂) (l'.app _ u₂) y).re := by rw [e₂]; exact hp₂
  refine (c₃.div (c₁.mul c₂) (mul_pos hp₁' hp₂').ne').congr ?_
  filter_upwards [(isOpen_ptsIn _).mem_nhds hy, c₁.eventually (lt_mem_nhds hp₁'),
    c₂.eventually (lt_mem_nhds hp₂')] with z hz h₁ h₂
  have := hv _ u₁ u₂ z hz
  simp only [Function.comp_apply] at h₁ h₂
  simp only [Pi.div_apply, Pi.mul_apply, Pi.pow_apply, Function.comp_apply]
  rw [this, mul_assoc, mul_div_cancel_right₀ _ (mul_pos h₁ h₂).ne']

end GlobalTheory.CosSqMeas

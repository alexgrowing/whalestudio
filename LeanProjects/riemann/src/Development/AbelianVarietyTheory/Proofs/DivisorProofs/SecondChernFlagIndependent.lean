import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsFrameIndependentClosedStatement

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm

open GlobalTheory.HermFrame Matrix
open scoped ComplexOrder

theorem c2F_flag_indep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl fl' : Vert.Flag E 2), c2F hX σ h fl = c2F hX σ h fl' := by
  intro k _ X _ p D hX σ E h H fl fl'
  have gf : ∀ (f : Vert.Flag E 2) (y z : CxPts p σ), z ∈ ptsIn p σ (frameAt f y).U →
      (h.met σ).gram (frameAt f y).frame z =
        ((h.met σ).G ((frameAt f y).mid (lineSC_shortExact f)) z).submatrix finSumFinEquiv finSumFinEquiv :=
    fun f y z hz => Met.gram_frame (S := lineSC f) (r := 1) (s := 1) (h.met σ) (lineSC_shortExact f) (frameAt f y) hz
  have pf : ∀ (f : Vert.Flag E 2) (y z : CxPts p σ), z ∈ ptsIn p σ (frameAt f y).U →
      ((h.met σ).gram (frameAt f y).frame z).PosDef :=
    fun f y z hz => Met.posDef_gram_frame (S := lineSC f) (r := 1) (s := 1) (h.met σ) (lineSC_shortExact f) (frameAt f y) hz
  have sf : ∀ (f : Vert.Flag E 2) (y : CxPts p σ) (i j : Fin 1 ⊕ Fin 1),
      (hX.atlas σ).SmoothOn (ptsIn p σ (frameAt f y).U) fun z => (h.met σ).gram (frameAt f y).frame z i j :=
    fun f y i j => hX.smoothOn (fun _ hz => Met.IsCInf.gram (H σ) (frameAt f y).frame hz) i j
  let ch : Bool × CxPts p σ → Chart E (1 + 1) := fun a =>
    cond a.1 ((frameAt fl a.2).mid (lineSC_shortExact fl)) ((frameAt fl' a.2).mid (lineSC_shortExact fl'))
  let G : Bool × CxPts p σ → CxPts p σ → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := fun a =>
    cond a.1 ((h.met σ).gram (frameAt fl a.2).frame) ((h.met σ).gram (frameAt fl' a.2).frame)
  let U : Bool × CxPts p σ → Set (CxPts p σ) := fun a => ptsIn p σ (ch a).U
  let g : Bool × CxPts p σ → Bool × CxPts p σ → CxPts p σ → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
    fun a b z => ((ch a).tr p σ (ch b) z).submatrix finSumFinEquiv finSumFinEquiv
  have hG : ∀ a, ∀ z ∈ U a, G a z = ((h.met σ).G (ch a) z).submatrix finSumFinEquiv finSumFinEquiv := by
    rintro ⟨b, y⟩ z hz
    cases b
    · exact gf fl' y z hz
    · exact gf fl y z hz
  have hUo : ∀ a, IsOpen (U a) := fun _ => isOpen_ptsIn _
  have hcov : ∀ y, ∃ a, y ∈ U a := fun y => ⟨(true, y), mem_frameAt fl y⟩
  have hholo : ∀ a b i j, (hX.atlas σ).HolOn (U a ∩ U b) fun z => g a b z i j := fun a b i j c =>
    (c.holo ((ch b).U ⊓ (ch a).U) (((ch a).isFrame.basis inf_le_right).repr
      (GlobalTheory.Twist.resM E inf_le_left ((ch b).e (finSumFinEquiv j))) (finSumFinEquiv i))).mono
      fun _ hv => ⟨hv.1, mem_ptsIn_inf.2 ⟨hv.2.2, hv.2.1⟩⟩
  have hsm : ∀ a i j, (hX.atlas σ).SmoothOn (U a) fun z => G a z i j := by
    rintro ⟨b, y⟩ i j
    cases b
    · exact sf fl' y i j
    · exact sf fl y i j
  have hpd : ∀ a, ∀ z ∈ U a, (G a z).PosDef := by
    rintro ⟨b, y⟩ z hz
    cases b
    · exact pf fl' y z hz
    · exact pf fl y z hz
  have htr : ∀ a b, ∀ z ∈ U a ∩ U b, G b z = chg (g a b z) (G a z) := by
    intro a b z hz
    rw [hG a z hz.1, hG b z hz.2, chg_submatrix, ← (h.met σ).trans _ _ z hz.1]
  have key := GlobalTheory.T.chernForms_frame_independent_closed (hX.atlas σ) U hUo hcov g hholo G hsm hpd htr 2
  funext x
  exact key.1 (true, x.pt) (false, x.pt) x (mem_frameAt fl x.pt) (mem_frameAt fl' x.pt)

end GlobalTheory.LineForm

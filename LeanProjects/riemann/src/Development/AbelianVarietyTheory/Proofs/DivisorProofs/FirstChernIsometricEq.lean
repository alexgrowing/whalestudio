import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.LineForm

theorem c1F_eq_of_isometric (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsRegVar p D) (σ : k →+* ℂ) :
    ∀ L M : HermLB p, L.Isometric M → c1F hX σ L = c1F hX σ M := by
  intro L M h
  obtain ⟨w, -, hw⟩ := h.exists_units
  funext x
  obtain ⟨⟨c, y⟩, hy⟩ := x
  have ha : y ∈ ptsIn p σ (M.B.U (pick (M.φ σ).isLB y)) := mem_pick _ y
  have hb : y ∈ ptsIn p σ (L.B.U (pick (L.φ σ).isLB y)) := mem_pick _ y
  set a := pick (M.φ σ).isLB y
  set b := pick (L.φ σ).isLB y
  have hy' : y ∈ c.e.source := hy
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (M.B.U a ⊓ L.B.U b))
  have hm := ChartGlue.mem_over c.e hy' (mem_ptsIn_inf.2 ⟨ha, hb⟩)
  have hg := c.holo _ (w a b).val
  have hf : ContDiffAt ℂ 2 (ev p σ _ (w a b).val ∘ c.e.symm) (c.e y) :=
    (SCV.analyticAt_of_differentiableOn (hg.mono fun v hv => ⟨hv.1, hv.2⟩) (ho.mem_nhds hm)).contDiffAt
  have h0 : (ev p σ _ (w a b).val ∘ c.e.symm) (c.e y) ≠ 0 := ev_ne_zero hm.2 (w a b).isUnit
  have hL : ContDiffAt ℝ 2 (fun v => (L.φ σ).φ b (c.e.symm v)) (c.e y) := (L.cInf σ).contDiffAt c hy' hb
  have hlog : ContDiffAt ℝ 2 (fun v => Real.log (‖(ev p σ _ (w a b).val ∘ c.e.symm) v‖ ^ 2)) (c.e y) :=
    ((hf.restrict_scalars ℝ).norm_sq ℂ).log (by simpa using h0)
  have key : leviForm (fun v => (M.φ σ).φ a (c.e.symm v)) (c.e y) =
      leviForm (fun v => (L.φ σ).φ b (c.e.symm v)) (c.e y) := by
    rw [leviForm_congr (u' := fun v => (L.φ σ).φ b (c.e.symm v) +
        Real.log (‖(ev p σ _ (w a b).val ∘ c.e.symm) v‖ ^ 2)), leviForm_add hL hlog,
      leviForm_log_normSq_eq_zero hf h0, add_zero]
    filter_upwards [ho.mem_nhds hm] with v hv
    exact hw σ a b _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2
  have eL : c1F hX σ L ⟨(c, y), hy⟩ =
      ofValues (HermFrame.ddc (fun v => (L.φ σ).φ b (c.e.symm v)) (c.e y)) := rfl
  have eM : c1F hX σ M ⟨(c, y), hy⟩ =
      ofValues (HermFrame.ddc (fun v => (M.φ σ).φ a (c.e.symm v)) (c.e y)) := rfl
  rw [eL, eM]
  unfold HermFrame.ddc
  rw [key]

end GlobalTheory.LineForm

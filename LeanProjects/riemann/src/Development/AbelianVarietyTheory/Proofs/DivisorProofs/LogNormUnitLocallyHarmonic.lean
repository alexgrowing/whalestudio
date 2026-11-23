import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O

theorem log_norm_ratVal_eq_re_holo : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (a : Fin (M.n + 1)) (h : Y.Fn) (x : M.X a), UnitAt (under (I.pt a x)) h → ∃ W : Set (M.X a), IsOpen W ∧ x ∈ W ∧ ∃ G : M.X a → ℂ, (M.A a).HoloOn W G ∧ ∀ y ∈ W, Real.log ‖ratVal h (I.pt a y)‖ = (G y).re := by
  intro F _ _ Y e M I a h x hx
  obtain ⟨U0, hU0, hU0u⟩ := hx.exists_nhds
  obtain ⟨b, hb⟩ := exists_unit_fnOf_eq hU0u
  have hb' := hb (gen_mem hU0)
  have hx0 : I.pt a x ∈ ptsIn Y.str (I.ε a) U0 := mem_ptsIn.2 hU0
  set r0 := ev Y.str (I.ε a) U0 b.1 (I.pt a x) with hr0
  have hr0ne : r0 ≠ 0 := ev_ne_zero hx0 b.isUnit
  let S : Set (Pts Y (I.ε a)) := ptsIn Y.str (I.ε a) U0 ∩ (fun p => ev Y.str (I.ε a) U0 b.1 p / r0) ⁻¹' Complex.slitPlane
  have hS : IsOpen S := ((continuousOn_ev b.1).div_const r0).isOpen_inter_preimage (isOpen_ptsIn U0) Complex.isOpen_slitPlane
  let g : Pts Y (I.ε a) → ℂ := fun p => Complex.log (ev Y.str (I.ε a) U0 b.1 p / r0) + ((Real.log ‖r0‖ : ℝ) : ℂ)
  refine ⟨(I.pt a) ⁻¹' S, hS.preimage (I.pt a).continuous, ⟨hx0, ?_⟩, g ∘ I.pt a, ?_, ?_⟩
  · show ev Y.str (I.ε a) U0 b.1 (I.pt a x) / r0 ∈ Complex.slitPlane
    rw [← hr0, div_self hr0ne]; exact Complex.one_mem_slitPlane
  · intro j
    obtain ⟨c, hc⟩ := I.alg a j
    have hd : DifferentiableOn ℂ (g ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' S) := by
      have h1 : DifferentiableOn ℂ (ev Y.str (I.ε a) U0 b.1 ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' S) :=
        (c.holo U0 b.1).mono fun v hv => ⟨hv.1, hv.2.1⟩
      intro v hv
      have h2 : (ev Y.str (I.ε a) U0 b.1 ∘ c.e.symm) v / r0 ∈ Complex.slitPlane := hv.2.2
      have h3 : DifferentiableWithinAt ℂ (fun w => (ev Y.str (I.ε a) U0 b.1 ∘ c.e.symm) w / r0) (c.e.target ∩ c.e.symm ⁻¹' S) v := by
        simpa only [div_eq_mul_inv] using (h1 v hv).mul_const r0⁻¹
      have h4 := h3.clog h2
      exact h4.add_const _
    have key := (c.analyticOnNhd_finChart_iff hS g).2 hd
    have hfun : (g ∘ I.pt a) ∘ ((M.A a).chart j).symm = g ∘ c.finChart.symm := by
      funext z; rw [hc]; simp [Homeomorph.transOpenPartialHomeomorph_symm_apply]
    rw [hfun]
    refine key.mono ?_
    rintro z ⟨hz1, hz2⟩
    rw [hc] at hz1 hz2
    refine ⟨by simpa using hz1, ?_⟩
    simpa [Homeomorph.transOpenPartialHomeomorph_symm_apply] using hz2
  · rintro y ⟨hy1, hy2⟩
    have hrat : ratVal h (I.pt a y) = ev Y.str (I.ε a) U0 b.1 (I.pt a y) := by
      rw [← hb', ratVal_fnOf hy1]
    have hne : ev Y.str (I.ε a) U0 b.1 (I.pt a y) ≠ 0 := ev_ne_zero hy1 b.isUnit
    simp only [g, Function.comp_apply, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div, hrat]
    rw [Real.log_div (norm_ne_zero_iff.2 hne) (norm_ne_zero_iff.2 hr0ne)]
    ring

end GlobalTheory.Mean4O

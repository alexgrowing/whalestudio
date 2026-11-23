import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralMulFderivOfTsupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralCutoffLogDecay
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory GlobalTheory.Cartier
  GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.TrueGeo GlobalTheory.ChartGlue GlobalTheory.ShFam GlobalTheory.FinChart Filter Topology

namespace GlobalTheory.AmplePos

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem levi_isPot_eq_curvMet {σ : F →+* ℂ} {Δ : Y.Dv} {m : Var.Met Y σ Δ} (hm : Y.mSmooth σ Δ m) {X : Type}
    [TopologicalSpace X] (h : X ≃ₜ Pts Y σ) {Q : LocPot X} (hQ : IsPot (C := cxSt F) h m Q) (c : AlgChart Y.str σ Y.dim)
    (z : X) (hz : h z ∈ c.e.source) (w : Fin Y.dim → ℂ) :
    levi (Q.φ z ∘ (h.transOpenPartialHomeomorph c.finChart).symm) (c.finChart (h z)) w =
      Real.pi / 2 * curvMet m c (h z) w := by
  obtain ⟨f, hf⟩ := hQ z
  have hf0 : f ≠ 0 := have ⟨_, _, hu⟩ := (hf z (Q.mem_U z)).1; left_ne_zero_of_mul hu.ne_zero
  set g : Y.Fnˣ := (Units.mk0 f hf0)⁻¹ with hg
  have hginv : ((g : Y.Fn))⁻¹ = f := by simp [g]
  have hmem : ∀ y' ∈ Q.U z, h y' ∈ Var.eqnSet σ Δ g := fun y' hy' =>
    CartierDiv.isEqn_iff_generatesAt_inv.2 (by rw [hginv]; exact (hf y' hy').1)
  have hval : ∀ y' ∈ Q.U z, Q.φ z y' = m.wt g (h y') / 2 := by
    intro y' hy'
    have e₁ : (cxSt F).pn Y σ Δ m ((cxSt F).cx Y σ f) (h y') = m.h g (h y') := by
      have := Var.pn_frame (m := m) (hmem y' hy')
      rwa [Units.val_inv_eq_inv_val, hginv] at this
    rw [(hf y' hy').2.2]
    unfold lnN
    rw [e₁, Var.Met.wt]
    ring
  have hS : IsOpen (h.symm ⁻¹' Q.U z) := (Q.isOpen_U z).preimage h.symm.continuous
  have e₁ : Q.φ z ∘ (h.transOpenPartialHomeomorph c.finChart).symm =ᶠ[𝓝 (c.finChart (h z))]
      fun v => (m.wt g ∘ c.finChart.symm) v / 2 := by
    have hN : c.finChart.target ∩ c.finChart.symm ⁻¹' (h.symm ⁻¹' Q.U z) ∈ 𝓝 (c.finChart (h z)) :=
      (c.finChart.isOpen_inter_preimage_symm hS).mem_nhds
        ⟨c.finChart.map_source hz, by simp [c.finChart.left_inv hz, Q.mem_U]⟩
    filter_upwards [hN] with v hv
    simp only [Function.comp_apply, Homeomorph.transOpenPartialHomeomorph_symm_apply]
    rw [hval _ hv.2, Homeomorph.apply_symm_apply]
  have hgz : h z ∈ Var.eqnSet σ Δ g := hmem z (Q.mem_U z)
  have hsm : ContDiffAt ℝ 2 (m.wt g ∘ c.e.symm) (c.e (h z)) :=
    (((((hm.2 g).mono (fun _ hy => ⟨trivial, hy⟩)).chart (Var.isOpen_eqnSet Δ g) c).contDiffAt
      ((isOpen_over _ (Var.isOpen_eqnSet Δ g)).mem_nhds (mem_over c.e hz hgz))).of_le (WithTop.coe_le_coe.2 le_top))
  rw [levi_congr e₁, levi_half, ← c.leviV_re_eq hsm w]
  have e₂ := hm.levi_frame Var.smoothOn_zero hz (Var.mem_eqnSet Δ (h z)) hgz w
  simp only [Pi.zero_apply, add_zero] at e₂
  change c.levi (m.wt g) (h z) w / 2 = Real.pi / 2 * (c.levi (m.wt (Var.eqn Δ (h z))) (h z) w / Real.pi)
  rw [show (m.wt g) = fun z => m.wt g z from rfl, e₂]
  field_simp

theorem leviAt_pos {e : ℕ} {M : Man e} (I : ManIs M Y) (he : Y.dim = e) (a : Fin (M.n + 1)) {Δ : Y.Dv}
    {m : Var.Met Y (I.ε a) Δ} (hm : Y.mSmooth (I.ε a) Δ m)
    (hc : ∀ (c : AlgChart Y.str (I.ε a) Y.dim), ∀ y ∈ c.e.source, ∀ ξ, ξ ≠ 0 → 0 < curvMet m c y ξ)
    {Q : LocPot (M.X a)} (hQ : IsPot (C := cxSt F) (I.pt a) m Q) (j : Fin (M.A a).n) {y : Fin e → ℂ}
    (hy : y ∈ ((M.A a).chart j).target) {w : Fin e → ℂ} (hw : w ≠ 0) : 0 < leviAt (M.A a) Q j y w := by
  subst he
  obtain ⟨c, hc'⟩ := I.alg a j
  unfold leviAt
  rw [hc'] at hy ⊢
  rw [Homeomorph.transOpenPartialHomeomorph_target] at hy
  have hq : c.finChart.symm y ∈ c.e.source := c.finChart.map_target hy
  have key := levi_isPot_eq_curvMet hm (I.pt a) hQ c ((I.pt a).symm (c.finChart.symm y)) (by simpa using hq) w
  simp only [Homeomorph.apply_symm_apply, c.finChart.right_inv hy] at key
  have hb : ((I.pt a).transOpenPartialHomeomorph c.finChart).symm y = (I.pt a).symm (c.finChart.symm y) := by simp
  rw [hb, key]
  exact mul_pos (by positivity) (hc c _ hq w hw)

end GlobalTheory.AmplePos

open GlobalTheory.AmplePos GlobalTheory.ShFam in

theorem GlobalTheory.AmplePos.ample_isPosPot : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y)
    (H : Ht O.Y), O.Reads A T H → ∀ (c : O.s.Comp) (σ : Fin ((T.M c).n + 1)),
    ReciprocityTheory.AnForm.M.IsPosPot ((T.M c).A σ) ((T.F c).a σ) := by
  intro _ _ D O hO A T H R c σ
  obtain ⟨xx, PP, hC⟩ := hO
  intro x j y hy w hw
  obtain ⟨Q, hQ, hlev⟩ := (R.an c).a σ
  have hd : (O.var c).dim = Formalism.MainNotions.WeightThresholdDefs.dimY O.Y := by rw [O.dim_eq c]; rfl
  have hab := hC.ab_eq
  have hpos : 0 < leviAt ((T.M c).A σ) (Q ()) j y w := by
    refine leviAt_pos (R.man c) hd σ (m := (O.met.ab c).m ((R.man c).ε σ)) ?_ ?_ (hQ ()).1 j hy.1 hw
    · rw [hab]; exact PP.ab_smooth c _
    · intro c' z hz ξ hξ
      have h1 := PP.curv_ge c ((R.man c).ε σ) c' z hz ξ
      have h2 := (PP.om_kaehler c ((R.man c).ε σ)).2 c' z hz ξ hξ
      have h3 : (0 : ℝ) < ((PP.ab c).n : ℕ) := by exact_mod_cast (PP.ab c).n.2
      rw [hab]
      have h4 := lt_of_lt_of_le (mul_pos PP.c₀_pos h2) h1
      exact (div_pos_iff_of_pos_right h3).1 h4
  rw [GlobalTheory.ShellMass.levi_base (T.a_pot c σ) x j hy.1 hy.2 w, hlev j y hy.1 w]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  exact mul_pos (inv_pos.2 (by exact_mod_cast (O.met.ab c).n.2)) hpos

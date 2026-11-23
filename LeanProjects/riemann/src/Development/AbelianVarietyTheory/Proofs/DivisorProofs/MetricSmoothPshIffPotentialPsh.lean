import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPotentialPositiveOnComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMetricOnLineGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MIntEqOfLeviEq
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Mean4O
open Filter Topology GlobalTheory.ChartGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PotSmoothPsh

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem cInfAt_log {σ : F →+* ℂ} {f : Pts Y σ → ℝ} {y : Pts Y σ} (h : CInfAt f y) (hy : 0 < f y) :
    CInfAt (fun z => Real.log (f z)) y := by
  obtain ⟨W, ι, hι, g, G, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have hG : 0 < G (fun a => ev Y.str σ W (g a) y) := by
    have e := h₅.self_of_nhds
    rw [e] at hy
    exact hy
  refine ⟨W, ι, hι, g, fun v => Real.log (G v), O ∩ G ⁻¹' Set.Ioi 0, h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ isOpen_Ioi, ⟨h₃, hG⟩,
    (h₄.mono Set.inter_subset_left).log fun v hv => (ne_of_gt hv.2), ?_⟩
  exact h₅.fun_comp Real.log

variable {e : ℕ} {M : Man e} (I : ManIs M Y) (a : Fin (M.n + 1)) {Δ : Y.Dv}

theorem h_pos_of_isPot {m : (cxSt F).Met Y (I.ε a) Δ} {Q : LocPot (M.X a)} (hQ : IsPot (I.pt a) m Q)
    {g : Y.Fnˣ} {y : Pts Y (I.ε a)} (hg : y ∈ Var.eqnSet (I.ε a) Δ g) : 0 < m.h g y := by
  have h1 := GlobalTheory.ChernWeilLine.pn_pos_of_isPot I a hQ (y := y) (CartierDiv.isEqn_iff_generatesAt_inv.1 hg)
  have h2 := Var.pn_frame (m := m) hg
  rw [Units.val_inv_eq_inv_val] at h2
  rw [← h2]
  exact h1

theorem mSmooth_of_isPot {m : (cxSt F).Met Y (I.ε a) Δ} {Q : LocPot (M.X a)} (hQ : IsPot (I.pt a) m Q)
    (hQ' : IsPotential (M.A a) Q) : Var.mSmooth Y (I.ε a) Δ m := by
  refine ⟨fun y _ => h_pos_of_isPot I a hQ (Var.mem_eqnSet Δ y), fun g => ?_⟩
  refine (cInfAt_iff_smoothOn (Y.an (I.ε a)) (isOpen_univ.inter (Var.isOpen_eqnSet Δ g))).1 fun y hy => ?_
  have hgen := CartierDiv.isEqn_iff_generatesAt_inv.1 hy.2
  have hc := GlobalTheory.ChernWeilLine.cInfAt_pn_of_isPot I a hQ hQ' hgen
  refine ((cInfAt_log hc (GlobalTheory.ChernWeilLine.pn_pos_of_isPot I a hQ hgen)).neg).congr ?_
  filter_upwards [(Var.isOpen_eqnSet Δ g).mem_nhds hy.2] with z hz
  have h2 := Var.pn_frame (m := m) hz
  rw [Units.val_inv_eq_inv_val] at h2
  show -Real.log (m.h g z) = _
  rw [← h2]
  rfl

section Levi

variable {σ : F →+* ℂ} {m : Var.Met Y σ Δ}

theorem mPsh_iff_chart (hm : Var.mSmooth Y σ Δ m) :
    Var.mPsh Y σ Δ m 0 ↔ ∀ (c : AlgChart Y.str σ Y.dim) (y : Pts Y σ), y ∈ c.e.source →
      ∀ ξ, 0 ≤ c.levi (m.wt (Var.eqn Δ y)) y ξ := by
  rw [hm.mPsh_iff_levi Var.smoothOn_zero]
  constructor
  · intro H c y hy ξ
    simpa using H c (Var.eqn Δ y) y hy (Var.mem_eqnSet Δ y) ξ
  · intro H c g y hy hg ξ
    rw [hm.levi_frame Var.smoothOn_zero hy (Var.mem_eqnSet Δ y) hg ξ]
    simpa using H c y hy ξ

theorem contDiffAt_wt (hm : Var.mSmooth Y σ Δ m) (c : AlgChart Y.str σ Y.dim) {g : Y.Fnˣ} {y : Pts Y σ}
    (hy : y ∈ c.e.source) (hg : y ∈ Var.eqnSet σ Δ g) :
    ContDiffAt ℝ 2 (m.wt g ∘ c.finChart.symm) (c.finChart y) := by
  have hS := Var.isOpen_eqnSet (σ := σ) Δ g
  have hOn := (c.contDiffOn_finChart_iff _ _ (m.wt g)).2
    (((hm.2 g).mono (fun _ hz => ⟨trivial, hz⟩)).chart hS c)
  exact (hOn.contDiffAt ((c.finChart.isOpen_inter_preimage_symm hS).mem_nhds
    ⟨c.finChart.map_source hy, by simpa [c.finChart.left_inv hy] using hg⟩)).of_le
    (WithTop.coe_le_coe.2 le_top)

theorem contDiffAt_wt' (hm : Var.mSmooth Y σ Δ m) (c : AlgChart Y.str σ Y.dim) {g : Y.Fnˣ} {y : Pts Y σ}
    (hy : y ∈ c.e.source) (hg : y ∈ Var.eqnSet σ Δ g) :
    ContDiffAt ℝ 2 (m.wt g ∘ c.e.symm) (c.e y) :=
  (((((hm.2 g).mono (fun _ hz => ⟨trivial, hz⟩)).chart (Var.isOpen_eqnSet Δ g) c).contDiffAt
    ((isOpen_over _ (Var.isOpen_eqnSet Δ g)).mem_nhds (mem_over c.e hy hg))).of_le (WithTop.coe_le_coe.2 le_top))

theorem levi_nonneg_of_chart (hm : Var.mSmooth Y σ Δ m) {c c' : AlgChart Y.str σ Y.dim} {g : Y.Fnˣ}
    {y : Pts Y σ} (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) (hg : y ∈ Var.eqnSet σ Δ g)
    (H : ∀ w, 0 ≤ c'.levi (m.wt g) y w) (ξ : Fin Y.dim → ℂ) : 0 ≤ c.levi (m.wt g) y ξ := by
  obtain ⟨w', -, hw⟩ := c.exists_levi_eq c' hy hy' (contDiffAt_wt hm c' hy' hg) ξ
  have e₁ := c.leviV_re_eq (contDiffAt_wt' hm c hy hg) ξ
  have e₂ := c'.leviV_re_eq (contDiffAt_wt' hm c' hy' hg) w'
  have h := H w'
  change 0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV _ (fun v => (m.wt g (c.e.symm v) : ℂ)) (c.e y) ξ).re
  change 0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV _ (fun v => (m.wt g (c'.e.symm v) : ℂ)) (c'.e y) w').re at h
  rw [e₁, hw, ← e₂]
  exact h

end Levi

section Man

variable {M' : Man Y.dim} (I' : ManIs M' Y) (a' : Fin (M'.n + 1))

theorem leviAt_nonneg_iff {m : Var.Met Y (I'.ε a') Δ} (hm : Var.mSmooth Y (I'.ε a') Δ m) {Q : LocPot (M'.X a')}
    (hQ : IsPot (C := cxSt F) (I'.pt a') m Q) (j : Fin (M'.A a').n) (c : AlgChart Y.str (I'.ε a') Y.dim)
    (hc : (M'.A a').chart j = (I'.pt a').transOpenPartialHomeomorph c.finChart) {y : Fin Y.dim → ℂ}
    (hy : y ∈ ((M'.A a').chart j).target) (w : Fin Y.dim → ℂ) :
    0 ≤ leviAt (M'.A a') Q j y w ↔
      0 ≤ c.levi (m.wt (Var.eqn Δ (c.finChart.symm y))) (c.finChart.symm y) w := by
  unfold leviAt
  rw [hc] at hy ⊢
  rw [Homeomorph.transOpenPartialHomeomorph_target] at hy
  have hq : c.finChart.symm y ∈ c.e.source := c.finChart.map_target hy
  have key := GlobalTheory.AmplePos.levi_isPot_eq_curvMet hm (I'.pt a') hQ c ((I'.pt a').symm (c.finChart.symm y))
    (by simpa using hq) w
  simp only [Homeomorph.apply_symm_apply, c.finChart.right_inv hy] at key
  have hb : ((I'.pt a').transOpenPartialHomeomorph c.finChart).symm y = (I'.pt a').symm (c.finChart.symm y) := by simp
  rw [hb, key]
  change 0 ≤ Real.pi / 2 * (c.levi (m.wt (Var.eqn Δ (c.finChart.symm y))) (c.finChart.symm y) w / Real.pi) ↔ _
  have hπ := Real.pi_pos
  have e₁ : ∀ x : ℝ, Real.pi / 2 * (x / Real.pi) = x / 2 := fun x => by field_simp
  rw [e₁]
  constructor <;> intro h <;> linarith

theorem isPsh_iff_leviAt {e' : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e' X} {P : LocPot X}
    (hP : IsPotential A P) : IsPsh A P ↔ ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, 0 ≤ leviAt A P j y w := by
  refine ⟨fun hp j y hy w => hp _ j y ⟨hy, P.mem_U _⟩ w, fun h x j y hy w => ?_⟩
  rw [GlobalTheory.LeviOnly.levi_base hP x j hy.1 hy.2]
  exact h j y hy.1 w

theorem mPsh_iff_isPsh {m : Var.Met Y (I'.ε a') Δ} (hm : Var.mSmooth Y (I'.ε a') Δ m) {Q : LocPot (M'.X a')}
    (hQ : IsPot (C := cxSt F) (I'.pt a') m Q) (hQ' : IsPotential (M'.A a') Q) :
    Var.mPsh Y (I'.ε a') Δ m 0 ↔ IsPsh (M'.A a') Q := by
  rw [mPsh_iff_chart hm, isPsh_iff_leviAt hQ']
  constructor
  · intro H j y hy w
    obtain ⟨c, hc⟩ := I'.alg a' j
    rw [leviAt_nonneg_iff I' a' hm hQ j c hc hy w]
    have hy' := hy
    rw [hc, Homeomorph.transOpenPartialHomeomorph_target] at hy'
    exact H c _ (c.finChart.map_target hy') w
  · intro H c p hp ξ
    obtain ⟨j, hj⟩ := (M'.A a').cover ((I'.pt a').symm p)
    obtain ⟨c', hc'⟩ := I'.alg a' j
    have hp' : p ∈ c'.e.source := by
      rw [hc', Homeomorph.transOpenPartialHomeomorph_source] at hj
      simpa using hj
    have hyt : c'.finChart p ∈ ((M'.A a').chart j).target := by
      rw [hc', Homeomorph.transOpenPartialHomeomorph_target]
      exact c'.finChart.map_source hp'
    have H' : ∀ w, 0 ≤ c'.levi (m.wt (Var.eqn Δ p)) p w := fun w => by
      have := (leviAt_nonneg_iff I' a' hm hQ j c' hc' hyt w).1 (H j _ hyt w)
      rwa [c'.finChart.left_inv hp'] at this
    exact levi_nonneg_of_chart hm hp hp' (Var.mem_eqnSet Δ p) H' ξ

end Man

theorem smooth_and_mPsh_iff : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y),
    e = Y.dim → ∀ (Δ : Y.Dv) (a : Fin (M.n + 1)) (m : (cxSt F).Met Y (I.ε a) Δ) (Q : LocPot (M.X a)),
    IsPot (I.pt a) m Q → IsPotential (M.A a) Q →
    (cxSt F).mSmooth Y (I.ε a) Δ m ∧ ((cxSt F).mPsh Y (I.ε a) Δ m 0 ↔ IsPsh (M.A a) Q) := by
  intro F _ _ Y e M I he Δ a m Q hQ hQ'
  subst he
  have hm := mSmooth_of_isPot I a hQ hQ'
  exact ⟨hm, mPsh_iff_isPsh I a hm hQ hQ'⟩

end GlobalTheory.PotSmoothPsh

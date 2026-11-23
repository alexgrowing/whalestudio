import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombSmoothCurv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralCutoffLogDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPotentialPullback
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry CategoryTheory MeasureTheory Set GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.CxPts GlobalTheory.TrueGeo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ProjVar Formalism.L2.Pj Formalism.L2.Geo GlobalTheory
open ReciprocityTheory.AnForm.M

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormPotBridge

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

section General

variable {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {X : Type} [TopologicalSpace X]

theorem smoothOn_image {A : FinHolAtlas Y.dim X} {h : X ≃ₜ Pts Y σ} (hA : DivSec.ChartsAlg A h) {U : Set X}
    (hU : IsOpen U) {f : X → ℝ} (hf : A.SmoothOn U f) :
    (Y.an σ).SmoothOn (h '' U) (fun y => f (h.symm y)) := by
  have hO : IsOpen (h '' U) := h.isOpenMap U hU
  rw [← (DivSec.isAlgAtlas_algAtlas hA).smoothOn_iff (Y.an σ) hO, ← DivSec.smoothOn_comp_iff hA]
  have e1 : h ⁻¹' (h '' U) = U := h.preimage_image U
  have e2 : (fun y => f (h.symm y)) ∘ h = f := by funext z; simp
  rw [e1, e2]; exact hf

variable [NumberField F]

theorem levi_pot_eq_curvMet {Δ : Y.Dv} {m : Var.Met Y σ Δ} (h : X ≃ₜ Pts Y σ) {Q : LocPot X}
    (hQ : IsPot (C := cxSt F) h m Q) (z : X)
    (hs : (Y.an σ).SmoothOn (h '' Q.U z) (fun y => Q.φ z (h.symm y)))
    (c : AlgChart Y.str σ Y.dim) (hz : h z ∈ c.e.source) (ξ : Fin Y.dim → ℂ) :
    c.levi (fun y => Q.φ z (h.symm y)) (h z) ξ = Real.pi / 2 * curvMet m c (h z) ξ := by
  obtain ⟨f, hf⟩ := hQ z
  have hf0 : f ≠ 0 := have ⟨_, _, hu⟩ := (hf z (Q.mem_U z)).1; left_ne_zero_of_mul hu.ne_zero
  set g : Y.Fnˣ := (Units.mk0 f hf0)⁻¹ with hg
  have hginv : ((g : Y.Fn))⁻¹ = f := by simp [g]
  have hmem : ∀ y' ∈ Q.U z, h y' ∈ Var.eqnSet σ Δ g := fun y' hy' =>
    Cartier.CartierDiv.isEqn_iff_generatesAt_inv.2 (by rw [hginv]; exact (hf y' hy').1)
  have hval : ∀ y' ∈ Q.U z, Q.φ z y' = m.wt g (h y') / 2 := by
    intro y' hy'
    have e₁ : (cxSt F).pn Y σ Δ m ((cxSt F).cx Y σ f) (h y') = m.h g (h y') := by
      have := Var.pn_frame (m := m) (hmem y' hy')
      rwa [Units.val_inv_eq_inv_val, hginv] at this
    rw [(hf y' hy').2.2]
    unfold lnN
    rw [e₁, Var.Met.wt]
    ring
  have hpos : ∀ y' ∈ Q.U z, h y' ∈ m.posSet := fun y' hy' =>
    pos_of_mul_pos_right (hf y' hy').2.1 (sq_nonneg _)
  have hO : IsOpen (h '' Q.U z) := h.isOpenMap _ (Q.isOpen_U z)
  have hzU : h z ∈ h '' Q.U z := ⟨z, Q.mem_U z, rfl⟩
  have hwt : ∀ y ∈ h '' Q.U z, m.wt g y = 2 * Q.φ z (h.symm y) := by
    rintro _ ⟨y', hy', rfl⟩
    rw [h.symm_apply_apply, hval y' hy']; ring
  have hsg : (Y.an σ).SmoothOn (h '' Q.U z) (m.wt g) := fun i =>
    (contDiffOn_const.mul (hs i)).congr fun v hv => hwt _ hv.2
  have hS1 : ∀ y ∈ h '' Q.U z ∩ Var.eqnSet σ Δ (Var.eqn Δ (h z)),
      y ∈ Var.eqnSet σ Δ g ∧ y ∈ m.posSet := by
    rintro _ ⟨⟨y', hy', rfl⟩, _⟩
    exact ⟨hmem y' hy', hpos y' hy'⟩
  have hL : c.levi (m.wt (Var.eqn Δ (h z))) (h z) ξ = c.levi (m.wt g) (h z) ξ :=
    AnRead.levi_eq_of_add_log (R := Y.an σ) (hO.inter (Var.isOpen_eqnSet Δ _))
      (hsg.mono Set.inter_subset_left)
      ((Var.holoOn_tv Δ g (Var.eqn Δ (h z))).mono fun y hy => ⟨(hS1 y hy).1, hy.2⟩)
      (fun y hy => Var.tv_ne_zero (hS1 y hy).1 hy.2)
      (fun y hy => Var.Met.wt_trans (hS1 y hy).2 (hS1 y hy).1 hy.2) hz ⟨hzU, Var.mem_eqnSet Δ (h z)⟩ ξ
  have hc2 : ContDiffAt ℝ 2 (m.wt g ∘ c.e.symm) (c.e (h z)) := hsg.contDiffAt_two hO hz hzU
  have e2 : c.levi (fun y => Q.φ z (h.symm y)) (h z) ξ = c.levi (fun y => (1 / 2 : ℝ) * m.wt g y) (h z) ξ :=
    AlgChart.levi_congr hO hz hzU (fun y hy => by rw [hwt y hy]; ring) ξ
  rw [e2, AlgChart.levi_const_mul _ hc2, curvMet, ddcForm, hL]
  field_simp

end General

end GlobalTheory.FormPotBridge

namespace GlobalTheory.FormPotBridge

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem isPotential_formOf {e : ℕ} {M : Man e} (I : ManIs M Y) (he : Y.dim = e) {ι : Type} [Fintype ι]
    {Δ : ι → Y.Dv} (m : ∀ i σ, (cxSt F).Met Y σ (Δ i)) (t : ι → ℝ) {P : M.Pot} (hF : I.FormOf m t P)
    (a : Fin (M.n + 1)) (hP : IsPotential (M.A a) (P a)) (x : M.X a) :
    GlobalTheory.ShFam.IsPotential (Y.an (I.ε a)) (fun c y ξ => ∑ i, t i * curvMet (m i (I.ε a)) c y ξ)
      ((I.pt a) '' (P a).U x) (fun y => 2 * (P a).φ x ((I.pt a).symm y)) := by
  subst he
  have hA : DivSec.ChartsAlg (M.A a) (I.pt a) := I.alg a
  obtain ⟨Q, hQ, hlev⟩ := hF a
  have hO : IsOpen ((I.pt a) '' (P a).U x) := (I.pt a).isOpenMap _ ((P a).isOpen_U x)
  have hsP : (Y.an (I.ε a)).SmoothOn ((I.pt a) '' (P a).U x) (fun y => (P a).φ x ((I.pt a).symm y)) :=
    smoothOn_image hA ((P a).isOpen_U x) (hP.1 x)
  refine ⟨hO, fun i => contDiffOn_const.mul (hsP i), fun c y hyc hyW ξ => ?_⟩
  obtain ⟨z, hzU, rfl⟩ := hyW
  obtain ⟨j, hj⟩ := (M.A a).cover z
  obtain ⟨c', hc'⟩ := I.alg a j
  have hv : (M.A a).chart j z ∈ ((M.A a).chart j).target := ((M.A a).chart j).map_source hj
  have hsymm : ((M.A a).chart j).symm ((M.A a).chart j z) = z := ((M.A a).chart j).left_inv hj
  have hz' : (I.pt a) z ∈ c'.e.source := by
    rw [hc', Homeomorph.transOpenPartialHomeomorph_source] at hj
    exact hj
  have hsQ : ∀ i, (Y.an (I.ε a)).SmoothOn ((I.pt a) '' (Q i).U z) (fun y => (Q i).φ z ((I.pt a).symm y)) :=
    fun i => smoothOn_image hA ((Q i).isOpen_U z) ((hQ i).2.1 z)
  have hOQ : ∀ i, IsOpen ((I.pt a) '' (Q i).U z) := fun i => (I.pt a).isOpenMap _ ((Q i).isOpen_U z)
  have hzQ : ∀ i, (I.pt a) z ∈ (I.pt a) '' (Q i).U z := fun i => ⟨z, (Q i).mem_U z, rfl⟩
  have hzP : (I.pt a) z ∈ (I.pt a) '' (P a).U x := ⟨z, hzU, rfl⟩
  have hcv : (M.A a).chart j z = c'.finChart ((I.pt a) z) := by rw [hc']; rfl
  have hcs : ⇑((M.A a).chart j).symm = (I.pt a).symm ∘ c'.finChart.symm := by
    rw [hc', Homeomorph.transOpenPartialHomeomorph_symm_apply]
  have conv : ∀ (φ : M.X a → ℝ) (w : Fin Y.dim → ℂ),
      ContDiffAt ℝ 2 ((fun y => φ ((I.pt a).symm y)) ∘ c'.e.symm) (c'.e ((I.pt a) z)) →
        c'.levi (fun y => φ ((I.pt a).symm y)) ((I.pt a) z) w =
          levi (φ ∘ ((M.A a).chart j).symm) ((M.A a).chart j z) w := by
    intro φ w hφ
    rw [AlgChart.levi, c'.leviV_re_eq hφ, hcv, hcs]
    rfl
  have key : ∀ w, c'.levi (fun y => (P a).φ x ((I.pt a).symm y)) ((I.pt a) z) w =
      ∑ i, t i * c'.levi (fun y => (Q i).φ z ((I.pt a).symm y)) ((I.pt a) z) w := by
    intro w
    have hb := GlobalTheory.ShellMass.levi_base hP x j hv (by rw [hsymm]; exact hzU) w
    rw [hlev j _ hv w] at hb
    rw [conv _ w (hsP.contDiffAt_two hO hz' hzP), hb]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [conv _ w ((hsQ i).contDiffAt_two (hOQ i) hz' (hzQ i))]
    simp only [leviAt, hsymm]
  have eP := AlgChart.levi_trans hyc hz' (hsP.contDiffAt_two hO hz' hzP) ξ
  have eQ : ∀ i, c.levi (fun y => (Q i).φ z ((I.pt a).symm y)) ((I.pt a) z) ξ =
      c'.levi (fun y => (Q i).φ z ((I.pt a).symm y)) ((I.pt a) z) (c.dtrans c' ((I.pt a) z) ξ) :=
    fun i => AlgChart.levi_trans hyc hz' ((hsQ i).contDiffAt_two (hOQ i) hz' (hzQ i)) ξ
  have hA' : ∀ i, c.levi (fun y => (Q i).φ z ((I.pt a).symm y)) ((I.pt a) z) ξ =
      Real.pi / 2 * curvMet (m i (I.ε a)) c ((I.pt a) z) ξ :=
    fun i => levi_pot_eq_curvMet (I.pt a) (hQ i).1 z (hsQ i) c hyc ξ
  show ∑ i, t i * curvMet (m i (I.ε a)) c ((I.pt a) z) ξ =
    c.levi (fun y => 2 * (P a).φ x ((I.pt a).symm y)) ((I.pt a) z) ξ / Real.pi
  rw [AlgChart.levi_const_mul 2 (hsP.contDiffAt_two hO hyc hzP), eP, key]
  simp_rw [← eQ, hA']
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

end GlobalTheory.FormPotBridge

open GlobalTheory.FormPotBridge in

theorem GlobalTheory.FormPotBridge.thW_isPotential : ∀ (D : D7) (O : Setup D) (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y)
    (R : O.Reads A T H) (c : O.s.Comp) (a : Fin ((T.M c).n + 1)) (u : D.what₂.Tau → Fin O.N → ℝ) (x : (T.M c).X a),
    GlobalTheory.ShFam.IsPotential (AnRead.all (O.var c).str ((R.man c).ε a) (O.var c).dim)
      (thW O.met.h0 c ((R.man c).ε a) u) ((R.man c).pt a '' ((T.F c).th u a).U x)
      (fun y => 2 * ((T.F c).th u a).φ x (((R.man c).pt a).symm y)) := by
  intro D O A T H R c a u x
  have hd : (O.var c).dim = Formalism.MainNotions.WeightThresholdDefs.dimY O.Y := by rw [O.dim_eq c]; rfl
  have h := isPotential_formOf (R.man c) hd (fun r σ => O.met.h0 c σ (O.ex r)) (fun r => -u r.1 r.2)
    ((R.an c).th u) a (T.th_pot c u a) x
  convert h using 1
  funext c' y ξ
  simp only [GlobalTheory.ShFam.thW, neg_mul, Finset.sum_neg_distrib]

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOffBoundary
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm.M GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LeviRed

open Filter Topology

variable {ι : Type} [Fintype ι]

theorem fderiv2_add {f g : (ι → ℂ) → ℝ} {z : ι → ℂ} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    fderiv ℝ (fderiv ℝ (fun v => f v + g v)) z = fderiv ℝ (fderiv ℝ f) z + fderiv ℝ (fderiv ℝ g) z := by
  have h1 : fderiv ℝ (fun v => f v + g v) =ᶠ[𝓝 z] fun v => fderiv ℝ f v + fderiv ℝ g v := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with v hfv hgv
    exact fderiv_add (hfv.differentiableAt (by norm_num)) (hgv.differentiableAt (by norm_num))
  rw [h1.fderiv_eq]
  exact fderiv_add ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

theorem fderiv2_const_mul {f : (ι → ℂ) → ℝ} {z : ι → ℂ} (c : ℝ) (hf : ContDiffAt ℝ 2 f z) :
    fderiv ℝ (fderiv ℝ (fun v => c * f v)) z = c • fderiv ℝ (fderiv ℝ f) z := by
  have h1 : fderiv ℝ (fun v => c * f v) =ᶠ[𝓝 z] fun v => c • fderiv ℝ f v := by
    filter_upwards [hf.eventually (by simp)] with v hfv
    exact fderiv_const_mul (hfv.differentiableAt (by norm_num)) c
  rw [h1.fderiv_eq]
  exact fderiv_const_smul ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)) c

theorem levi_add {f g : (ι → ℂ) → ℝ} {z : ι → ℂ} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (w : ι → ℂ) : ReciprocityTheory.AnForm.levi (fun v => f v + g v) z w =
      ReciprocityTheory.AnForm.levi f z w + ReciprocityTheory.AnForm.levi g z w := by
  simp only [ReciprocityTheory.AnForm.levi, fderiv2_add hf hg, ContinuousLinearMap.add_apply]
  ring

theorem levi_const_mul {f : (ι → ℂ) → ℝ} {z : ι → ℂ} (c : ℝ) (hf : ContDiffAt ℝ 2 f z) (w : ι → ℂ) :
    ReciprocityTheory.AnForm.levi (fun v => c * f v) z w = c * ReciprocityTheory.AnForm.levi f z w := by
  simp only [ReciprocityTheory.AnForm.levi, fderiv2_const_mul c hf, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem levi_sum {α : Type} (s : Finset α) {F : α → (ι → ℂ) → ℝ} {z : ι → ℂ}
    (hF : ∀ i ∈ s, ContDiffAt ℝ 2 (F i) z) (w : ι → ℂ) :
    ReciprocityTheory.AnForm.levi (fun v => ∑ i ∈ s, F i v) z w = ∑ i ∈ s, ReciprocityTheory.AnForm.levi (F i) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ReciprocityTheory.AnForm.levi]
  | insert i s hi ih =>
    have hs : ∀ i ∈ s, ContDiffAt ℝ 2 (F i) z := fun k hk => hF k (Finset.mem_insert_of_mem hk)
    simp only [Finset.sum_insert hi]
    rw [levi_add (hF i (Finset.mem_insert_self i s)) (ContDiffAt.sum fun k hk => hs k hk), ih hs]

theorem levi_congr {f g : (ι → ℂ) → ℝ} {z : ι → ℂ} (h : f =ᶠ[𝓝 z] g) (w : ι → ℂ) :
    ReciprocityTheory.AnForm.levi f z w = ReciprocityTheory.AnForm.levi g z w := by
  have h2 : fderiv ℝ f =ᶠ[𝓝 z] fderiv ℝ g := h.fderiv
  simp only [ReciprocityTheory.AnForm.levi, h2.fderiv_eq]

end GlobalTheory.LeviRed

open Filter Topology in

theorem GlobalTheory.LeviRed.levi_th_add_ph : Hypotheses2 → HypothesesH → OnObj fun D O _ T _ h => ∀ (c : O.Y.Comp) (a : Fin ((T.M c).n + 1)) (j : Fin ((T.M c).A a).n),
  ∀ y ∈ (((T.M c).A a).chart j).target, (((T.M c).A a).chart j).symm y ∉ (T.M c).Z a →
  ∀ u : D.what₂.Tau → Fin O.Y.N → ℝ, ∃ f : DV.Rt D.what₂.Tau O.N → (O.var c).Fn,
    (∀ x, (GlobalTheory.ShFam.Pad.divOf (O.Φ.C c) (O.ex x)).GeneratesAt (under ((h.man c).pt a ((((T.M c).A a).chart j).symm y))) (f x)) ∧
    ∀ w, GlobalTheory.Mean4O.leviAt ((T.M c).A a) ((T.F c).th u a + ReciprocityTheory.AnForm.M.LocPot.ofFun ((T.F c).ph u a)) j y w =
      ReciprocityTheory.AnForm.levi (fun v => ∑ x : DV.Rt D.what₂.Tau O.N, u x.1 x.2 *
        GlobalTheory.Mean4O.lnN (O.met.hm c none ((h.man c).ε a) (O.ex x)) (f x) ((h.man c).pt a ((((T.M c).A a).chart j).symm v))) y w := by
  intro p2 ph D O hc hR A T H h c a j y hy hZ u
  set I := h.man c
  set ch := ((T.M c).A a).chart j with hch
  set x0 := ch.symm y with hx0
  obtain ⟨Q, hQ, hlevi⟩ := (h.an c).th u a
  have hP : ∀ x, ∃ f : (O.var c).Fn, ∀ z ∈ (Q x).U x0,
      CartierDiv.GeneratesAt (Pad.divOf (O.Φ.C c) (O.ex x)) (under ((I.pt a) z)) f ∧
        PosAt (O.met.h0 c (I.ε a) (O.ex x)) ((I.pt a) z) ∧
        (Q x).φ x0 z = -lnN (O.met.h0 c (I.ε a) (O.ex x)) f ((I.pt a) z) := fun x => (hQ x).1 x0
  choose f hf using hP
  refine ⟨f, fun x => (hf x x0 ((Q x).mem_U x0)).1, fun w => ?_⟩

  have hZc : IsClosed ((T.M c).Z a) := ((T.M c).bd a).1
  set S : Set ((T.M c).X a) := (⋂ x, (Q x).U x0) ∩ ((T.M c).Z a)ᶜ with hS
  have hSo : IsOpen S := (isOpen_iInter_of_finite fun x => (Q x).isOpen_U x0).inter hZc.isOpen_compl
  have hW : ch.target ∩ ch.symm ⁻¹' S ∈ 𝓝 y := by
    refine (ch.isOpen_inter_preimage_symm hSo).mem_nhds ⟨hy, ?_⟩
    refine ⟨Set.mem_iInter.2 fun x => (Q x).mem_U x0, hZ⟩

  have h2inf : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
  have hθ : ContDiffAt ℝ 2 (((T.F c).th u a).φ x0 ∘ ch.symm) y := by
    have h1 := (T.th_pot c u a).1 x0 j
    refine (h1.contDiffAt ?_).of_le h2inf
    exact (ch.isOpen_inter_preimage_symm (((T.F c).th u a).isOpen_U x0)).mem_nhds ⟨hy, ((T.F c).th u a).mem_U x0⟩
  have hq : ∀ x, ContDiffAt ℝ 2 ((Q x).φ x0 ∘ ch.symm) y := fun x => by
    have h1 := (hQ x).2.1 x0 j
    refine (h1.contDiffAt ?_).of_le h2inf
    exact (ch.isOpen_inter_preimage_symm ((Q x).isOpen_U x0)).mem_nhds ⟨hy, (Q x).mem_U x0⟩
  have hφ : ContDiffAt ℝ 2 ((T.F c).ph u a ∘ ch.symm) y := by
    have h1 := GlobalTheory.HodgeChgSmooth.smoothOn_ph p2 ph D O hc hR A T H h c u a j
    refine (h1.contDiffAt ?_).of_le h2inf
    exact (ch.isOpen_inter_preimage_symm hZc.isOpen_compl).mem_nhds ⟨hy, hZ⟩

  set g : (Fin (WeightThresholdDefs.dimY O.Y) → ℂ) → ℝ := fun v => ∑ x : DV.Rt D.what₂.Tau O.N, u x.1 x.2 *
    lnN (O.met.hm c none (I.ε a) (O.ex x)) (f x) ((I.pt a) (ch.symm v)) with hg
  have hEq : (T.F c).ph u a ∘ ch.symm =ᶠ[𝓝 y]
      fun v => g v + ∑ x : DV.Rt D.what₂.Tau O.N, u x.1 x.2 * ((Q x).φ x0 ∘ ch.symm) v := by
    filter_upwards [hW] with v hv
    have hvZ : ch.symm v ∉ (T.M c).Z a := hv.2.2
    have hvU : ∀ x, ch.symm v ∈ (Q x).U x0 := fun x => Set.mem_iInter.1 hv.2.1 x
    simp only [Function.comp_apply, hg]
    rw [(h.an c).ph u a _ hvZ]
    unfold Setup.chg
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lnRatio_eq (hf x _ (hvU x)).1 (hc.posAt_hm c _ none _ _) (hc.referenceMetric_posAt c _ _ _), (hf x _ (hvU x)).2.2]
    ring
  have hgs : ContDiffAt ℝ 2 g y := by
    have h2 : ContDiffAt ℝ 2 (fun v => ((T.F c).ph u a ∘ ch.symm) v -
        ∑ x : DV.Rt D.what₂.Tau O.N, u x.1 x.2 * ((Q x).φ x0 ∘ ch.symm) v) y :=
      hφ.sub (ContDiffAt.sum fun x _ => contDiffAt_const.mul (hq x))
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [hEq] with v hv
    rw [hv]
    ring

  have hθl : ReciprocityTheory.AnForm.levi (((T.F c).th u a).φ x0 ∘ ch.symm) y w =
      ∑ x : DV.Rt D.what₂.Tau O.N, -u x.1 x.2 * ReciprocityTheory.AnForm.levi ((Q x).φ x0 ∘ ch.symm) y w :=
    hlevi j y hy w
  have hsum : ReciprocityTheory.AnForm.levi (fun v => ∑ x : DV.Rt D.what₂.Tau O.N, u x.1 x.2 * ((Q x).φ x0 ∘ ch.symm) v) y w =
      ∑ x : DV.Rt D.what₂.Tau O.N, u x.1 x.2 * ReciprocityTheory.AnForm.levi ((Q x).φ x0 ∘ ch.symm) y w := by
    rw [levi_sum _ (fun x _ => contDiffAt_const.mul (hq x))]
    exact Finset.sum_congr rfl fun x _ => levi_const_mul _ (hq x) w
  change ReciprocityTheory.AnForm.levi (fun v => (((T.F c).th u a).φ x0 ∘ ch.symm) v + ((T.F c).ph u a ∘ ch.symm) v) y w = _
  rw [levi_add hθ hφ, levi_congr hEq, levi_add hgs (ContDiffAt.sum fun x _ => contDiffAt_const.mul (hq x)), hsum, hθl]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

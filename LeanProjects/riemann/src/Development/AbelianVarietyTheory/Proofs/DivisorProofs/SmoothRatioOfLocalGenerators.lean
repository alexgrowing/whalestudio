import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPotentialPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVariety
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DivSec

theorem sub_eq_re_of_eqns : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (σ : F →+* ℂ) (C : Closeds Y.X) (n : Pts Y σ → ℝ) (V V' : Y.X.affineOpens) (t : Γ(Y.X, V.1)) (t' : Γ(Y.X, V'.1)) (f f' : Pts Y σ → ℝ), (∃ y : Y.X, y ∉ C) → (Scheme.IdealSheafData.vanishingIdeal C).ideal V = Ideal.span {t} → (Scheme.IdealSheafData.vanishingIdeal C).ideal V' = Ideal.span {t'} → (Y.an σ).SmoothOn (ptsIn Y.str σ V.1) f → (Y.an σ).SmoothOn (ptsIn Y.str σ V'.1) f' → (∀ z ∈ ptsIn Y.str σ V.1, n z ^ 2 = ‖ev Y.str σ V.1 t z‖ ^ 2 * Real.exp (-f z)) → (∀ z ∈ ptsIn Y.str σ V'.1, n z ^ 2 = ‖ev Y.str σ V'.1 t' z‖ ^ 2 * Real.exp (-f' z)) → ∀ y₀ ∈ ptsIn Y.str σ V.1 ∩ ptsIn Y.str σ V'.1, ∃ W : Set (Pts Y σ), IsOpen W ∧ y₀ ∈ W ∧ ∃ G : Pts Y σ → ℂ, (Y.an σ).HoloOn W G ∧ ∀ z ∈ W ∩ ptsIn Y.str σ V.1 ∩ ptsIn Y.str σ V'.1, f z - f' z = (G z).re := by
  intro F _ _ Y σ C n V V' t t' f f' hC ht ht' hf hf' hn hn' y₀ hy₀
  have hx : y₀.1 (IsLocalRing.closedPoint ℂ) ∈ V.1 ⊓ V'.1 := ⟨mem_ptsIn.1 hy₀.1, mem_ptsIn.1 hy₀.2⟩
  obtain ⟨h, hhW, hxh⟩ := V.2.exists_basicOpen_le (V := V.1 ⊓ V'.1) ⟨_, hx⟩ hx.1
  let Wa : Y.X.affineOpens := ⟨Y.X.basicOpen h, V.2.basicOpen h⟩
  have hWV : Wa.1 ≤ V.1 := hhW.trans inf_le_left
  have hWV' : Wa.1 ≤ V'.1 := hhW.trans inf_le_right
  have hy0W : y₀ ∈ ptsIn Y.str σ Wa.1 := mem_ptsIn.2 hxh
  haveI : Nonempty Wa.1 := ⟨⟨_, hxh⟩⟩
  have e1 : (Scheme.IdealSheafData.vanishingIdeal C).ideal Wa = Ideal.span {resG Y.X hWV t} := by
    rw [← Scheme.IdealSheafData.map_ideal _ (U := Wa) (V := V) hWV, ht, Ideal.map_span, Set.image_singleton]
    rfl
  have e2 : (Scheme.IdealSheafData.vanishingIdeal C).ideal Wa = Ideal.span {resG Y.X hWV' t'} := by
    rw [← Scheme.IdealSheafData.map_ideal _ (U := Wa) (V := V') hWV', ht', Ideal.map_span, Set.image_singleton]
    rfl
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 (e2.symm.trans e1)
  have hev : ∀ z ∈ ptsIn Y.str σ Wa.1,
      ev Y.str σ V.1 t z = ev Y.str σ V'.1 t' z * ev Y.str σ Wa.1 (u : Γ(Y.X, Wa.1)) z := by
    intro z hz
    rw [← ev_res hWV hz, ← hu, ev_mul, ev_res hWV' hz]
  set g := ev Y.str σ Wa.1 ((u : Γ(Y.X, Wa.1)) * u) with hg_def
  have hg0 : ∀ z ∈ ptsIn Y.str σ Wa.1, g z ≠ 0 := fun z hz =>
    ev_ne_zero hz (u.isUnit.mul u.isUnit)
  have hgn : ∀ z, ‖g z‖ = ‖ev Y.str σ Wa.1 (u : Γ(Y.X, Wa.1)) z‖ ^ 2 := fun z => by
    rw [hg_def, ev_mul, norm_mul, sq]
  obtain ⟨W₁, hW₁, hyW₁, hW₁s, G, hG, hGre⟩ :=
    ((Y.an σ).holoOn_ev Wa.1 ((u : Γ(Y.X, Wa.1)) * u)).exists_log (isOpen_ptsIn _) hy0W (hg0 y₀ hy0W)
  have hoff : ∀ z ∈ ptsIn Y.str σ Wa.1 ∩ {z | ¬ LiesIn z C}, f z - f' z = Real.log ‖g z‖ := by
    rintro z ⟨hz, hzC⟩
    have hzV := ptsIn_mono hWV hz
    have hzV' := ptsIn_mono hWV' hz
    have ht0 : ev Y.str σ V.1 t z ≠ 0 := fun h0 => hzC ((ev_eq_zero_iff ht hzV).1 h0)
    have hb : 0 < ‖ev Y.str σ Wa.1 (u : Γ(Y.X, Wa.1)) z‖ := norm_pos_iff.2 (ev_ne_zero hz u.isUnit)
    have ha : 0 < ‖ev Y.str σ V'.1 t' z‖ := by
      refine norm_pos_iff.2 fun h0 => ht0 ?_
      rw [hev z hz, h0, zero_mul]
    have e := (hn z hzV).symm.trans (hn' z hzV')
    rw [hev z hz, norm_mul, mul_pow, mul_assoc] at e
    have e' := mul_left_cancel₀ (pow_ne_zero 2 ha.ne') e
    have hl := congrArg Real.log e'
    rw [Real.log_mul (pow_ne_zero 2 hb.ne') (Real.exp_ne_zero _), Real.log_exp, Real.log_exp] at hl
    rw [hgn]
    linarith
  have hcont : ContinuousOn (fun z => f z - f' z - Real.log ‖g z‖) (ptsIn Y.str σ Wa.1) := by
    refine (((hf.continuousOn (isOpen_ptsIn _)).mono (ptsIn_mono hWV)).sub
      ((hf'.continuousOn (isOpen_ptsIn _)).mono (ptsIn_mono hWV'))).sub ?_
    exact ((continuousOn_ev _).norm).log fun z hz => norm_ne_zero_iff.2 (hg0 z hz)
  have hdense : Dense {z : Pts Y σ | ¬ LiesIn z C} := by
    obtain ⟨y, hy⟩ := hC
    have hd := (CxPtsDense.nonempty_and_dense F Y σ).2 C.compl ⟨y, hy⟩
    have hs : ptsIn Y.str σ C.compl = {z : Pts Y σ | ¬ LiesIn z C} :=
      Set.ext fun z => mem_ptsIn (U := C.compl)
    rwa [hs] at hd
  have hall : Set.EqOn (fun z => f z - f' z - Real.log ‖g z‖) 0 (ptsIn Y.str σ Wa.1) :=
    Set.EqOn.of_subset_closure (fun z hz => sub_eq_zero.2 (hoff z hz)) hcont continuousOn_const
      Set.inter_subset_left (hdense.open_subset_closure_inter (isOpen_ptsIn _))
  refine ⟨W₁, hW₁, hyW₁, G, hG, fun z hz => ?_⟩
  rw [hGre z hz.1.1]
  exact sub_eq_zero.1 (hall (hW₁s hz.1.1))

end GlobalTheory.DivSec

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix.RegLog

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem cInfAt_comp {f : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) {G : ℝ → ℝ} {T : Set ℝ}
    (hT : IsOpen T) (hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G T) (hf : ∀ z, f z ∈ T) :
    CInfAt (fun z => G (f z)) y := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have e : f y = F (fun a => ev p σ W (g a) y) := h₅.eq_of_nhds
  refine ⟨W, ι, inferInstance, g, G ∘ F, O ∩ F ⁻¹' T, h₁, h₄.continuousOn.isOpen_inter_preimage h₂ hT,
    ⟨h₃, show F _ ∈ T from e ▸ hf y⟩, hG.comp (h₄.mono inter_subset_left) fun v hv => hv.2, ?_⟩
  filter_upwards [h₅] with z hz
  simp only [Function.comp_apply, hz]

theorem cInfAt_normSq_ev {W : X.Opens} (g : Γ(X, W)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W) :
    CInfAt (fun z => ‖ev p σ W g z‖ ^ 2) y :=
  ⟨W, Unit, inferInstance, fun _ => g, fun v => ‖v ()‖ ^ 2, univ, hy, isOpen_univ, trivial,
    ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ ())).contDiffOn, EventuallyEq.rfl⟩

theorem cInfAt_nsq {B : LB X} (φ : Weight p σ B) (hφ : φ.IsCInf) (s : B.Sec) (y : CxPts p σ) :
    CInfAt (φ.nsq (secVal p σ s)) y := by
  have hi := mem_pick φ.isLB y
  have h := (cInfAt_normSq_ev (s.f (pick φ.isLB y)) hi).comp₂ (hφ _ y hi)
    (G := fun x => x.1 * Real.exp (-x.2)) (contDiff_fst.mul (Real.contDiff_exp.comp contDiff_snd.neg))
  refine h.congr ?_
  filter_upwards [(isOpen_ptsIn (p := p) (σ := σ) _).mem_nhds hi] with z hz
  exact φ.nsq_eq (secVal_mem s) hz

end GlobalTheory.Mix.RegLog

open GlobalTheory.Mix.RegLog in

theorem GlobalTheory.Mix.semiPosReg_addFn_log_nsq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (N : MLine p σ), N.φ.SemiPosReg D → ∀ (t : N.B.Sec) (δ : ℝ), 0 < δ → (∀ y, CInfAt (fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)) y) ∧ (N.φ.addFn fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)).SemiPosReg D := by
  intro k _ X p σ D N hN t δ hδ
  have hC : ∀ y, CInfAt (fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)) y := fun y =>
    cInfAt_comp ((cInfAt_nsq N.φ N.cInf t y).add (cInfAt_const δ y)) isOpen_compl_singleton
      Real.contDiffOn_log fun z => (add_pos_of_nonneg_of_pos (N.φ.nsq_nonneg _ z) hδ).ne'
  refine ⟨hC, ?_⟩
  intro i c y hy ξ
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (N.B.U i))
  have hm := mem_over c.e hy.1 hy.2
  have hf : ContDiffAt ℂ 2 (ev p σ (N.B.U i) (t.f i) ∘ c.e.symm) (c.e y) :=
    ReciprocityTheory.L2DbarEstimates.Y.contDiffAt_two_of_holo ho (c.holo _ (t.f i)) hm
  have hψ : ContDiffAt ℝ 2 (fun v => N.φ.φ i (c.e.symm v)) (c.e y) := N.cInf.contDiffAt c hy.1 hy.2
  have hψ' : ContDiffAt ℝ 2 (fun v => 1 * N.φ.φ i (c.e.symm v) + Real.log δ) (c.e y) :=
    (contDiffAt_const.mul hψ).add contDiffAt_const
  let w : Fin 2 → ReciprocityTheory.L2DbarEstimates.V D → ℝ := ![fun v => Complex.normSq ((ev p σ (N.B.U i) (t.f i) ∘ c.e.symm) v),
    fun v => Real.exp (1 * N.φ.φ i (c.e.symm v) + Real.log δ)]
  have hu : ∀ j, ContDiffAt ℝ 2 (w j) (c.e y) := by
    intro j; fin_cases j
    · exact ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp hf
    · exact Real.contDiff_exp.contDiffAt.comp _ hψ'
  have hl : ∀ j, ReciprocityTheory.L2DbarEstimates.LogPshAt D (w j) (c.e y) := by
    intro j; fin_cases j
    · exact ReciprocityTheory.L2DbarEstimates.logPshAt_normSq hf
    · refine ReciprocityTheory.L2DbarEstimates.logPshAt_exp hψ' fun ζ => ?_
      rw [ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul hψ 1 (Real.log δ) ζ, Complex.ofReal_one, one_mul]
      exact hN i c y hy ζ
  have hpos : 0 < ∑ j, w j (c.e y) := by
    simp only [Fin.sum_univ_two, w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (Real.exp_pos _)
  have key := ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg hu hl hpos ξ
  have e : (fun v => (((N.φ.addFn fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)).φ i (c.e.symm v) : ℝ) : ℂ))
      =ᶠ[𝓝 (c.e y)] fun v => ((Real.log (∑ j, w j v) : ℝ) : ℂ) := by
    filter_upwards [ho.mem_nhds hm] with v hv
    have hz : c.e.symm v ∈ ptsIn p σ (N.B.U i) := hv.2
    congr 1
    simp only [Weight.addFn, N.φ.nsq_eq (secVal_mem t) hz, Fin.sum_univ_two, w, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Function.comp_apply, secVal_apply]
    set a := N.φ.φ i (c.e.symm v)
    set b := ev p σ (N.B.U i) (t.f i) (c.e.symm v)
    have h1 : ‖b‖ ^ 2 * Real.exp (-a) + δ = Real.exp (-a) * (Complex.normSq b + Real.exp (1 * a + Real.log δ)) := by
      rw [Complex.normSq_eq_norm_sq, Real.exp_add, Real.exp_log hδ, one_mul, Real.exp_neg]
      field_simp
    rw [h1, Real.log_mul (Real.exp_pos _).ne' (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (Real.exp_pos _)).ne', Real.log_exp]
    ring
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e]
  exact key

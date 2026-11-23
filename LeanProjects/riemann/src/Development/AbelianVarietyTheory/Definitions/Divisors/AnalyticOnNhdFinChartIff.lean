import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V leviV)
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic
open scoped ContDiff

namespace GlobalTheory

open CxPts

namespace FinChart

variable {D : ℕ}

abbrev toV (D : ℕ) : (Fin D → ℂ) ≃L[ℝ] V D :=
  (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin D => ℂ).symm

theorem leviV_re_eq_levi {h : V D → ℝ} {z : Fin D → ℂ} (hh : ContDiffAt ℝ 2 h (toV D z))
    (ξ : Fin D → ℂ) : (leviV D (fun v => (h v : ℂ)) (toV D z) ξ).re = levi (h ∘ toV D) z ξ := by
  have h₁ : fderiv ℝ (h ∘ toV D) = fun w => (fderiv ℝ h (toV D w)).comp (toV D).toContinuousLinearMap :=
    funext fun _ => (toV D).comp_right_fderiv
  have h₂ := ((((hh.fderiv_right (m := 1) (by norm_num)).differentiableAt
    one_ne_zero).hasFDerivAt.comp z (toV D).hasFDerivAt).clm_comp
    (hasFDerivAt_const (toV D).toContinuousLinearMap z)).fderiv
  have e₁ : (∑ k, ((ξ k).re • ReciprocityTheory.L2DbarEstimates.bas D k +
      (ξ k).im • (Complex.I • ReciprocityTheory.L2DbarEstimates.bas D k))) = toV D ξ := by
    ext a
    apply Complex.ext <;> simp [ReciprocityTheory.L2DbarEstimates.bas, Pi.single_apply, Finset.sum_add_distrib]
  have e₂ : (∑ k, ((ξ k).re • (Complex.I • ReciprocityTheory.L2DbarEstimates.bas D k) -
      (ξ k).im • ReciprocityTheory.L2DbarEstimates.bas D k)) = toV D (Complex.I • ξ) := by
    ext a
    apply Complex.ext <;> simp [ReciprocityTheory.L2DbarEstimates.bas, Pi.single_apply, Finset.sum_sub_distrib]
  have := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_eq hh ξ
  rw [e₁, e₂] at this
  rw [levi, h₁, eq_div_iff four_ne_zero, this]
  erw [h₂]
  simp

theorem levi_half (h : (Fin D → ℂ) → ℝ) (z w : Fin D → ℂ) :
    levi (fun v => h v / 2) z w = levi h z w / 2 := by
  have e : (fun v => h v / 2) = (2⁻¹ : ℝ) • h := funext fun v => by simp [div_eq_inv_mul]
  simp only [e, levi, fderiv_const_smul_field, Pi.smul_apply]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

end FinChart

open FinChart

section SameForm

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {P Q T : LocPot X}

def SameForm (A : FinHolAtlas e X) (P Q : LocPot X) : Prop :=
  ∀ j, ∀ y ∈ (A.chart j).target, hessC (P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y =
    hessC (Q.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y

namespace SameForm

theorem refl (A : FinHolAtlas e X) (P : LocPot X) : SameForm A P P := fun _ _ _ => rfl

theorem symm (h : SameForm A P Q) : SameForm A Q P := fun j y hy => (h j y hy).symm

theorem trans (h : SameForm A P Q) (h' : SameForm A Q T) : SameForm A P T :=
  fun j y hy => (h j y hy).trans (h' j y hy)

theorem of_re (hQ : IsPotential A Q) (h : ∀ x, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∃ G : X → ℂ,
    A.HoloOn W G ∧ ∀ z ∈ W, P.φ x z = Q.φ x z + (G z).re) : SameForm A P Q := fun j y hy => by
  obtain ⟨W, hW, hx, G, hG, h⟩ := h ((A.chart j).symm y)
  refine (hessCGerm _ _ _ ?_).trans (ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ _ _
    (potSmoothAt A Q hQ _ j ⟨hy, Q.mem_U _⟩) (hG j y ⟨hy, hx⟩))
  exact eventually_of_mem (((A.chart j).isOpen_inter_preimage_symm hW).mem_nhds ⟨hy, hx⟩)
    fun w hw => h _ hw.2

variable {Φ Ψ : Fin e → LocPot X} (h : ∀ i, SameForm A (Φ i) (Ψ i))
include h

theorem locDens_eq {j : Fin A.n} {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) :
    locDens A Φ j y = locDens A Ψ j y := maDens_congr_hessC _ _ _ fun i => h i j y hy

theorem mInt_eq (g : X → ℝ) : mInt A Φ g = mInt A Ψ g := by
  unfold mInt integralWith
  split_ifs
  · exact Finset.sum_congr rfl fun j _ => MeasureTheory.setIntegral_congr_fun
      (A.chart j).open_target.measurableSet fun y hy => by simp only [locDens_eq h hy]
  · rfl

theorem mIntegrable_iff (g : X → ℝ) : MIntegrable A Φ g ↔ MIntegrable A Ψ g :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun hK => forall_congr' fun hc =>
    MeasureTheory.integrableOn_congr_fun (fun y hy => by simp only [locDens_eq h (hK hy)])
      hc.measurableSet

end SameForm

end SameForm

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

namespace AlgChart

variable (c c' : AlgChart p σ D) {S : Set (CxPts p σ)} {y : CxPts p σ}

def finChart : OpenPartialHomeomorph (CxPts p σ) (Fin D → ℂ) :=
  c.e.transHomeomorph (EuclideanSpace.equiv (Fin D) ℂ).toHomeomorph

@[simp] theorem finChart_source : c.finChart.source = c.e.source := rfl

theorem finChart_target : c.finChart.target = toV D ⁻¹' c.e.target := rfl

@[simp] theorem finChart_apply (y : CxPts p σ) (a : Fin D) : c.finChart y a = c.e y a := rfl

theorem toV_finChart (y : CxPts p σ) : toV D (c.finChart y) = c.e y := rfl

theorem finChart_symm_apply (z : Fin D → ℂ) : c.finChart.symm z = c.e.symm (toV D z) := rfl

theorem finChart_eq_ev (hy : y ∈ c.e.source) (a : Fin D) :
    c.finChart y a = ev p σ c.U (c.x a) y := c.apply_eq y hy a

theorem analyticOnNhd_finChart_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (hS : IsOpen S) (f : CxPts p σ → E) :
    AnalyticOnNhd ℂ (f ∘ c.finChart.symm) (c.finChart.target ∩ c.finChart.symm ⁻¹' S) ↔
      DifferentiableOn ℂ (f ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' S) :=
  (SCV.analyticOnNhd_iff_differentiableOn (c.finChart.isOpen_inter_preimage_symm hS)).trans
    ((EuclideanSpace.equiv (Fin D) ℂ).symm.comp_right_differentiableOn_iff (f := f ∘ c.e.symm)
      (s := c.e.target ∩ c.e.symm ⁻¹' S))

theorem contDiffOn_finChart_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : WithTop ℕ∞) (S : Set (CxPts p σ)) (f : CxPts p σ → E) :
    ContDiffOn ℝ n (f ∘ c.finChart.symm) (c.finChart.target ∩ c.finChart.symm ⁻¹' S) ↔
      ContDiffOn ℝ n (f ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' S) :=
  (toV D).contDiffOn_comp_iff (f := f ∘ c.e.symm) (s := c.e.target ∩ c.e.symm ⁻¹' S)

theorem analyticOnNhd_trans : AnalyticOnNhd ℂ (c'.finChart ∘ c.finChart.symm)
    (c.finChart.target ∩ c.finChart.symm ⁻¹' c'.finChart.source) :=
  (c.analyticOnNhd_finChart_iff c'.e.open_source _).2
    ((EuclideanSpace.equiv (Fin D) ℂ).differentiable.comp_differentiableOn (c.holo_trans c'))

theorem leviV_re_eq {f : CxPts p σ → ℝ} (hf : ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y))
    (ξ : Fin D → ℂ) : (leviV D (fun v => (f (c.e.symm v) : ℂ)) (c.e y) ξ).re =
      levi (f ∘ c.finChart.symm) (c.finChart y) ξ :=
  leviV_re_eq_levi (h := f ∘ c.e.symm) (z := c.finChart y) hf ξ

theorem exists_levi_eq (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) {f : CxPts p σ → ℝ}
    (hf : ContDiffAt ℝ 2 (f ∘ c'.finChart.symm) (c'.finChart y)) (w : Fin D → ℂ) :
    ∃ w', (w ≠ 0 → w' ≠ 0) ∧ levi (f ∘ c.finChart.symm) (c.finChart y) w =
      levi (f ∘ c'.finChart.symm) (c'.finChart y) w' := by
  have hl : c.finChart.symm (c.finChart y) = y := c.finChart.left_inv hy
  have hl' : c'.finChart.symm (c'.finChart y) = y := c'.finChart.left_inv hy'
  have hm : c.finChart y ∈ c.finChart.target ∩ c.finChart.symm ⁻¹' c'.finChart.source :=
    ⟨c.finChart.map_source hy, by rwa [mem_preimage, hl]⟩
  have hn := (c.finChart.isOpen_inter_preimage_symm c'.finChart.open_source).mem_nhds hm
  have hτ := c.analyticOnNhd_trans c' _ hm
  have hp : (c'.finChart ∘ c.finChart.symm) (c.finChart y) = c'.finChart y := congrArg _ hl
  have hτ' := c'.analyticOnNhd_trans c (c'.finChart y)
    ⟨c'.finChart.map_source hy', by rwa [mem_preimage, hl']⟩
  refine ⟨fderiv ℂ (c'.finChart ∘ c.finChart.symm) (c.finChart y) w, fun hw h0 => hw ?_, ?_⟩
  · have e : (c.finChart ∘ c'.finChart.symm) ∘ (c'.finChart ∘ c.finChart.symm) =ᶠ[𝓝 (c.finChart y)]
        id := eventually_of_mem hn fun v hv =>
      (congrArg c.finChart (c'.finChart.left_inv hv.2)).trans (c.finChart.right_inv hv.1)
    have := congrArg (· w) ((fderiv_comp _ (hp ▸ hτ'.differentiableAt)
      hτ.differentiableAt).symm.trans e.fderiv_eq)
    simpa [h0] using this.symm
  · refine (levi_congr ?_ w).trans ((levi_comp w hτ (hp ▸ hf)).trans (by rw [hp]))
    exact eventually_of_mem hn fun v hv => (congrArg f (c'.finChart.left_inv hv.2)).symm

end AlgChart

def IsAlgAtlas (A : FinHolAtlas D (CxPts p σ)) : Prop :=
  ∀ j, ∃ c : AlgChart p σ D, A.chart j = c.finChart

namespace AnRead

variable (R : AnRead p σ D)

def finAtlasOf (s : Finset R.ι) (hs : ∀ y, ∃ i ∈ s, y ∈ (R.chart i).e.source) :
    FinHolAtlas D (CxPts p σ) where
  n := s.card
  chart j := (R.chart (s.equivFin.symm j)).finChart
  cover y := by
    obtain ⟨i, hi, hy⟩ := hs y
    exact ⟨s.equivFin ⟨i, hi⟩, by rwa [Equiv.symm_apply_apply]⟩
  holo _ _ := AlgChart.analyticOnNhd_trans _ _

def finAtlas [CompactSpace (CxPts p σ)] : FinHolAtlas D (CxPts p σ) :=
  R.finAtlasOf R.exists_finite.choose R.exists_finite.choose_spec

theorem finAtlasOf_chart (s : Finset R.ι) (hs) (j : Fin s.card) :
    (R.finAtlasOf s hs).chart j = (R.chart (s.equivFin.symm j)).finChart := rfl

theorem isAlgAtlas_finAtlasOf (s : Finset R.ι) (hs) : IsAlgAtlas (R.finAtlasOf s hs) :=
  fun _ => ⟨_, rfl⟩

theorem isAlgAtlas_finAtlas [CompactSpace (CxPts p σ)] : IsAlgAtlas R.finAtlas :=
  R.isAlgAtlas_finAtlasOf _ _

end AnRead

namespace IsAlgAtlas

variable {A A' : FinHolAtlas D (CxPts p σ)} (hA : IsAlgAtlas A) {S : Set (CxPts p σ)}
include hA

def anRead : AnRead p σ D where
  ι := Fin A.n
  chart j := (hA j).choose
  cover y := (A.cover y).imp fun j hj => by rwa [(hA j).choose_spec] at hj

theorem chart_eq (j : Fin A.n) : A.chart j = (hA.anRead.chart j).finChart := (hA j).choose_spec

theorem isCompatChart (c : AlgChart p σ D) : IsCompatChart A c.finChart := fun j => by
  rw [hA.chart_eq j]
  exact ⟨AlgChart.analyticOnNhd_trans _ _, AlgChart.analyticOnNhd_trans _ _⟩

theorem compatible (hA' : IsAlgAtlas A') : A.Compatible A' :=
  ⟨fun j l => hA'.chart_eq l ▸ (hA.isCompatChart _ j).1,
    fun j l => hA.chart_eq l ▸ (hA'.isCompatChart _ j).1⟩

theorem holoOn_iff (R : AnRead p σ D) (hS : IsOpen S) {f : CxPts p σ → ℂ} :
    A.HoloOn S f ↔ R.HoloOn S f :=
  Iff.trans (forall_congr' fun j => by
    rw [hA.chart_eq j]
    exact AlgChart.analyticOnNhd_finChart_iff _ hS f) (AnRead.holoOn_iff hA.anRead R hS)

theorem smoothOn_iff (R : AnRead p σ D) (hS : IsOpen S) {f : CxPts p σ → ℝ} :
    A.SmoothOn S f ↔ R.SmoothOn S f :=
  Iff.trans (forall_congr' fun j => by
    rw [hA.chart_eq j]
    exact AlgChart.contDiffOn_finChart_iff _ _ S f) (AnRead.smoothOn_iff hA.anRead R hS)

theorem smooth_iff (R : AnRead p σ D) {f : CxPts p σ → ℝ} : A.Smooth f ↔ R.SmoothOn univ f :=
  hA.smoothOn_iff R isOpen_univ

theorem holoMap {k' : Type} [CommRing k'] {Y' : Scheme.{0}} {p' : Y' ⟶ Sp k'} {σ' : k' →+* ℂ}
    {D' : ℕ} {A' : FinHolAtlas D' (CxPts p' σ')} (hA' : IsAlgAtlas A') {f : Y' ⟶ Y}
    {m : CxPts p' σ' → CxPts p σ} (hm : ∀ z, (m z).1 = z.1 ≫ f) : HoloMap A' A m := by
  refine ⟨continuous_of_comp hm, fun j l => ?_⟩
  rw [hA.chart_eq l, hA'.chart_eq j]
  exact (AlgChart.analyticOnNhd_finChart_iff _ ((hA.anRead.chart l).e.open_source.preimage
    (continuous_of_comp hm)) ((hA.anRead.chart l).finChart ∘ m)).2
    ((EuclideanSpace.equiv (Fin D) ℂ).differentiable.comp_differentiableOn
      (AlgChart.holo_map hm _ _))

end IsAlgAtlas

namespace AnRead

variable (R R' : AnRead p σ D) {S : Set (CxPts p σ)}

theorem finAtlasOf_compatible (s : Finset R.ι) (hs) (s' : Finset R'.ι) (hs') :
    (R.finAtlasOf s hs).Compatible (R'.finAtlasOf s' hs') :=
  (R.isAlgAtlas_finAtlasOf s hs).compatible (R'.isAlgAtlas_finAtlasOf s' hs')

variable {R} in

theorem HoloOn.exists_log {g : CxPts p σ → ℂ} (h : R.HoloOn S g) (hS : IsOpen S) {y : CxPts p σ}
    (hy : y ∈ S) (h0 : g y ≠ 0) : ∃ W, IsOpen W ∧ y ∈ W ∧ W ⊆ S ∧ ∃ G : CxPts p σ → ℂ,
      R.HoloOn W G ∧ ∀ z ∈ W, (G z).re = Real.log ‖g z‖ := by
  refine ⟨S ∩ (fun z => g z * (g y)⁻¹) ⁻¹' Complex.slitPlane, ((h.continuousOn hS).mul
    continuousOn_const).isOpen_inter_preimage hS Complex.isOpen_slitPlane, ⟨hy, ?_⟩, inter_subset_left,
    fun z => Complex.log (g z * (g y)⁻¹) + Real.log ‖g y‖, fun i => ?_, fun z hz => ?_⟩
  · simp [mul_inv_cancel₀ h0]
  · exact (DifferentiableOn.clog ((h.mono inter_subset_left i).mul_const _)
      fun _ hv => hv.2.2).add_const _
  · have hz0 : g z ≠ 0 := left_ne_zero_of_mul (Complex.slitPlane_ne_zero hz.2)
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, ← div_eq_mul_inv, norm_div,
      Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 h0), sub_add_cancel]

variable [CompactSpace (CxPts p σ)]

theorem finAtlas_compatible : R.finAtlas.Compatible R'.finAtlas :=
  R.isAlgAtlas_finAtlas.compatible R'.isAlgAtlas_finAtlas

theorem isCompatChart_finAtlas (c : AlgChart p σ D) : IsCompatChart R.finAtlas c.finChart :=
  R.isAlgAtlas_finAtlas.isCompatChart c

theorem finAtlas_holoOn_iff (hS : IsOpen S) {f : CxPts p σ → ℂ} :
    R.finAtlas.HoloOn S f ↔ R.HoloOn S f := R.isAlgAtlas_finAtlas.holoOn_iff R hS

theorem finAtlas_smoothOn_iff (hS : IsOpen S) {f : CxPts p σ → ℝ} :
    R.finAtlas.SmoothOn S f ↔ R.SmoothOn S f := R.isAlgAtlas_finAtlas.smoothOn_iff R hS

theorem mInt_finAtlas_eq [T2Space (CxPts p σ)] {Φ : Fin D → LocPot (CxPts p σ)}
    (hΦ : ∀ i, IsPotential R.finAtlas (Φ i)) {g : CxPts p σ → ℝ} (hg : MIntegrable R.finAtlas Φ g) :
    MIntegrable R'.finAtlas Φ g ∧ mInt R.finAtlas Φ g = mInt R'.finAtlas Φ g :=
  mIntAtlasIndep _ _ (R.finAtlas_compatible R') Φ hΦ g hg

end AnRead

namespace Weight

open AnRead

variable {R : AnRead p σ D} {A : FinHolAtlas D (CxPts p σ)} {B B' : LB Y}

def locPot (φ : Weight p σ B) : LocPot (CxPts p σ) where
  U x := ptsIn p σ (B.U (pick φ.isLB x))
  isOpen_U _ := isOpen_ptsIn _
  mem_U := mem_pick φ.isLB
  φ x y := φ.φ (pick φ.isLB x) y / 2

def locSec (φ : Weight p σ B) (s : B.ι → CxPts p σ → ℂ) : CxPts p σ → CxPts p σ → ℂ :=
  fun x => s (pick φ.isLB x)

variable {φ : Weight p σ B}

theorem locPot_U (x : CxPts p σ) : φ.locPot.U x = ptsIn p σ (B.U (pick φ.isLB x)) := rfl

theorem locPot_φ (x y : CxPts p σ) : φ.locPot.φ x y = φ.φ (pick φ.isLB x) y / 2 := rfl

theorem locSec_apply (s : B.ι → CxPts p σ → ℂ) (x : CxPts p σ) :
    φ.locSec s x = s (pick φ.isLB x) := rfl

variable (φ) in

theorem half_eq {i j : B.ι} {y : CxPts p σ} (hi : y ∈ ptsIn p σ (B.U i))
    (hj : y ∈ ptsIn p σ (B.U j)) : φ.φ i y / 2 = φ.φ j y / 2 + Real.log ‖gv p σ B i j y‖ := by
  rw [φ.trans i j y hi hj, Real.log_pow]
  push_cast
  ring

variable (φ R) in

theorem exists_half_eq {i j : B.ι} {y : CxPts p σ} (hi : y ∈ ptsIn p σ (B.U i))
    (hj : y ∈ ptsIn p σ (B.U j)) : ∃ W, IsOpen W ∧ y ∈ W ∧ ∃ G : CxPts p σ → ℂ,
      R.HoloOn W G ∧ ∀ z ∈ W, φ.φ i z / 2 = φ.φ j z / 2 + (G z).re := by
  obtain ⟨W, hW, hy, hs, G, hG, e⟩ := (R.holoOn_ev _ (B.g i j).val).exists_log (isOpen_ptsIn _)
    (mem_ptsIn_inf.2 ⟨hi, hj⟩) (gv_ne_zero hi hj)
  exact ⟨W, hW, hy, G, hG, fun z hz => by
    rw [e z hz, φ.half_eq (mem_ptsIn_inf.1 (hs hz)).1 (mem_ptsIn_inf.1 (hs hz)).2, CxPts.gv]⟩

theorem IsSmooth.isPotential (h : φ.IsSmooth R) (hA : IsAlgAtlas A) : IsPotential A φ.locPot := by
  refine ⟨fun x => (hA.smoothOn_iff R (isOpen_ptsIn _)).2 fun c => (h _ c).div_const 2,
    fun x x' y hy => ?_⟩
  obtain ⟨W, hW, hy, G, hG, e⟩ := φ.exists_half_eq R hy.1 hy.2
  exact ⟨W, hW, hy, G, (hA.holoOn_iff R hW).2 hG, fun z hz => sub_eq_iff_eq_add'.2 (e z hz.1.1)⟩

theorem isSmooth_of_isPotential (hA : IsAlgAtlas A) (h : IsPotential A φ.locPot) :
    φ.IsSmooth R := fun i =>
  smoothOn_of_cover (T := φ.locPot.U) φ.locPot.isOpen_U (fun y _ => ⟨y, φ.locPot.mem_U y⟩) fun x =>
    SmoothOn.congr (f := fun y => 2 * φ.locPot.φ x y +
        Real.log (‖gv p σ B i (pick φ.isLB x) y‖ ^ 2))
      (fun c => (contDiffOn_const.mul (((hA.smoothOn_iff R (isOpen_ptsIn _)).1 (h.1 x)).mono
        inter_subset_right c)).add ((holoOn_ev_of_subset _ fun _ => mem_ptsIn_inf.2).smoothOn_log
          ((isOpen_ptsIn _).inter (isOpen_ptsIn _)) (fun _ hy => gv_ne_zero hy.1 hy.2) c))
      fun y hy => by
        rw [locPot_φ, φ.trans i _ y hy.1 hy.2]
        ring

variable (φ) in

theorem norm_mul_exp_eq_sqrt {s : B.ι → CxPts p σ → ℂ} (hs : s ∈ fibSec p σ B) {i : B.ι}
    {y : CxPts p σ} (hi : y ∈ ptsIn p σ (B.U i)) :
    ‖s i y‖ * Real.exp (-(φ.φ i y / 2)) = √(φ.nsq s y) := by
  rw [φ.nsq_eq hs hi, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), ← Real.exp_half,
    neg_div]

variable (φ) in

theorem isSection_of_isAlgAtlas (hA : IsAlgAtlas A) {s : B.ι → CxPts p σ → ℂ}
    (hs : s ∈ R.holSec B) : IsSection A φ.locPot (φ.locSec s) :=
  ⟨fun _ => (hA.holoOn_iff R (isOpen_ptsIn _)).2 (hs.2 _), fun _ _ _ hy =>
    (φ.norm_mul_exp_eq_sqrt hs.1 hy.1).trans (φ.norm_mul_exp_eq_sqrt hs.1 hy.2).symm⟩

variable (φ) in

theorem logNormSec_locSec (s : B.ι → CxPts p σ → ℂ) (y : CxPts p σ) :
    logNormSec φ.locPot (φ.locSec s) y = 1 / 2 * Real.log (φ.nsq s y) := by
  have e : φ.nsq s y = (‖φ.locSec s y y‖ * Real.exp (-φ.locPot.φ y y)) ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul, locPot_φ, nsq, locSec_apply]
    congr 2
    push_cast
    ring
  rw [e, Real.log_pow, logNormSec]
  push_cast
  ring

variable (φ) in

theorem exp_logNormSec_locSec {s : B.ι → CxPts p σ → ℂ} {y : CxPts p σ} (h : φ.nsq s y ≠ 0) :
    Real.exp (2 * logNormSec φ.locPot (φ.locSec s) y) = φ.nsq s y := by
  rw [logNormSec_locSec, ← mul_assoc, mul_one_div_cancel two_ne_zero, one_mul,
    Real.exp_log ((φ.nsq_nonneg s y).lt_of_ne' h)]

theorem IsSmooth.contDiffAt_finChart (h : φ.IsSmooth R) (c : AlgChart p σ D) {i : B.ι}
    {y : CxPts p σ} (hy : y ∈ c.e.source) (hi : y ∈ ptsIn p σ (B.U i)) :
    ContDiffAt ℝ 2 (φ.φ i ∘ c.finChart.symm) (c.finChart y) :=
  (((c.contDiffOn_finChart_iff _ _ _).2 ((h i).chart (isOpen_ptsIn _) c)).contDiffAt
    ((c.finChart.isOpen_inter_preimage_symm (isOpen_ptsIn _)).mem_nhds
      (mem_over c.e hy hi))).of_le (WithTop.coe_le_coe.2 le_top)

theorem IsSmooth.exists_levi_eq (h : φ.IsSmooth R) (c c' : AlgChart p σ D) {i j : B.ι}
    {y : CxPts p σ} (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) (hi : y ∈ ptsIn p σ (B.U i))
    (hj : y ∈ ptsIn p σ (B.U j)) (w : Fin D → ℂ) : ∃ w', (w ≠ 0 → w' ≠ 0) ∧
      levi (φ.φ i ∘ c.finChart.symm) (c.finChart y) w =
        levi (φ.φ j ∘ c'.finChart.symm) (c'.finChart y) w' := by
  obtain ⟨w', hw, e⟩ := c.exists_levi_eq c' hy hy' (h.contDiffAt_finChart c' hy' hi) w
  obtain ⟨W, hW, hyW, G, hG, e'⟩ := φ.exists_half_eq R hi hj
  have hm : c'.finChart y ∈ c'.finChart.target ∩ c'.finChart.symm ⁻¹' W := mem_over c'.e hy' hyW
  have hGa := (c'.analyticOnNhd_finChart_iff hW G).2 (hG.chart hW c') _ hm
  refine ⟨w', hw, e.trans ((levi_congr (ψ := fun v => (φ.φ j ∘ c'.finChart.symm) v +
    2 * ((G ∘ c'.finChart.symm) v).re) ?_ w').trans ?_)⟩
  · refine eventually_of_mem ((c'.finChart.isOpen_inter_preimage_symm hW).mem_nhds hm) fun v hv => ?_
    have := e' _ hv.2
    simp only [Function.comp_apply]
    linarith
  · rw [levi_add_smul (g := fun v => ((G ∘ c'.finChart.symm) v).re) 2
      (h.contDiffAt_finChart c' hy' hj) (Complex.reCLM.contDiff.contDiffAt.comp _
      (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt), levi_re_analytic hGa, mul_zero, add_zero]

theorem IsSmooth.leviV_re_eq (h : φ.IsSmooth R) (c : AlgChart p σ D) {i : B.ι} {y : CxPts p σ}
    (hy : y ∈ c.e.source) (hi : y ∈ ptsIn p σ (B.U i)) (ξ : Fin D → ℂ) :
    (leviV D (fun v => (φ.φ i (c.e.symm v) : ℂ)) (c.e y) ξ).re =
      levi (φ.φ i ∘ c.finChart.symm) (c.finChart y) ξ :=
  c.leviV_re_eq ((((h i).chart (isOpen_ptsIn _) c).contDiffAt ((isOpen_over _
    (isOpen_ptsIn _)).mem_nhds (mem_over c.e hy hi))).of_le (WithTop.coe_le_coe.2 le_top)) ξ

theorem IsSmooth.levi_locPot (h : φ.IsSmooth R) (hA : IsAlgAtlas A) {x : CxPts p σ} {j : Fin A.n}
    {z : Fin D → ℂ} (hz : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' φ.locPot.U x)
    (w : Fin D → ℂ) : ∃ (i : B.ι) (c : R.ι), ∃ y ∈ (R.chart c).e.source ∩ ptsIn p σ (B.U i), ∃ ξ,
      (w ≠ 0 → ξ ≠ 0) ∧ levi (φ.locPot.φ x ∘ (A.chart j).symm) z w =
        (leviV D (fun v => (φ.φ i ((R.chart c).e.symm v) : ℂ)) ((R.chart c).e y) ξ).re / 2 := by
  obtain ⟨c, hc⟩ := hA j
  rw [hc] at hz ⊢
  obtain ⟨c', hc'⟩ := R.cover (c.finChart.symm z)
  obtain ⟨ξ, hξ, e⟩ := h.exists_levi_eq c (R.chart c') (c.finChart.map_target hz.1) hc' hz.2 hz.2 w
  refine ⟨_, c', _, ⟨hc', hz.2⟩, ξ, hξ, ?_⟩
  rw [h.leviV_re_eq _ hc' hz.2, ← e, c.finChart.right_inv hz.1]
  exact levi_half _ z w

theorem IsSmooth.leviV_eq_locPot (h : φ.IsSmooth R) (hA : IsAlgAtlas A) {i : B.ι}
    {c : AlgChart p σ D} {y : CxPts p σ} (hy : y ∈ c.e.source ∩ ptsIn p σ (B.U i)) (ξ : Fin D → ℂ) :
    ∃ j, ∃ z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' φ.locPot.U y, ∃ w, (ξ ≠ 0 → w ≠ 0) ∧
      (leviV D (fun v => (φ.φ i (c.e.symm v) : ℂ)) (c.e y) ξ).re =
        2 * levi (φ.locPot.φ y ∘ (A.chart j).symm) z w := by
  obtain ⟨j, hj⟩ := A.cover y
  obtain ⟨c', hc'⟩ := hA j
  rw [hc'] at hj
  obtain ⟨w, hw, e⟩ := h.exists_levi_eq c c' hy.1 hj hy.2 (mem_pick φ.isLB y) ξ
  refine ⟨j, c'.finChart y, by rw [hc']; exact mem_over c'.e hj (φ.locPot.mem_U y), w, hw, ?_⟩
  rw [h.leviV_re_eq _ hy.1 hy.2, e, hc']
  exact ((congrArg (2 * ·) (levi_half _ _ w)).trans (mul_div_cancel₀ _ two_ne_zero)).symm

theorem IsSmooth.isPsh_iff (h : φ.IsSmooth R) (hA : IsAlgAtlas A) :
    IsPsh A φ.locPot ↔ φ.SemiPos R := by
  refine ⟨fun H i c y hy ξ => ?_, fun H x j z hz w => ?_⟩
  · obtain ⟨j, z, hz, w, -, e⟩ := h.leviV_eq_locPot hA hy ξ
    exact e ▸ mul_nonneg zero_le_two (H y j z hz w)
  · obtain ⟨i, c, y, hy, ξ, -, e⟩ := h.levi_locPot hA hz w
    exact e ▸ div_nonneg (H i c y hy ξ) zero_le_two

theorem IsSmooth.isPosPot_iff (h : φ.IsSmooth R) (hA : IsAlgAtlas A) :
    IsPosPot A φ.locPot ↔ φ.StrictPos R := by
  refine ⟨fun H i c y hy ξ h0 => ?_, fun H x j z hz w h0 => ?_⟩
  · obtain ⟨j, z, hz, w, hw, e⟩ := h.leviV_eq_locPot hA hy ξ
    exact e ▸ mul_pos two_pos (H y j z hz w (hw h0))
  · obtain ⟨i, c, y, hy, ξ, hξ, e⟩ := h.levi_locPot hA hz w
    exact e ▸ half_pos (H i c y hy ξ (hξ h0))

variable (φ) in

theorem sameForm_of_re (hA : IsAlgAtlas A) {Q : LocPot (CxPts p σ)} (hQ : IsPotential A Q)
    (h : ∀ x, ∃ i, x ∈ ptsIn p σ (B.U i) ∧ ∃ W, IsOpen W ∧ x ∈ W ∧ ∃ G : CxPts p σ → ℂ,
      R.HoloOn W G ∧ ∀ z ∈ W, φ.φ i z / 2 = Q.φ x z + (G z).re) : SameForm A φ.locPot Q :=
  SameForm.of_re hQ fun x => by
    obtain ⟨i, hi, W, hW, hx, G, hG, e⟩ := h x
    obtain ⟨W', hW', hx', G', hG', e'⟩ := φ.exists_half_eq R (mem_pick φ.isLB x) hi
    refine ⟨W ∩ W', hW.inter hW', ⟨hx, hx'⟩, _, holoOn_add A ((hA.holoOn_iff R hW).2 hG)
      ((hA.holoOn_iff R hW').2 hG'), fun z hz => ?_⟩
    rw [locPot_φ, e' z hz.2, e z hz.1, Complex.add_re, add_assoc]

variable (φ) in

theorem sameForm_of_eq (hA : IsAlgAtlas A) {Q : LocPot (CxPts p σ)} (hQ : IsPotential A Q)
    (h : ∀ x, ∃ i, x ∈ ptsIn p σ (B.U i) ∧ ∀ z, φ.φ i z / 2 = Q.φ x z) :
    SameForm A φ.locPot Q :=
  φ.sameForm_of_re (R := hA.anRead) hA hQ fun x => (h x).imp fun _ hi => ⟨hi.1, univ, isOpen_univ,
    trivial, fun _ => 0, fun _ => differentiableOn_const (0 : ℂ), fun z _ => by simp [hi.2 z]⟩

theorem IsSmooth.sameForm_tens {ψ : Weight p σ B'} (h' : ψ.IsSmooth R) (h : φ.IsSmooth R)
    (hA : IsAlgAtlas A) : SameForm A (ψ.tens φ).locPot (ψ.locPot + φ.locPot) :=
  sameForm_of_eq _ hA (isPotentialAdd A _ _ (h'.isPotential hA) (h.isPotential hA)) fun x =>
    ⟨(pick ψ.isLB x, pick φ.isLB x), mem_ptsIn_inf.2 ⟨mem_pick ψ.isLB x, mem_pick φ.isLB x⟩,
      fun _ => add_div _ _ _⟩

theorem IsSmooth.sameForm_zpow (h : φ.IsSmooth R) (hA : IsAlgAtlas A) (n : ℤ) :
    SameForm A (φ.zpow n).locPot (φ.locPot.zsmul n) :=
  sameForm_of_eq _ hA (isPotentialZsmul A n _ (h.isPotential hA)) fun x =>
    ⟨fun _ => pick φ.isLB x, mem_pow_iff.2 (mem_pick _ x), fun z => by
      rw [φ.zpow_φ n _ z]
      exact mul_div_assoc _ _ _⟩

theorem IsSmooth.sameForm_dual (h : φ.IsSmooth R) (hA : IsAlgAtlas A) :
    SameForm A φ.dual.locPot (φ.locPot.zsmul (-1)) :=
  sameForm_of_eq _ hA (isPotentialZsmul A _ _ (h.isPotential hA)) fun x =>
    ⟨(pick φ.isLB x : B.ι), mem_pick φ.isLB x, fun z => by
      simp [Weight.dual, LocPot.zsmul, locPot_φ, neg_div]⟩

variable (φ) in

theorem sameForm_addFn (A : FinHolAtlas D (CxPts p σ)) (u : CxPts p σ → ℝ) :
    SameForm A (φ.addFn u).locPot (φ.locPot + LocPot.ofFun fun y => u y / 2) :=
  fun _ _ _ => congrArg (hessC · _) (funext fun _ => add_div _ _ _)

theorem sameForm_ofFun (A : FinHolAtlas D (CxPts p σ)) (u : CxPts p σ → ℝ) :
    SameForm A (ofFun u).locPot (LocPot.ofFun fun y => u y / 2) := fun _ _ _ => rfl

theorem IsSmooth.sameForm_ofIso (h : φ.IsSmooth R) (hA : IsAlgAtlas A) (hB' : B'.IsLB)
    (w : LB.Iso B B') (hw : w.IsGen) : SameForm A (φ.ofIso hB' w hw).locPot φ.locPot :=
  sameForm_of_re (R := R) _ hA (h.isPotential hA) fun x => by
    have ha := mem_pick hB' x
    have hb := mem_pick φ.isLB x
    obtain ⟨W, hW, hx, hs, G, hG, e⟩ :=
      (R.holoOn_ev _ (w.s (pick hB' x, pick φ.isLB x)).val).exists_log (isOpen_ptsIn _)
        (mem_ptsIn_inf.2 ⟨ha, hb⟩) (ev_iso_ne_zero w hb ha)
    refine ⟨_, ha, W, hW, hx, G, hG, fun z hz => ?_⟩
    rw [Weight.ofIso, ofPairs_φ (mem_ptsIn_inf.1 (hs hz)).1 (mem_ptsIn_inf.1 (hs hz)).2, e z hz,
      locPot_φ, Real.log_pow]
    push_cast
    ring

theorem IsSmooth.sameForm_pull (h : φ.IsSmooth R) (hA : IsAlgAtlas A) {Y' : Scheme.{0}}
    {q : Y' ⟶ Sp k} {D' : ℕ} {A' : FinHolAtlas D' (CxPts q σ)} (hA' : IsAlgAtlas A') (f : Y' ⟶ Y)
    (hf : f ≫ p = q) : SameForm A' (φ.pull f hf).locPot
      (φ.locPot.pullback (PtsOver.map f hf _) (continuous_of_comp (f := f) fun _ => rfl)) :=
  sameForm_of_eq _ hA' (isPotentialPullback A A' _ (hA.holoMap hA' (f := f) fun _ => rfl) _
    (h.isPotential hA)) fun x => ⟨fun _ => pick φ.isLB (PtsOver.map f hf _ x),
      ptsIn_mono (fun _ hx => mem_iInter.2 fun _ => hx)
        ((mem_ptsIn_preimage (f := f) (m := PtsOver.map f hf _) fun _ => rfl).2 (mem_pick _ _)),
      fun z => congrArg (· / 2) (φ.pull_φ f hf _ z)⟩

theorem locDens_locPot (hA : IsAlgAtlas A) {L : Fin D → LB Y} {χ : ∀ a, Weight p σ (L a)}
    (h : ∀ a, (χ a).IsSmooth R) {j : Fin A.n} {z : Fin D → ℂ} (hz : z ∈ (A.chart j).target)
    {i : ∀ a, (L a).ι} (hi : ∀ a, (A.chart j).symm z ∈ ptsIn p σ ((L a).U (i a))) :
    locDens A (fun a => (χ a).locPot) j z =
      maDens (fun a v => (χ a).φ (i a) ((A.chart j).symm v) / 2) z :=
  maDens_congr_hessC _ _ _ fun a => by
    obtain ⟨W, hW, hx, G, hG, e⟩ := (χ a).exists_half_eq R (mem_pick (χ a).isLB _) (hi a)
    refine (hessCGerm _ _ _ ?_).trans (ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ _ _ ?_
      ((hA.holoOn_iff R hW).2 hG j z ⟨hz, hx⟩))
    · exact eventually_of_mem (((A.chart j).isOpen_inter_preimage_symm hW).mem_nhds ⟨hz, hx⟩)
        fun w hw => e _ hw.2
    · exact ((((hA.smoothOn_iff R (isOpen_ptsIn _)).2 (h a (i a)) j).contDiffAt
        (((A.chart j).isOpen_inter_preimage_symm (isOpen_ptsIn _)).mem_nhds ⟨hz, hi a⟩)).of_le
        (WithTop.coe_le_coe.2 le_top)).div_const 2

variable [CompactSpace (CxPts p σ)]

theorem isPotential_locPot (h : φ.IsSmooth R) : IsPotential R.finAtlas φ.locPot :=
  h.isPotential R.isAlgAtlas_finAtlas

theorem isPotential_locPot_iff : IsPotential R.finAtlas φ.locPot ↔ φ.IsSmooth R :=
  ⟨isSmooth_of_isPotential R.isAlgAtlas_finAtlas, isPotential_locPot⟩

variable (φ) in

theorem isSection_locSec {s : B.ι → CxPts p σ → ℂ} (hs : s ∈ R.holSec B) :
    IsSection R.finAtlas φ.locPot (φ.locSec s) := φ.isSection_of_isAlgAtlas R.isAlgAtlas_finAtlas hs

theorem isPsh_iff_semiPos (h : φ.IsSmooth R) : IsPsh R.finAtlas φ.locPot ↔ φ.SemiPos R :=
  h.isPsh_iff R.isAlgAtlas_finAtlas

theorem isPosPot_iff_strictPos (h : φ.IsSmooth R) : IsPosPot R.finAtlas φ.locPot ↔ φ.StrictPos R :=
  h.isPosPot_iff R.isAlgAtlas_finAtlas

theorem mInt_locPot_eq [T2Space (CxPts p σ)] {L : Fin D → LB Y} {χ : ∀ a, Weight p σ (L a)}
    (h : ∀ a, (χ a).IsSmooth R) (R' : AnRead p σ D) {g : CxPts p σ → ℝ} (hg : Continuous g) :
    MIntegrable R.finAtlas (fun a => (χ a).locPot) g ∧
      mInt R.finAtlas (fun a => (χ a).locPot) g = mInt R'.finAtlas (fun a => (χ a).locPot) g :=
  have hΦ := fun a => isPotential_locPot (h a)
  have hi := mIntegrableCont _ _ hΦ g hg
  ⟨hi, (R.mInt_finAtlas_eq R' hΦ hi).2⟩

end Weight

namespace ProjAn

open ProjSpace

variable (k σ) (N : ℕ)

def finAtlas : FinHolAtlas N (CxPts (PSpace.str k N) σ) := (AnRead.all _ σ N).finAtlas

example : IsPotential (finAtlas k σ N) (fsO1 k σ N).locPot ∧ ∀ a,
    IsSection (finAtlas k σ N) (fsO1 k σ N).locPot
      ((fsO1 k σ N).locSec (secVal _ σ (coord k N a))) :=
  ⟨Weight.isPotential_locPot (Weight.isSmooth_fsBasis _ _ _ _ _),
    fun _ => Weight.isSection_locSec _ (AnRead.secVal_mem_holSec _ _)⟩

example : ∃ j, ((finAtlas k σ N).chart j).target.Nonempty := by
  obtain ⟨j, hj⟩ := (finAtlas k σ N).cover (projPt σ ⟨fun _ => 1, by
    rw [Ideal.eq_top_iff_one]; exact Ideal.subset_span ⟨0, rfl⟩⟩)
  exact ⟨j, _, OpenPartialHomeomorph.map_source _ hj⟩

example (x : CxPts (PSpace.str k N) σ) (v : Unimodular ℂ N) (i : Fin (N + 1))
    (e : pick (fsO1 k σ N).isLB x = i) (hi : v.1 i ≠ 0) :
    (fsO1 k σ N).locPot.φ x (projPt σ v) = Real.log √(∑ a, ‖v.1 a / v.1 i‖ ^ 2) := by
  rw [Weight.locPot_φ, e, fubiniStudyWeight_projPoint k σ N v i hi,
    Real.log_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

end ProjAn

example (y : CxPts p σ) : logNormSec (Weight.ofFun fun _ : CxPts p σ => Real.log 4).locPot
    ((Weight.ofFun fun _ => Real.log 4).locSec fun _ _ => 1) y = -Real.log 2 := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  simp [logNormSec, Weight.locPot, Weight.locSec, Weight.ofFun, this]

example (z : Fin 1 → ℂ) :
    maDens (fun _ v => (∑ a, Complex.normSq (v a)) / 2) z = 1 / Real.pi := by
  have e : (fun v : Fin 1 → ℂ => (∑ a, Complex.normSq (v a)) / 2) =
      fun v => 2⁻¹ * ∑ a, Complex.normSq (v a) := funext fun _ => div_eq_inv_mul _ _
  rw [maDens, ReciprocityTheory.AnForm.A.mdisc_const, e, hessC_const_mul',
    ReciprocityTheory.AnForm.A.hessC_sum_normSq]
  simp
  ring

end GlobalTheory

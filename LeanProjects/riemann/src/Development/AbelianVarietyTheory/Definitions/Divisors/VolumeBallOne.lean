import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.InhHasFDerivAtNormSq
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic
open scoped ContDiff
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.AnReadModel

open GlobalTheory.CxPts GlobalTheory.AnRead

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem volume_ball_one : volume (Metric.ball (0 : V 1) 1) = ENNReal.ofReal Real.pi := by
  have h : Module.finrank ℝ (V 1) = 2 * 1 := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (V 1)]; simp
  rw [InnerProductSpace.volume_ball_of_dim_even h]
  simp

theorem topInt_pos [SmoothOfRelativeDimension D p] [SecondCountableTopology (CxPts p σ)] {B : LB Y}
    (K : CanonLB p D) {φ : Weight p σ B} {f : (tens K.bundle B).ι → CxPts p σ → ℂ}
    {R : AnRead p σ D} (hφ : φ.IsSmooth R) (hf : f ∈ R.holSec (tens K.bundle B))
    {j : (tens K.bundle B).ι} {y : CxPts p σ} (h0 : f j y ≠ 0) : 0 < R.topInt K φ f := by
  have hj : y ∈ ptsIn p σ ((tens K.bundle B).U j) := by
    by_contra h; exact h0 (hf.1.2 j y h)
  obtain ⟨a, b⟩ := j
  obtain ⟨ha, hb⟩ := mem_ptsIn_inf.1 hj
  obtain ⟨i, hi⟩ := R.cover y
  set c := R.chart i
  let S := ptsIn p σ (c.U ⊓ K.bundle.U a) ∩ ptsIn p σ (B.U b)
  have hS : IsOpen S := (isOpen_ptsIn _).inter (isOpen_ptsIn _)
  have hc : ContinuousOn (fun v => c.topDens K φ f (c.e.symm v)) (c.e.target ∩ c.e.symm ⁻¹' S) := by
    have h₁ := (holoOn_ev_of_subset (R := R) (c.isFrame.ratio (K.isFrame a)).val
      (inter_subset_left (t := ptsIn p σ (B.U b)))).mul
      ((hf.2 (a, b)).mono
        fun _ hz => mem_ptsIn_inf.2 ⟨(mem_ptsIn_inf.1 hz.1).2, hz.2⟩) i
    have h₂ := (hφ b).mono (inter_subset_right : S ⊆ _) i
    exact (continuousOn_const.mul ((h₁.continuousOn.norm.pow 2).mul h₂.continuousOn.neg.rexp)).congr
      fun v hv => c.topDens_eq K φ hf.1 (c.e.map_target hv.1) (mem_ptsIn_inf.1 hv.2.1).2 hv.2.2
  have hyS : y ∈ S := ⟨mem_ptsIn_inf.2 ⟨c.source_subset hi, ha⟩, hb⟩
  have hpos : 0 < c.topDens K φ f (c.e.symm (c.e y)) := by
    rw [c.e.left_inv hi, c.topDens_eq K φ hf.1 hi ha hb]
    have : c.topCoeff K f a b y ≠ 0 :=
      mul_ne_zero (rv_ne_zero _ _ (c.source_subset hi) ha) h0
    positivity
  have ho := isOpen_over c.e hS
  have hO := hc.isOpen_inter_preimage ho (isOpen_Ioi (a := c.topDens K φ f (c.e.symm (c.e y)) / 2))
  have hA : IsOpen (c.e.source ∩ S) := c.e.open_source.inter hS
  refine lt_of_lt_of_le ?_ (measure_mono (subset_univ (c.e.source ∩ S)))
  rw [R.topMeasure_apply K φ f c hA.measurableSet inter_subset_left, c.e.image_source_inter_eq']
  refine lt_of_lt_of_le ?_ (lintegral_mono_set inter_subset_left (s := (c.e.target ∩ c.e.symm ⁻¹' S) ∩
    (fun v => c.topDens K φ f (c.e.symm v)) ⁻¹' Ioi (c.topDens K φ f (c.e.symm (c.e y)) / 2)))
  refine lt_of_lt_of_le ?_ (setLIntegral_mono' hO.measurableSet
    (f := fun _ => ENNReal.ofReal (c.topDens K φ f (c.e.symm (c.e y)) / 2))
    fun v hv => ENNReal.ofReal_le_ofReal (le_of_lt hv.2))
  rw [setLIntegral_const]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (half_pos hpos)).ne'
    (hO.measure_pos _ ⟨c.e y, mem_over c.e hi hyS, half_lt_self hpos⟩).ne'

open ProjSpace in

theorem topInt_jac (N : ℕ) (K : CanonLB (PSpace.str k N) N) (R : AnRead (PSpace.str k N) σ N) :
    0 < R.topInt K ((ProjAn.fsO1 k σ N).pow (N + 1)) (secVal _ σ (K.jacSec (coord k N))) ∧
      R.topInt K ((ProjAn.fsO1 k σ N).pow (N + 1)) (secVal _ σ (K.jacSec (coord k N))) < ⊤ := by
  have hs := (Weight.isSmooth_fsBasis (R := R) (O1_isLB k N) (coord k N)
    (iSup_nonzeroLocus_coord k N) 1 (by simp)).zpow ((N + 1 : ℕ) : ℤ)
  refine ⟨?_, topInt_lt_top K hs (R.secVal_mem_holSec _)⟩
  let y : CxPts (PSpace.str k N) σ := projPt σ ⟨fun _ => 1, (Ideal.eq_top_iff_one _).2
    (Ideal.subset_span ⟨0, rfl⟩)⟩
  obtain ⟨_, h⟩ := ProjAn.noCommonZero_jac k σ N K _ y (mem_pick (K.isLB_adj (O1_isLB k N) _) y)
  exact topInt_pos K hs (R.secVal_mem_holSec _) h

def X (a : Fin D) : CxPts (CanonLB.affStr k D) σ → ℂ :=
  ev _ σ ⊤ (CanonLB.polyFn (MvPolynomial.X a))

def origin : CxPts (CanonLB.affStr k D) σ :=
  ofHom (isAffineOpen_top _) ((MvPolynomial.eval₂Hom σ fun _ => 0).comp
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin D) k))).hom.hom) fun a => by
    have := RingHom.congr_fun (CanonLB.polyFn_comp k D) a
    rw [← this]
    simp [CanonLB.polyFn]

theorem exists_std (y : CxPts (CanonLB.affStr k D) σ) :
    ∃ c : AlgChart (CanonLB.affStr k D) σ D, y ∈ c.e.source ∧
      ∀ z ∈ c.e.source, ∀ a, c.e z a = X a z := by
  have he : MvPolynomial.eval₂Hom (algX (CanonLB.affStr k D) ⊤)
      (fun a => CanonLB.polyFn (MvPolynomial.X a)) = CanonLB.polyFn :=
    MvPolynomial.ringHom_ext (fun a => (MvPolynomial.eval₂Hom_C _ _ a).trans
      (RingHom.congr_fun (CanonLB.polyFn_comp k D) a).symm) fun a => MvPolynomial.eval₂Hom_X' _ _ a
  have het : (MvPolynomial.eval₂Hom (algX (CanonLB.affStr k D) ⊤)
      (fun a => CanonLB.polyFn (MvPolynomial.X a))).Etale := by
    rw [he]
    exact RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin D) k))).inv)
  obtain ⟨⟨e, U, hU, x, hx, h₁, h₂, h₃⟩, hy, hU', hx'⟩ := AlgChart.exists_of_etale
    (isAffineOpen_top _) _ het (mem_ptsIn_top (y := y))
  dsimp only at hU'
  subst hU'
  dsimp only at hx'
  subst hx'
  exact ⟨_, hy, h₂⟩

theorem holo_X (R : AnRead (CanonLB.affStr k D) σ D) (a : Fin D) : R.HoloOn univ (X a) :=
  holoOn_ev_of_subset _ fun _ _ => mem_ptsIn_top

theorem not_holo_conj (R : AnRead (CanonLB.affStr k D) σ D) (a : Fin D) :
    ¬ R.HoloOn univ fun z => starRingEnd ℂ (X a z) := fun h => by
  obtain ⟨c, hy, hc⟩ := exists_std (origin (k := k) (σ := σ) (D := D))
  have ht := c.e.open_target.mem_nhds (c.e.map_source hy)
  have h1 := (h.chart isOpen_univ c).differentiableAt (x := c.e origin) (by simpa using ht)
  have h2 : DifferentiableAt ℂ (fun v : V D => starRingEnd ℂ (v a)) (c.e origin) :=
    h1.congr_of_eventuallyEq (eventually_of_mem ht fun v hv => by
      simp only [Function.comp_apply, ← hc _ (c.e.map_target hv), c.e.right_inv hv])
  have h3 := ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt (j := a) h2
  rw [ReciprocityTheory.L2DbarEstimates.wdb_conj (by fun_prop), ReciprocityTheory.L2DbarEstimates.inh_wd_coord] at h3
  simp at h3

def sq (t : ℝ) (z : CxPts (CanonLB.affStr k D) σ) : ℝ := t * ∑ a, Complex.normSq (X a z)

theorem smooth_sq (R : AnRead (CanonLB.affStr k D) σ D) (t : ℝ) :
    (Weight.ofFun (sq t)).IsSmooth R := Weight.isSmooth_ofFun fun i =>
  contDiffOn_const.mul (ContDiffOn.sum (f := fun a v => Complex.normSq (X a ((R.chart i).e.symm v)))
    fun a _ => by
      simp only [Complex.normSq_eq_norm_sq]
      exact (contDiffOn_real (isOpen_over _ isOpen_univ) (holo_X R a i)).norm_sq ℂ)

theorem levi_sq (c : AlgChart (CanonLB.affStr k D) σ D) (t : ℝ) {y} (hy : y ∈ c.e.source)
    (ξ : Fin D → ℂ) :
    (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => (sq t (c.e.symm v) : ℂ)) (c.e y) ξ).re =
      t * ∑ a, Complex.normSq (∑ j, ReciprocityTheory.L2DbarEstimates.wd D j (X a ∘ c.e.symm) (c.e y) * ξ j) := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := CanonLB.affStr k D) (σ := σ) ⊤)
  have hg (a) : ContDiffAt ℂ 2 (X a ∘ c.e.symm) (c.e y) :=
    ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ ho (c.holo ⊤ _)).contDiffAt
      (ho.mem_nhds (mem_over _ hy mem_ptsIn_top))).of_le (by norm_cast)
  have hu (a) := ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp (hg a)
  have e := ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul (ContDiffAt.sum (s := Finset.univ) fun a _ => hu a) t 0 ξ
  rw [ReciprocityTheory.L2DbarEstimates.leviV_ofReal_sum hu] at e
  simp only [ReciprocityTheory.L2DbarEstimates.leviV_normSq_comp (hg _), add_zero] at e
  refine (congrArg Complex.re e).trans ?_
  rw [← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem semiPos_sq (R : AnRead (CanonLB.affStr k D) σ D) : (Weight.ofFun (sq 1)).SemiPos R :=
  fun _ c _ hy ξ => (mul_nonneg zero_le_one (Finset.sum_nonneg fun _ _ =>
    Complex.normSq_nonneg _)).trans_eq (levi_sq (R.chart c) 1 hy.1 ξ).symm

theorem not_semiPos_sq (a : Fin D) :
    ¬ (Weight.ofFun (sq (-1))).SemiPos (AnRead.all (CanonLB.affStr k D) σ D) := fun h => by
  obtain ⟨c, hy, hc⟩ := exists_std (origin (k := k) (σ := σ) (D := D))
  have ht := c.e.open_target.mem_nhds (c.e.map_source hy)
  have h1 := (h PUnit.unit c _ ⟨hy, mem_ptsIn_top⟩ fun _ => 1).trans_eq (levi_sq c (-1) hy _)
  have e (b j : Fin D) : ReciprocityTheory.L2DbarEstimates.wd D j (X b ∘ c.e.symm) (c.e origin) =
      if j = b then 1 else 0 := by
    rw [← ReciprocityTheory.L2DbarEstimates.inh_wd_coord D j b (c.e origin)]
    exact ReciprocityTheory.L2DbarEstimates.wd_congr (eventually_of_mem ht fun v hv => by
      simp only [Function.comp_apply, ← hc _ (c.e.map_target hv), c.e.right_inv hv])
  simp only [e, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  have : (0 : ℝ) < D := Nat.cast_pos.2 a.pos
  linarith

end GlobalTheory.AnReadModel

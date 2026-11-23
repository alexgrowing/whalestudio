import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradFPfA
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

open Filter Topology Set
open scoped ContDiff

namespace GlobalTheory.HessPull

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.AR.Up.RGF in

theorem cHess_comp_apply (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (U : Set (V n)) (hU : IsOpen U)
    (v : V n) (hv : v ∈ U) (hF : ContDiffOn ℂ 2 F U) (hg : ContDiffAt ℝ 2 g (F v)) (j k : Fin n) :
    cHess n (g ∘ F) v j k = ∑ a, ∑ b,
      cHess d g (F v) b a * fderiv ℂ F v (bas n j) b *
        (starRingEnd ℂ) (fderiv ℂ F v (bas n k) a) := by
  have hFd : ∀ y ∈ U, HasFDerivAt F (fderiv ℂ F y) y := fun y hy =>
    (((hF.differentiableOn (by norm_num)) y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  have hgev : ∀ᶠ y in 𝓝 v, ContDiffAt ℝ 2 g (F y) :=
    (hFd v hv).continuousAt.eventually (hg.eventually (by simp))
  have hwdb : ∀ k, wdb n k (g ∘ F) =ᶠ[𝓝 v]
      fun y => ∑ a, wdb d a g (F y) * (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a) := by
    intro k
    filter_upwards [hgev, hU.mem_nhds hv] with y hy hyU
    exact gc_wdb_comp n d g F _ y (hy.differentiableAt (by simp)) (hFd y hyU) k
  have hD : DifferentiableAt ℝ (fderiv ℝ g) (F v) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hWg : ∀ a, DifferentiableAt ℝ (wdb d a g) (F v) := by
    intro a
    show DifferentiableAt ℝ (fun y => (fderiv ℝ g y (bas d a) +
      Complex.I * fderiv ℝ g y (Complex.I • bas d a)) / 2) (F v)
    have h1 := hD.clm_apply (differentiableAt_const (bas d a))
    have h2 := hD.clm_apply (differentiableAt_const (Complex.I • bas d a))
    have h3 := (h1.add (h2.const_mul Complex.I)).mul_const ((2 : ℂ)⁻¹)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp [div_eq_mul_inv]
  have hWa : ∀ a, DifferentiableAt ℝ (fun y => wdb d a g (F y)) v := fun a =>
    (hWg a).comp v ((hFd v hv).restrictScalars ℝ).differentiableAt
  have hDF : DifferentiableAt ℂ (fun y => fderiv ℂ F y) v :=
    ((hF.fderiv_of_isOpen hU (m := 1) (by norm_num)).contDiffAt (hU.mem_nhds hv)).differentiableAt
      (by norm_num)
  have hPa : ∀ k a, DifferentiableAt ℂ (fun y => fderiv ℂ F y (bas n k) a) v := fun k a =>
    (differentiableAt_piLp 2).1 (hDF.clm_apply (differentiableAt_const _)) a
  have hCa : ∀ k a, DifferentiableAt ℝ
      (fun y => (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)) v := by
    intro k a
    have := Complex.conjCLE.differentiableAt.comp v ((hPa k a).restrictScalars ℝ)
    simpa [Function.comp_def] using this
  show wd n j (wdb n k (g ∘ F)) v = _
  rw [wd_congr n j _ _ v (hwdb k),
    fc_wd_sum n j Finset.univ (fun a y => wdb d a g (F y) *
      (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)) v (fun a _ => (hWa a).mul (hCa k a))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [wd_mul' n j _ _ v (hWa a) (hCa k a), wd_conj', fc_wdb_holo n _ v (hPa k a) j, map_zero,
    mul_zero, add_zero]
  have := gc_wd_comp n d (wdb d a g) F (fderiv ℂ F v) v (hWg a) (hFd v hv) j
  rw [show (fun y => wdb d a g (F y)) = wdb d a g ∘ F from rfl, this, Finset.sum_mul]
  rfl

end GlobalTheory.HessPull

namespace GlobalTheory.HessPull

open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open GlobalTheory.ChartGlue

theorem hess_pull_factor : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k)
    (f : Y ⟶ B) (w : f ≫ q = p) (σ : k →+* ℂ) (D d : ℕ) (c : AlgChart p σ D) (c' : AlgChart q σ d)
    (y : CxPts p σ), y ∈ c.e.source → PtsOver.map f w (spMap σ) y ∈ c'.e.source →
    ∃ (P : Matrix (Fin D) (Fin d) ℂ) (Q : Matrix (Fin d) (Fin D) ℂ), ∀ (A : HermLB q)
      (i : (A.pull f w).B.ι), y ∈ ptsIn p σ ((A.pull f w).B.U i) →
        ∃ K : Matrix (Fin d) (Fin d) ℂ, c.hess ((A.pull f w).φ σ) i y = P * K * Q := by
  intro k _ B Y q p f w σ D d c c' y hy hy'
  set m := PtsOver.map f w (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ f := fun _ => rfl
  set F : V D → V d := c'.e ∘ m ∘ c.e.symm with hFdef
  set U := c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c'.e.source)
  have hU : IsOpen U := isOpen_over c.e (c'.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c.e y ∈ U := mem_over c.e hy hy'
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c c'
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c.e y) = c'.e (m y) := by
    simp only [hFdef, Function.comp_apply, c.e.left_inv hy]
  refine ⟨Matrix.of fun j b => fderiv ℂ F (c.e y) (bas D j) b,
    Matrix.of fun a k => (starRingEnd ℂ) (fderiv ℂ F (c.e y) (bas D k) a), ?_⟩
  intro A i hi
  have him : m y ∈ ptsIn q σ (A.B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hi PUnit.unit
  set g : V d → ℂ := fun v => ((A.φ σ).φ (i PUnit.unit) (c'.e.symm v) : ℂ)
  have hg : ContDiffAt ℝ 2 g (F (c.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((A.cInf σ).contDiffAt c' hy' him)
  have e : (fun v => (((A.pull f w).φ σ).φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ (A.φ σ) f w i (c.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c'.e.left_inv hv.2]
    exact congrArg _ this
  refine ⟨cHess d g (F (c.e y)), ?_⟩
  show cHess D _ (c.e y) = _
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e]
  ext j k
  rw [cHess_comp_apply D d g F U hU _ hyU hF hg j k, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end GlobalTheory.HessPull

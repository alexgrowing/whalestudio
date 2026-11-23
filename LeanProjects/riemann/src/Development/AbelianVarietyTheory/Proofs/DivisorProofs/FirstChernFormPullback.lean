import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartCombinationPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackChartMetricBlockForm
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false
noncomputable section
open GlobalTheory.Points GlobalTheory.ChernTop GlobalTheory.HermFrame
open scoped ComplexConjugate
namespace GlobalTheory.ChernPull
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory.GoodMetric (coordVec)

theorem coe_matForm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (matForm n M : Alt n) = kappa • ∑ a, ∑ b, M a b • (dz a * dzb b) := by
  simp only [matForm, LinearMap.coe_mk, AddHom.coe_mk, rowForm, Fintype.linearCombination_apply,
    Subalgebra.coe_smul, AddSubmonoidClass.coe_finsetSum, sym]

theorem pull_matForm {n d : ℕ} (F : V n →L[ℂ] V d) (K : Matrix (Fin d) (Fin d) ℂ) :
    pull F (matForm d K : Alt d) = (matForm n (Matrix.of (fun j b => F (coordVec j) b) * K *
      Matrix.of (fun a l => conj (F (coordVec l) a))) : Alt n) := by
  rw [coe_matForm, coe_matForm, map_smul]
  congr 1
  simp only [map_sum, map_smul, map_mul, (pull_dz F _).1, (pull_dz F _).2, Finset.sum_mul, Finset.mul_sum,
    smul_mul_smul_comm, Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul]
  simp only [← Finset.sum_product']
  refine Finset.sum_nbij' (fun x => (x.2.2.2, x.2.2.1, x.2.1, x.1)) (fun y => (y.2.2.2, y.2.2.1, y.2.1, y.1))
    (by simp) (by simp) (by simp) (by simp) (fun x _ => ?_)
  congr 1
  ring

theorem hess_pull {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {p' : Y ⟶ Sp k} {D D' : ℕ}
    (π : Y ⟶ X) (w : π ≫ p = p') (σ : k →+* ℂ) (c : AlgChart p' σ D') (c0 : AlgChart p σ D) (y : CxPts p' σ)
    (hy : y ∈ c.e.source) (hy0 : PtsOver.map π w (spMap σ) y ∈ c0.e.source) (L : HermLB p)
    (i : (L.pull π w).B.ι) (hi : y ∈ ptsIn p' σ ((L.pull π w).B.U i)) :
    c.hess ((L.pull π w).φ σ) i y =
      Matrix.of (fun j b => fderiv ℂ (c0.e ∘ PtsOver.map π w (spMap σ) ∘ c.e.symm) (c.e y) (coordVec j) b) *
        c0.hess (L.φ σ) (i PUnit.unit) (PtsOver.map π w (spMap σ) y) *
        Matrix.of (fun a l => conj (fderiv ℂ (c0.e ∘ PtsOver.map π w (spMap σ) ∘ c.e.symm) (c.e y) (coordVec l) a)) := by
  set m := PtsOver.map π w (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  set F : V D' → V D := c0.e ∘ m ∘ c.e.symm with hFdef
  set U := c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c0.e.source)
  have hU : IsOpen U := GlobalTheory.ChartGlue.isOpen_over c.e (c0.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c.e y ∈ U := GlobalTheory.ChartGlue.mem_over c.e hy hy0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c c0
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D' _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c.e y) = c0.e (m y) := by
    simp only [hFdef, Function.comp_apply, c.e.left_inv hy]
  have him : m y ∈ ptsIn p σ (L.B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hi PUnit.unit
  set g : V D → ℂ := fun v => ((L.φ σ).φ (i PUnit.unit) (c0.e.symm v) : ℂ)
  have hg : ContDiffAt ℝ 2 g (F (c.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((L.cInf σ).contDiffAt c0 hy0 him)
  have e : (fun v => (((L.pull π w).φ σ).φ i (c.e.symm v) : ℂ)) =ᶠ[nhds (c.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ (L.φ σ) π w i (c.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c0.e.left_inv hv.2]
    exact congrArg _ this
  have hK : c0.hess (L.φ σ) (i PUnit.unit) (m y) = cHess D g (F (c.e y)) := by
    rw [hFy]; rfl
  show cHess D' _ (c.e y) = _
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e, hK]
  ext j l
  rw [GlobalTheory.HessPull.cHess_comp_apply D' D g F U hU _ hyU hF hg j l]
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
    simp only [ReciprocityTheory.L2DbarEstimates.bas, coordVec]; ring

theorem c1F_pull_eq_pullF_c1F : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (Y : Scheme.{0}) (p' : Y ⟶ Sp k) (D' : ℕ) (hY : IsRegVar p' D') (π : Y ⟶ X) (w : π ≫ p = p'),
    ∀ L : HermLB p, fld _ (c1F hY σ (L.pull π w)) = pullF hX hY σ π w (fld _ (c1F hX σ L)) := by
  intro k _ X _ p D hX σ Y p' D' hY π w L
  funext x
  obtain ⟨⟨c, y⟩, hy⟩ := x
  simp only [pullF, HolAtlas.pullback, fld]
  rw [c1F_eq_matForm_hessL hY _ hy]
  have key : ∀ (c0 : AlgChart p σ D) (h0 : PtsOver.map π w (spMap σ) y ∈ c0.e.source),
      (matForm D' (hessL (L.pull π w) c y) : Alt D') =
        pull (fderiv ℂ (c0.e ∘ PtsOver.map π w (spMap σ) ∘ c.e.symm) (c.e y))
          (c1F hX σ L ⟨(c0, PtsOver.map π w (spMap σ) y), h0⟩ : Alt D) := by
    intro c0 h0
    have hp := mem_pick ((L.pull π w).φ σ).isLB y
    rw [c1F_eq_matForm_hessL hX L h0, pull_matForm]
    simp only [hessL]
    rw [hess_pull π w σ c c0 y hy h0 L _ hp,
      c0.hess_eq (L.cInf σ) h0 (mem_pick (L.φ σ).isLB _)
        (mem_of_mem_linComb (m := fun _ => PtsOver.map π w (spMap σ) y) (fun _ => rfl) hp PUnit.unit)]
  exact key _ _

end GlobalTheory.ChernPull

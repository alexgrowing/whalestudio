import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix.ChartChange

section
variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

def colSum (H : Fin D → Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  ∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => H (τ l) j l).det

theorem colSum_mul_left (A : Matrix (Fin D) (Fin D) ℂ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => A * H a) = A.det * colSum H := by
  simp only [colSum, Finset.mul_sum, ← Matrix.det_mul]
  refine Finset.sum_congr rfl fun τ _ => congrArg _ ?_
  ext j l
  simp [Matrix.mul_apply]

theorem colSum_transpose (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => (H a).transpose) = colSum H := by
  simp only [colSum, Matrix.det_apply', Matrix.of_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun (τ ρ : Equiv.Perm (Fin D)) => ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ∏ i, H (τ i) (ρ i) i)]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun ρ => ?_
  refine Fintype.sum_equiv (Equiv.mulRight ρ⁻¹) _ _ fun τ => ?_
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv, Equiv.coe_mulRight]
  congr 1
  refine Fintype.prod_equiv ρ _ _ fun i => ?_
  simp

theorem colSum_mul (A B : Matrix (Fin D) (Fin D) ℂ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => A * H a * B) = A.det * B.det * colSum H := by
  have e : colSum (fun a => H a * B) = B.det * colSum H := by
    rw [← colSum_transpose, ← colSum_transpose H, ← Matrix.det_transpose B, ← colSum_mul_left]
    simp only [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [colSum_mul_left A fun a => H a * B, e, mul_assoc]

theorem dens_eq (L : Fin D → MLine p σ) (c : AlgChart p σ D) (y : CxPts p σ) :
    dens L c y = (Real.pi ^ D)⁻¹ * (colSum fun a => c.hess (L a).φ (pick (L a).φ.isLB y) y).re := rfl

theorem dens_trans (L : Fin D → MLine p σ) (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : dens L c y = ‖transDet c.e c'.e y‖ ^ 2 * dens L c' y := by
  have ho := isOpen_over c.e c'.e.open_source
  have hm := mem_over c.e hy hy'
  have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  let J : Matrix (Fin D) (Fin D) ℂ :=
    Matrix.of fun l j => (fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (ReciprocityTheory.L2DbarEstimates.bas D j)) l
  have h (a) : c.hess (L a).φ (pick (L a).φ.isLB y) y =
      J.transpose * c'.hess (L a).φ (pick (L a).φ.isLB y) y * J.map (starRingEnd ℂ) := by
    have e : (fun v => ((L a).φ.φ (pick (L a).φ.isLB y) (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)]
        (fun v => ((L a).φ.φ (pick (L a).φ.isLB y) (c'.e.symm v) : ℂ)) ∘ c'.e ∘ c.e.symm :=
      eventually_of_mem (ho.mem_nhds hm) fun v hv => by
        simp only [Function.comp_apply, c'.e.left_inv hv.2]
    rw [AlgChart.hess, AlgChart.hess, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e,
      ReciprocityTheory.L2DbarEstimates.Y.cmpa_cHess_comp ho hm (c.holo_trans c') (e₂ ▸
        Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((L a).cInf.contDiffAt c' hy' (mem_pick _ y))), e₂]
  have hJ : J.det = transDet c.e c'.e y := ReciprocityTheory.L2DbarEstimates.Y.cmpa_det_jac _
  have hd : J.transpose.det * (J.map (starRingEnd ℂ)).det = ((‖transDet c.e c'.e y‖ ^ 2 : ℝ) : ℂ) := by
    have hm' : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det := (RingHom.map_det (starRingEnd ℂ) J).symm
    rw [hm', Matrix.det_transpose, hJ, Complex.mul_conj']
    push_cast
    rfl
  rw [dens_eq, dens_eq]
  simp only [h]
  rw [colSum_mul, hd, Complex.re_ofReal_mul]
  ring

end

theorem dens_change_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → MLine p σ) (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → dens L c y = ‖transDet c.e c'.e y‖ ^ 2 * dens L c' y :=
  fun _ _ _ _ _ _ L c c' _ hy hy' => dens_trans L c c' hy hy'

end GlobalTheory.Mix.ChartChange

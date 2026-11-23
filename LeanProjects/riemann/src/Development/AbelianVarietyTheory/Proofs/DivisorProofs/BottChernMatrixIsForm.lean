import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixDens.BcMatForm

section Alg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  (K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : E)

theorem kappa_ne_zero : kappa ≠ 0 := by
  rw [kappa]
  exact div_ne_zero Complex.I_ne_zero
    (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero))

def secondFormL : E →ₗ[ℂ] Matrix l m ℂ where
  toFun := secondForm K z
  map_add' ξ ξ' := by ext; simp [secondForm_eq, conn_add_vec, toBlocks₂₁]
  map_smul' c ξ := by ext; simp [secondForm_eq, conn_smul_vec, toBlocks₂₁]

theorem trace_secondForm_sum {ι : Type} [Fintype ι] (x y : ι → ℂ) (u : ι → E) :
    (secondForm K z (∑ a, x a • u a) * secondFormAdj K z (∑ b, y b • u b)).trace =
      ∑ a, ∑ b, x a * star (y b) * (secondForm K z (u a) * secondFormAdj K z (u b)).trace := by
  have e (w : ι → ℂ) : secondForm K z (∑ a, w a • u a) = ∑ a, w a • secondForm K z (u a) := by
    change secondFormL K z _ = ∑ a, w a • secondFormL K z (u a)
    rw [map_sum]; simp only [map_smul]
  simp only [secondFormAdj, adj, e, conjTranspose_sum, conjTranspose_smul, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, trace_sum, trace_smul, smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem star_trace_secondForm (hK : (K z).IsHermitian) (ξ η : E) :
    star (secondForm K z ξ * secondFormAdj K z η).trace =
      (secondForm K z η * secondFormAdj K z ξ).trace := by
  have hS := (isHermitian_subGram hK).transpose.inv
  have hQ := (isHermitian_quotGram hK).transpose
  rw [← trace_conjTranspose]
  simp only [secondFormAdj, adj, conjTranspose_mul, conjTranspose_conjTranspose, hS.eq, hQ.eq,
    Matrix.mul_assoc]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]

variable {K z}

theorem extTrace_div (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (ξ η : E) :
    extTrace K z ξ η / kappa = (secondForm K z ξ * secondFormAdj K z η).trace := by
  rw [extTrace_eq h hp, mul_div_cancel_left₀ _ kappa_ne_zero]

theorem continuousAt_trace (hK : MContDiffAt ∞ K z) (hp : (K z).PosDef) (ξ η : E) :
    ContinuousAt (fun w => (secondForm K w ξ * secondFormAdj K w η).trace) z := by
  have hsu : IsUnit (subGram (K z)).det := (posDef_subGram hp).det_pos.ne'.isUnit
  have hu : IsUnit (K z).det := hp.det_pos.ne'.isUnit
  have h0 : MContDiffAt 0 K z := hK.of_le (by simp)
  have hs (ζ : E) : MContDiffAt 0 (fun w => secondForm K w ζ) z := fun a b => by
    simp only [secondForm_eq]; exact hK.conn hu (by simp) ζ (Sum.inr a) (Sum.inl b)
  have ha : MContDiffAt 0 (fun w => secondFormAdj K w η) z :=
    ((h0.subGram.transpose.inv (by rwa [det_transpose])).mul (hs η).conjTranspose).mul
      (h0.quotGram hsu).transpose
  have hM := (hs ξ).mul ha
  simp only [Matrix.trace, Matrix.diag]
  exact (ContDiffAt.sum fun i _ => hM i i).continuousAt

end Alg

section Main

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
  {S : ShortComplex X.Modules} {r s : ℕ} {h : Met p σ S.X₂ (r + s)} (hS : S.ShortExact)
  (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s)

theorem bcMat_apply (H : h.IsCInf) (a : VBExt.AdaptedChart S r s) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) (ha : y ∈ ptsIn p σ a.U) (j l : Fin D) :
    bcMat h hS h₁ h₃ c y j l =
      (secondForm (fun v => h.gram a.frame (c.e.symm v)) (c.e y) (EuclideanSpace.single j 1) *
        secondFormAdj (fun v => h.gram a.frame (c.e.symm v)) (c.e y) (EuclideanSpace.single l 1)).trace := by
  rw [bcMat, formMat, of_apply,
    Met.bcForm_eq hS a _ c H hy ha (Met.exists_adapted hS h₁ h₃ y).choose_spec, Met.bcForm,
    extTrace_div (((H.gram a.frame ha).mContDiffAt c hy).of_le (by norm_cast))
      (h.eventually_posDef hS a c hy ha)]

theorem bcMat_trans (H : h.IsCInf) (c c' : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) :
    bcMat h hS h₁ h₃ c y = chg (transMat c c' y) (bcMat h hS h₁ h₃ c' y) := by
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ y
  have ho := ChartGlue.isOpen_over c.e c'.e.open_source
  have hm := ho.mem_nhds (ChartGlue.mem_over c.e hy hy')
  have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  have hd := ((H.gram a.frame ha).mContDiffAt c' hy').of_le (j := 1) (by norm_cast)
  have hp := h.eventually_posDef hS _ c' hy' ha
  have hl (j : Fin D) : fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (EuclideanSpace.single j 1) =
      ∑ b, transMat c c' y b j • (EuclideanSpace.single b 1 : V D) := by
    ext i
    simp [transMat, Finset.sum_apply, Pi.single_apply]
  ext j l
  have e₁ : bcMat h hS h₁ h₃ c y j l = ∑ b, ∑ b', transMat c c' y b j * star (transMat c c' y b' l) *
      bcMat h hS h₁ h₃ c' y b b' := by
    simp only [bcMat_apply hS h₁ h₃ H a c' hy' ha]
    rw [← trace_secondForm_sum, ← hl, ← hl, ← extTrace_div hd hp, bcMat, formMat, of_apply,
      Met.bcForm_eq hS a _ c H hy ha (Met.exists_adapted hS h₁ h₃ y).choose_spec, Met.bcForm,
      extTrace_congr (K' := fun v => h.gram a.frame (c'.e.symm ((c'.e ∘ c.e.symm) v)))
        (eventually_of_mem hm fun v hv => by simp only [Function.comp_apply, c'.e.left_inv hv.2]),
      extTrace_comp_holo (K := fun v => h.gram a.frame (c'.e.symm v)) (e₂ ▸ hd) (e₂ ▸ hp)
        (contDiffAt_euclidean.2 fun i => ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ ho
          (differentiableOn_euclidean.1 (c.holo_trans c') i)).contDiffAt hm).of_le (by norm_cast)), e₂]
  rw [e₁, Finset.sum_comm]
  simp only [chg, mul_apply, transpose_apply, conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  ring

theorem continuousOn_bcMat (H : h.IsCInf) (c : AlgChart p σ D) :
    ContinuousOn (fun v => bcMat h hS h₁ h₃ c (c.e.symm v)) c.e.target := by
  intro v hv
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ (c.e.symm v)
  have hWo := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) a.U)
  have hK : MContDiffAt ∞ (fun v => h.gram a.frame (c.e.symm v)) v := by
    have := (H.gram a.frame ha).mContDiffAt c (c.e.map_target hv)
    rwa [c.e.right_inv hv] at this
  have hm := hWo.mem_nhds (show v ∈ _ from ⟨hv, ha⟩)
  refine ContinuousAt.continuousWithinAt
    (continuousAt_pi.2 fun j => continuousAt_pi.2 fun l => ?_)
  refine (continuousAt_trace hK (h.posDef_gram_frame hS a ha) (EuclideanSpace.single j 1)
    (EuclideanSpace.single l 1)).congr ?_
  filter_upwards [hm] with w hw
  rw [bcMat_apply hS h₁ h₃ H a c (c.e.map_target hw.1) hw.2, c.e.right_inv hw.1]

theorem isHermitian_bcMat (H : h.IsCInf) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) : (bcMat h hS h₁ h₃ c y).IsHermitian := by
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ y
  ext j l
  rw [conjTranspose_apply, bcMat_apply hS h₁ h₃ H a c hy ha, bcMat_apply hS h₁ h₃ H a c hy ha]
  exact star_trace_secondForm (fun v => h.gram a.frame (c.e.symm v)) (c.e y)
    (h.eventually_posDef hS a c hy ha).self_of_nhds.isHermitian _ _

end Main

theorem isForm_bcMat : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ)
    (S : ShortComplex X.Modules) (r s : ℕ) (h : Met p σ S.X₂ (r + s)) (hS : S.ShortExact)
    (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s), h.IsCInf →
    IsForm fun (c : AlgChart p σ D) y => bcMat h hS h₁ h₃ c y :=
  fun _ _ _ _ _ _ _ _ _ _ hS h₁ h₃ H =>
    ⟨fun c c' _ hy hy' => bcMat_trans hS h₁ h₃ H c c' hy hy', continuousOn_bcMat hS h₁ h₃ H,
      fun c _ hy => isHermitian_bcMat hS h₁ h₃ H c hy⟩

end GlobalTheory.MixDens.BcMatForm

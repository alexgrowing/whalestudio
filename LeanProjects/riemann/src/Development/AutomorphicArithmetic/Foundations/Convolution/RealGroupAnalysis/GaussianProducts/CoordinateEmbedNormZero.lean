import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors
open scoped GroundTheory.Global.AdeleBaseChange

namespace UpperTheory.ConvolutionTheory.R2.G.similitudePositivity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)

local notation "ι" => AdeleBaseChange.adeleMap F E
local notation "BB" => AdeleBaseChange.adeleBasis (K := F) (L := E) (Dat.b D)

private theorem basis0 : BB 0 = 1 := by
  rw [AdeleBaseChange.adeleBasis_apply, D.b0, map_one]

private theorem basis1 : BB 1 = rt D.θ := by
  rw [AdeleBaseChange.adeleBasis_apply, D.b1]

private theorem mkE_eq (u t : A F) : D.mkE u t = u • BB 0 + t • BB 1 := by
  rw [basis0, basis1, Algebra.smul_def, Algebra.smul_def, AdeleBaseChange.algebraMap_adeleRing, mul_one]
  rfl

private theorem co_mkE (u t : A F) : D.co (D.mkE u t) = ![u, t] := by
  have h : D.mkE u t = ∑ j, (![u, t] : Fin 2 → A F) j • BB j := by
    simp [Fin.sum_univ_two, mkE_eq]
  funext i
  rw [h]
  change (BB).repr _ i = _
  rw [Module.Basis.repr_sum_self]

private theorem coordinate_embedNorm_zero (u t : A F) : D.co (D.mkE u t) 0 = u := by simp [co_mkE]
private theorem coordinate_embedNorm_one (u t : A F) : D.co (D.mkE u t) 1 = t := by simp [co_mkE]

private theorem mkE_co (z : A E) : D.mkE (D.co z 0) (D.co z 1) = z := by
  rw [mkE_eq]
  have := (BB).sum_repr z
  rw [Fin.sum_univ_two] at this
  exact this

private theorem θ_mul : rt D.θ * rt D.θ = ι (rt D.δ) := by
  rw [← map_mul, ← sq, D.sq, AdeleBaseChange.adeleMap_algebraMap]

private theorem norm_mkE (u t : A F) :
    Algebra.norm (A F) (D.mkE u t) = u ^ 2 - rt D.δ * t ^ 2 := by
  have hm : D.mkE u t * rt D.θ = D.mkE (rt D.δ * t) u := by
    have h := θ_mul D
    simp only [Dat.mkE, map_mul]
    linear_combination (ι t) * h
  rw [Algebra.norm_eq_matrix_det (BB), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, basis0, basis1, mul_one, hm]
  change D.co _ 0 * D.co _ 1 - D.co _ 0 * D.co _ 1 = _
  simp only [coordinate_embedNorm_zero, coordinate_embedNorm_one]
  ring

variable [IsTotallyReal F]

private theorem pInf_δ (v : InfinitePlace F) : TR.pInf F (rt D.δ) v < 0 := by
  have h := D.neg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))
  have e : TR.pInf F (rt D.δ) v = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) D.δ :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal v) (WithAbs.toAbs _ D.δ)
  rw [e]
  exact h

include D in
private theorem nu_pos (h : GL (Fin 2) (A E)) (v : InfinitePlace F) :
    0 < TR.pInf F (nu F h : A F) v := by
  have hn : ((nu F h : (A F)ˣ) : A F) = Algebra.norm (A F) h.val.det := rfl
  have hv : TR.pInf F (nu F h : A F) v =
      (TR.pInf F (D.co h.val.det 0) v) ^ 2 - TR.pInf F (rt D.δ) v * (TR.pInf F (D.co h.val.det 1) v) ^ 2 := by
    rw [hn, ← mkE_co D h.val.det, norm_mkE, coordinate_embedNorm_zero, coordinate_embedNorm_one]
    simp [map_sub, map_mul, map_pow]
  have hne : TR.pInf F (nu F h : A F) v ≠ 0 := by
    intro h0
    have h1 : TR.pInf F (nu F h : A F) * TR.pInf F (((nu F h)⁻¹ : (A F)ˣ) : A F) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 := congrFun h1 v
    simp [h0] at h2
  have hd := pInf_δ D v
  have hge : 0 ≤ TR.pInf F (nu F h : A F) v := by
    rw [hv]
    nlinarith [sq_nonneg (TR.pInf F (D.co h.val.det 0) v), sq_nonneg (TR.pInf F (D.co h.val.det 1) v)]
  exact lt_of_le_of_ne hge (Ne.symm hne)

private theorem pInf_id (u : (TR.Rinf F)ˣ) : TR.pInf F (TR.infId F u).val = u.val := by
  change TR.pInf F (1 - TR.sInf F 1 + TR.sInf F _) = _
  have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
  simp [h]

end UpperTheory.ConvolutionTheory.R2.G.similitudePositivity

open UpperTheory.ConvolutionTheory.R2.G.similitudePositivity in
theorem UpperTheory.ConvolutionTheory.R2.G.nuPos :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (h : GL (Fin 2) (A E)), ∃ s : (A F)ˣ, ((nu F h * (s ^ 4)⁻¹ : (A F)ˣ) : A F).1 = 1 := by
  intro F E _ _ _ _ _ _ _ D h
  have hpos := nu_pos D h
  let r : TR.Rinf F := TR.pInf F (nu F h : A F)
  have hroot : ∀ w, 0 < Real.sqrt (Real.sqrt (r w)) := fun w => Real.sqrt_pos.2 (Real.sqrt_pos.2 (hpos w))
  let d : (TR.Rinf F)ˣ :=
    ⟨fun w => Real.sqrt (Real.sqrt (r w)), fun w => (Real.sqrt (Real.sqrt (r w)))⁻¹,
      funext fun w => mul_inv_cancel₀ (hroot w).ne', funext fun w => inv_mul_cancel₀ (hroot w).ne'⟩
  refine ⟨TR.infId F d, ?_⟩
  have e : TR.pInf F (nu F h : A F) = TR.pInf F (((TR.infId F d) ^ 4 : (A F)ˣ) : A F) := by
    rw [Units.val_pow_eq_pow_val, map_pow, pInf_id]
    funext w
    have h1 : Real.sqrt (Real.sqrt (r w)) ^ 2 = Real.sqrt (r w) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (r w) ^ 2 = r w := Real.sq_sqrt (hpos w).le
    change r w = Real.sqrt (Real.sqrt (r w)) ^ 4
    calc r w = (Real.sqrt (Real.sqrt (r w)) ^ 2) ^ 2 := by rw [h1, h2]
      _ = _ := by ring
  have hp : TR.pInf F ((nu F h * ((TR.infId F d) ^ 4)⁻¹ : (A F)ˣ) : A F) = 1 := by
    rw [Units.val_mul, map_mul, e, ← map_mul, Units.mul_inv, map_one]
  exact (TR.infEq F).symm.injective (by rw [map_one]; exact hp)

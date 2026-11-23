import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

namespace UpperTheory.ConvolutionTheory.R2.C.NearIdentityUnipotents

variable {F : Type} [Field F] [NumberField F]

private noncomputable def fstR : A F →+* InfiniteAdeleRing F :=
  RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

private theorem cont_fst : Continuous (fun x : A F => x.1) :=
  continuous_fst (X := InfiniteAdeleRing F) (Y := FiniteAdeleRing (𝓞 F) F)

private theorem cont_pair (y : FiniteAdeleRing (𝓞 F) F) :
    Continuous (fun x : InfiniteAdeleRing F => ((x, y) : A F)) :=
  Continuous.prodMk_left (X := InfiniteAdeleRing F) (Y := FiniteAdeleRing (𝓞 F) F) y

private theorem cont_entry (i j : Fin 2) : Continuous (fun h : G1 F => h i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

private theorem d_one : ((1 : G1 F) 1 1).1 = 1 := by
  simp
  rfl

private theorem cont_d (v : InfinitePlace F) : Continuous (fun h : G1 F => (h 1 1).1 v) :=
  (continuous_apply (A := fun v : InfinitePlace F => v.Completion) v).comp (cont_fst.comp (cont_entry 1 1))

private theorem ne_one (v : InfinitePlace F) : ((1 : G1 F) 1 1).1 v ≠ 0 := by
  rw [d_one]
  exact one_ne_zero

private theorem ev_ne : ∀ᶠ h in 𝓝 (1 : G1 F), ∀ v, (h 1 1).1 v ≠ 0 := by
  rw [Filter.eventually_all]
  intro v
  exact (cont_d v).continuousAt.eventually_ne (ne_one v)

private noncomputable def eI (h : G1 F) : InfiniteAdeleRing F := fun v => ((h 1 1).1 v)⁻¹

private theorem eI_mul {h : G1 F} (hu : ∀ v, (h 1 1).1 v ≠ 0) : eI h * (h 1 1).1 = 1 := by
  funext v
  exact inv_mul_cancel₀ (hu v)

private theorem eI_cont : ContinuousAt (eI : G1 F → InfiniteAdeleRing F) 1 :=
  continuousAt_pi.2 fun v => (cont_d v).continuousAt.inv₀ (ne_one v)

private theorem eI_one : eI (1 : G1 F) = 1 := by
  funext v
  show (((1 : G1 F) 1 1).1 v)⁻¹ = 1
  rw [d_one]
  exact inv_one

private noncomputable def aU (h : G1 F) : (A F)ˣ :=
  if hu : ∀ v, (h 1 1).1 v ≠ 0 then
    ⟨(eI h, 1), ((h 1 1).1, 1), Prod.ext (eI_mul hu) (mul_one _),
      Prod.ext ((mul_comm _ _).trans (eI_mul hu)) (mul_one _)⟩
  else 1

private noncomputable def bU (h : G1 F) : A F := ((h 0 1).1 * eI h, 0)
private noncomputable def cU (h : G1 F) : A F := (-(h 1 0).1 * eI h, 0)

private noncomputable def pU (b : A F) (a : (A F)ˣ) (c : A F) : G1 F :=
  nU b * mD a * wW F * nU c * (wW F)⁻¹

private theorem pU_coe (b : A F) (a : (A F)ˣ) (c : A F) :
    (pU b a c).1 = !![(a : A F) - b * c * ((a⁻¹ : (A F)ˣ) : A F), b * ((a⁻¹ : (A F)ˣ) : A F);
      -c * ((a⁻¹ : (A F)ˣ) : A F), ((a⁻¹ : (A F)ˣ) : A F)] := by
  have hw : ((wW F)⁻¹).1 = !![0, -1; 1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [wW]
  simp only [pU, Matrix.SpecialLinearGroup.coe_mul, hw]
  simp only [nU, mD, wW, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

private theorem fstR_a {h : G1 F} (hu : ∀ v, (h 1 1).1 v ≠ 0) : fstR (aU h : A F) = eI h := by
  simp only [aU, dif_pos hu]
  rfl

private theorem fstR_ai {h : G1 F} (hu : ∀ v, (h 1 1).1 v ≠ 0) :
    fstR (((aU h)⁻¹ : (A F)ˣ) : A F) = (h 1 1).1 := by
  simp only [aU, dif_pos hu]
  rfl

private theorem fstR_b (h : G1 F) : fstR (bU h) = (h 0 1).1 * eI h := rfl
private theorem fstR_c (h : G1 F) : fstR (cU h) = -(h 1 0).1 * eI h := rfl

private theorem pU_fst {h : G1 F} (hu : ∀ v, (h 1 1).1 v ≠ 0) (i j : Fin 2) :
    ((pU (bU h) (aU h) (cU h)).1 i j).1 = (h i j).1 := by
  have hdet : (h 0 0).1 * (h 1 1).1 - (h 0 1).1 * (h 1 0).1 = 1 := by
    have h1 : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
      have := h.det_coe
      rwa [Matrix.det_fin_two] at this
    have := congrArg fstR h1
    rw [map_sub, map_mul, map_mul, map_one] at this
    exact this
  have he := eI_mul hu
  have e00 : fstR ((aU h : A F) - bU h * cU h * (((aU h)⁻¹ : (A F)ˣ) : A F)) = (h 0 0).1 := by
    rw [map_sub, map_mul, map_mul, fstR_a hu, fstR_ai hu, fstR_b, fstR_c]
    linear_combination ((h 0 1).1 * (h 1 0).1 * eI h + (h 0 0).1) * he - eI h * hdet
  have e01 : fstR (bU h * (((aU h)⁻¹ : (A F)ˣ) : A F)) = (h 0 1).1 := by
    rw [map_mul, fstR_ai hu, fstR_b]
    linear_combination (h 0 1).1 * he
  have e10 : fstR (-cU h * (((aU h)⁻¹ : (A F)ˣ) : A F)) = (h 1 0).1 := by
    rw [map_mul, map_neg, fstR_ai hu, fstR_c]
    linear_combination (h 1 0).1 * he
  have e11 : fstR (((aU h)⁻¹ : (A F)ˣ) : A F) = (h 1 1).1 := fstR_ai hu
  rw [pU_coe]
  fin_cases i <;> fin_cases j
  exacts [e00, e01, e10, e11]

private noncomputable def kU (h : G1 F) : G1 F := (pU (bU h) (aU h) (cU h))⁻¹ * h

private theorem infOne_kU {h : G1 F} (hu : ∀ v, (h 1 1).1 v ≠ 0) : InfOne (kU h) := by
  have hP : Matrix.SpecialLinearGroup.map fstR (pU (bU h) (aU h) (cU h)) =
      Matrix.SpecialLinearGroup.map fstR h := by
    ext i j
    exact pU_fst hu i j
  have hk : Matrix.SpecialLinearGroup.map fstR (kU h) = 1 := by
    rw [kU, map_mul, map_inv, hP, inv_mul_cancel]
  intro i j
  have h1 : fstR ((kU h).1 i j) = (Matrix.SpecialLinearGroup.map fstR (kU h)).1 i j := rfl
  have h2 : fstR ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j) =
      (fstR.mapMatrix (1 : Matrix (Fin 2) (Fin 2) (A F))) i j := rfl
  have h3 := h1.trans (by rw [hk]; rfl : _ = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j)
  rw [map_one] at h2
  exact h3.trans h2.symm

private theorem cont_nU : Continuous (nU : A F → G1 F) := by
  refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem cont_mD : Continuous (mD : (A F)ˣ → G1 F) := by
  refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
  fin_cases i <;> fin_cases j <;> simp
  · exact Units.continuous_val
  · exact continuous_const
  · exact continuous_const
  · exact Units.continuous_val.comp continuous_inv

private theorem bU_cont : ContinuousAt (bU : G1 F → A F) 1 :=
  (cont_pair 0).continuousAt.comp
    (((cont_fst.comp (cont_entry 0 1)).continuousAt).mul eI_cont)

private theorem cU_cont : ContinuousAt (cU : G1 F → A F) 1 :=
  (cont_pair 0).continuousAt.comp
    ((((continuous_neg.comp (cont_fst.comp (cont_entry 1 0))).continuousAt)).mul eI_cont)

private theorem aU_cont : ContinuousAt (aU : G1 F → (A F)ˣ) 1 := by
  rw [Units.isEmbedding_embedProduct.isInducing.continuousAt_iff]
  have hf : ContinuousAt (fun h : G1 F => ((((eI h, 1) : A F), MulOpposite.op (((h 1 1).1, 1) : A F)) :
      A F × (A F)ᵐᵒᵖ)) 1 := by
    refine ContinuousAt.prodMk ((cont_pair 1).continuousAt.comp eI_cont) ?_
    exact (MulOpposite.continuous_op.comp ((cont_pair 1).comp (cont_fst.comp (cont_entry 1 1)))).continuousAt
  refine hf.congr ?_
  filter_upwards [ev_ne] with h hu
  simp only [Function.comp, aU, dif_pos hu]
  rfl

private theorem bU_one : bU (1 : G1 F) = 0 := by
  have : (1 : G1 F) 0 1 = 0 := by simp
  simp only [bU, this]
  exact Prod.ext (zero_mul _) rfl

private theorem cU_one : cU (1 : G1 F) = 0 := by
  have : (1 : G1 F) 1 0 = 0 := by simp
  simp only [cU, this]
  exact Prod.ext (by show -(0 : InfiniteAdeleRing F) * _ = 0; simp) rfl

private theorem aU_one : aU (1 : G1 F) = 1 := by
  refine Units.ext ?_
  simp only [aU, dif_pos (ne_one (F := F))]
  exact Prod.ext eI_one rfl

private theorem pU_one : pU (bU (1 : G1 F)) (aU 1) (cU 1) = 1 := by
  rw [bU_one, cU_one, aU_one]
  ext i j
  rw [pU_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem kU_tendsto : Tendsto (kU : G1 F → G1 F) (𝓝 1) (𝓝 1) := by
  have hb : ContinuousAt (fun h : G1 F => nU (bU h)) 1 := cont_nU.continuousAt.comp bU_cont
  have hc : ContinuousAt (fun h : G1 F => nU (cU h)) 1 := cont_nU.continuousAt.comp cU_cont
  have ha : ContinuousAt (fun h : G1 F => mD (aU h)) 1 := cont_mD.continuousAt.comp aU_cont
  have hp : ContinuousAt (fun h : G1 F => pU (bU h) (aU h) (cU h)) 1 :=
    (((hb.mul ha).mul continuousAt_const).mul hc).mul continuousAt_const
  have hk : ContinuousAt (kU : G1 F → G1 F) 1 := hp.inv.mul continuousAt_id
  have h1 : kU (1 : G1 F) = 1 := by simp [kU, pU_one]
  have := hk.tendsto
  rwa [h1] at this

end UpperTheory.ConvolutionTheory.R2.C.NearIdentityUnipotents

open UpperTheory.ConvolutionTheory.R2.C.NearIdentityUnipotents in
theorem UpperTheory.ConvolutionTheory.R2.C.near :
    ∀ (F : Type) [Field F] [NumberField F], ∃ (b c : G1 F → A F) (a : G1 F → (A F)ˣ) (k : G1 F → G1 F), ContinuousAt b 1 ∧ ContinuousAt c 1 ∧ ContinuousAt a 1 ∧
    Tendsto k (𝓝 1) (𝓝 1) ∧ ∀ᶠ h in 𝓝 (1 : G1 F), InfOne (k h) ∧ h = nU (b h) * mD (a h) * wW F * nU (c h) * (wW F)⁻¹ * k h := by
  intro F _ _
  refine ⟨bU, cU, aU, kU, bU_cont, cU_cont, aU_cont, kU_tendsto, ?_⟩
  filter_upwards [ev_ne] with h hu
  refine ⟨infOne_kU hu, ?_⟩
  show h = pU (bU h) (aU h) (cU h) * kU h
  rw [kU, mul_inv_cancel_left]

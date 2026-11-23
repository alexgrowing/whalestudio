import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)

variable (E) in

abbrev am : A F →+* A E := AdeleBaseChange.adeleMap F E

theorem am_rt (c : F) : am E (rt c) = rt (algebraMap F E c) := AdeleBaseChange.adeleMap_algebraMap c
theorem am_injective : Function.Injective (am (F := F) E) := AdeleBaseChange.adeleMap_injective
theorem continuous_am : Continuous (am (F := F) E) := AdeleBaseChange.continuous_adeleMap

namespace Dat

include D in
theorem finrank_eq : Module.finrank F E = 2 := by simpa using Module.finrank_eq_card_basis D.b
theorem θ_ne_zero : D.θ ≠ 0 := D.b1 ▸ D.b.ne_zero 1
theorem δ_ne_zero : D.δ ≠ 0 := fun h => D.θ_ne_zero (pow_eq_zero_iff (two_ne_zero) |>.1 (by rw [D.sq, h, map_zero]))
theorem rt_θ_sq : (rt D.θ : A E) ^ 2 = am E (rt D.δ) := by rw [am_rt, ← D.sq]; exact (map_pow _ _ _).symm
theorem mkE_def (u t : A F) : D.mkE u t = am E u + am E t * rt D.θ := rfl
@[simp] theorem mkE_base (u : A F) : D.mkE u 0 = am E u := by simp [mkE_def]
theorem mkE_zero : D.mkE 0 0 = 0 := by simp
theorem mkE_one : D.mkE 1 0 = 1 := by simp
theorem mkE_add (u t u' t' : A F) : D.mkE (u + u') (t + t') = D.mkE u t + D.mkE u' t' := by simp only [mkE_def, map_add]; ring
theorem am_mul_mkE (a u t : A F) : am E a * D.mkE u t = D.mkE (a * u) (a * t) := by simp only [mkE_def, map_mul]; ring
theorem mkE_mul (u t u' t' : A F) : D.mkE u t * D.mkE u' t' = D.mkE (u * u' + rt D.δ * (t * t')) (u * t' + t * u') := by
  simp only [mkE_def, map_add, map_mul, ← D.rt_θ_sq]; ring
@[simp] theorem mkE_co (z : A E) : D.mkE (D.co z 0) (D.co z 1) = z := by
  letI : Algebra (A F) (A E) := AdeleBaseChange.algebraAdeleRing
  have h := (AdeleBaseChange.adeleBasis D.b).sum_repr z
  rw [Fin.sum_univ_two, AdeleBaseChange.adeleBasis_apply, AdeleBaseChange.adeleBasis_apply, D.b0, D.b1, map_one,
    Algebra.smul_def, Algebra.smul_def, mul_one] at h
  exact h
@[simp] theorem co_mkE (u t : A F) : D.co (D.mkE u t) = ![u, t] := by
  letI : Algebra (A F) (A E) := AdeleBaseChange.algebraAdeleRing
  have h : D.mkE u t = u • AdeleBaseChange.adeleBasis D.b 0 + t • AdeleBaseChange.adeleBasis D.b 1 := by
    rw [AdeleBaseChange.adeleBasis_apply, AdeleBaseChange.adeleBasis_apply, D.b0, D.b1, map_one,
      Algebra.smul_def, Algebra.smul_def, mul_one]
    rfl
  rw [h]
  ext i
  fin_cases i <;> simp [co]
theorem exists_mkE (z : A E) : ∃ u t, z = D.mkE u t := ⟨_, _, (D.mkE_co z).symm⟩
theorem mkE_inj {u t u' t' : A F} (h : D.mkE u t = D.mkE u' t') : u = u' ∧ t = t' := by
  have := congrArg D.co h
  rw [co_mkE, co_mkE] at this
  exact ⟨congrFun this 0, congrFun this 1⟩
@[simp] theorem co_am (u : A F) : D.co (am E u) = ![u, 0] := by rw [← D.mkE_base, co_mkE]
@[simp] theorem co_zero : D.co 0 = 0 := by rw [← D.mkE_zero, co_mkE]; ext i; fin_cases i <;> rfl
@[simp] theorem co_one : D.co 1 = ![1, 0] := by rw [← D.mkE_one, co_mkE]
theorem co_add (z z' : A E) : D.co (z + z') = D.co z + D.co z' := by
  obtain ⟨u, t, rfl⟩ := D.exists_mkE z
  obtain ⟨u', t', rfl⟩ := D.exists_mkE z'
  rw [← mkE_add]; simp
theorem co_am_mul (a : A F) (z : A E) : D.co (am E a * z) = a • D.co z := by
  obtain ⟨u, t, rfl⟩ := D.exists_mkE z
  rw [am_mul_mkE]; simp
theorem co_mul (z z' : A E) : D.co (z * z') =
    ![D.co z 0 * D.co z' 0 + rt D.δ * (D.co z 1 * D.co z' 1), D.co z 0 * D.co z' 1 + D.co z 1 * D.co z' 0] := by
  rw [← D.co_mkE, ← mkE_mul, mkE_co, mkE_co]
theorem mkE_rt (u t : F) : D.mkE (rt u) (rt t) = rt (algebraMap F E u + algebraMap F E t * D.θ) := by
  rw [mkE_def, am_rt, am_rt]; simp only [rt, map_add, map_mul]
theorem co_rt (z : E) (i : Fin 2) : D.co (rt z) i = rt (D.b.repr z i) := AdeleBaseChange.adeleBasis_repr_algebraMap D.b z i
theorem continuous_mkE' {X : Type*} [TopologicalSpace X] {u t : X → A F} (hu : Continuous u) (ht : Continuous t) :
    Continuous fun x => D.mkE (u x) (t x) :=
  (continuous_am.comp hu).add ((continuous_am.comp ht).mul continuous_const)
theorem continuous_co : Continuous D.co := continuous_pi fun i => by
  have : (fun z => D.co z i) = AdeleBaseChange.coord D.b i := funext fun z => AdeleBaseChange.adeleBasis_repr D.b z i
  rw [this]; exact AdeleBaseChange.continuous_coord D.b i

def coE : A E ≃ₜ+ (Fin 2 → A F) where
  toFun := D.co
  invFun u := D.mkE (u 0) (u 1)
  left_inv := D.mkE_co
  right_inv u := by rw [co_mkE]; ext i; fin_cases i <;> rfl
  map_add' := D.co_add
  continuous_toFun := D.continuous_co
  continuous_invFun := D.continuous_mkE' (continuous_apply 0) (continuous_apply 1)

@[simp] theorem bar_am (a : A F) : D.bar (am E a) = am E a := AdeleBaseChange.smul_adeleMap D.σ a
theorem bar_rt (z : E) : D.bar (rt z) = rt (D.σ z) := AdeleBaseChange.smul_algebraMap D.σ z
theorem bar_mkE (u t : A F) : D.bar (D.mkE u t) = D.mkE u (-t) := by
  simp only [mkE_def, map_add, map_mul, bar_am, bar_rt, D.conj, map_neg]; ring
@[simp] theorem bar_bar (z : A E) : D.bar (D.bar z) = z := by
  obtain ⟨u, t, rfl⟩ := D.exists_mkE z
  rw [bar_mkE, bar_mkE, neg_neg]
theorem continuous_bar : Continuous D.bar := continuous_const_smul D.σ
theorem mkE_mul_bar (u t : A F) : D.mkE u t * D.bar (D.mkE u t) = am E (u ^ 2 - rt D.δ * t ^ 2) := by
  rw [bar_mkE, mkE_mul, ← D.mkE_base]; congr 1 <;> ring
theorem mul_bar (z : A E) : z * D.bar z = am E (D.co z 0 ^ 2 - rt D.δ * D.co z 1 ^ 2) := by
  rw [← mkE_mul_bar, mkE_co]
theorem eq_am_of_bar_eq {z : A E} (h : D.bar z = z) : z = am E (D.co z 0) := by
  obtain ⟨u, t, rfl⟩ := D.exists_mkE z
  rw [bar_mkE] at h
  have h2 : (rt 2 : A F) * t = 0 := by rw [rt, map_ofNat]; linear_combination -(D.mkE_inj h).2
  have ht : t = 0 := ((IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (A F))).mul_right_eq_zero.1 h2
  rw [ht]; simp

theorem coe_ideleNorm (z : (A E)ˣ) :
    ((ideleNorm F E z : (A F)ˣ) : A F) = D.co z 0 ^ 2 - rt D.δ * D.co z 1 ^ 2 := by
  letI : Algebra (A F) (A E) := AdeleBaseChange.algebraAdeleRing
  rw [GroundTheory.Global.coe_ideleNorm, Algebra.norm_eq_matrix_det (AdeleBaseChange.adeleBasis D.b), Matrix.det_fin_two]
  have h0 : (rt (D.b 0) : A E) = D.mkE 1 0 := by rw [D.b0, mkE_one]; exact map_one _
  have h1 : (rt (D.b 1) : A E) = D.mkE 0 1 := by rw [D.b1]; simp [mkE_def]
  have e : ∀ i j, Algebra.leftMulMatrix (AdeleBaseChange.adeleBasis D.b) (z : A E) i j = D.co (z * rt (D.b j)) i := fun i j => by
    rw [Algebra.leftMulMatrix_eq_repr_mul, AdeleBaseChange.adeleBasis_apply]; rfl
  simp only [e, h0, h1, co_mul, co_mkE]
  simp
  ring
theorem am_ideleNorm (z : (A E)ˣ) : am E ((ideleNorm F E z : (A F)ˣ) : A F) = z * D.bar z := by rw [D.coe_ideleNorm, mul_bar]

def barU (z : (A E)ˣ) : (A E)ˣ := Units.map D.bar.toMonoidHom z
@[simp] theorem coe_barU (z : (A E)ˣ) : ((D.barU z : (A E)ˣ) : A E) = D.bar z := rfl
theorem ideleNorm_barU (z : (A E)ˣ) : ideleNorm F E (D.barU z) = ideleNorm F E z :=
  Units.ext (am_injective (E := E) (by rw [D.am_ideleNorm, D.am_ideleNorm, coe_barU, bar_bar, mul_comm]))
include D in
theorem ideleNorm_emb (a : (A F)ˣ) : ideleNorm F E (ideleEmbedding F E a) = a ^ 2 := by
  rw [ideleNorm_ideleEmbedding, D.finrank_eq]
theorem norm_eq (z : E) : Algebra.norm F z = D.b.repr z 0 ^ 2 - D.δ * D.b.repr z 1 ^ 2 := by
  haveI := AdeleBaseChange.nontrivial_adeleRing F
  by_cases hz : z = 0
  · haveI : Module.Finite F E := Module.Finite.of_basis D.b
    simp [hz]
  apply (algebraMap F (A F)).injective
  have h := D.coe_ideleNorm (IdeleGroup.diagonal E (Units.mk0 z hz))
  rw [ideleNorm_diagonal, coe_diagonal, coe_diagonal, co_rt, co_rt] at h
  simpa using h

end Dat

end UpperTheory.ConvolutionTheory.R2

end

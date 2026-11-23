import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open scoped GroundTheory.Global.AdeleBaseChange

namespace UpperTheory.ConvolutionTheory.R2.D.actionMatrixCoordinates

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

private theorem bar_apply (x : A E) : D.bar x = D.σ • x := rfl

private theorem bar_map (a : A F) : D.bar (ι a) = ι a := by
  rw [bar_apply, AdeleBaseChange.smul_adeleMap]

private theorem bar_θ : D.bar (rt D.θ) = -rt D.θ := by
  rw [bar_apply, AdeleBaseChange.smul_algebraMap, D.conj, map_neg]

private theorem θ_mul : rt D.θ * rt D.θ = ι (rt D.δ) := by
  rw [← map_mul, ← sq, D.sq, AdeleBaseChange.adeleMap_algebraMap]

private theorem bar_mkE (u t : A F) : D.bar (D.mkE u t) = D.mkE u (-t) := by
  simp [Dat.mkE, map_add, map_mul, bar_map, bar_θ, map_neg]

private theorem mkE_mul_bar (u t : A F) : D.mkE u t * D.mkE u (-t) = ι (u ^ 2 - rt D.δ * t ^ 2) := by
  have h := θ_mul D
  simp only [Dat.mkE, map_neg, map_sub, map_mul, map_pow]
  linear_combination (-(ι t) ^ 2) * h

private theorem mkE_add (u t u' t' : A F) : D.mkE (u + u') (t + t') = D.mkE u t + D.mkE u' t' := by
  simp only [Dat.mkE, map_add]; ring

private theorem mkE_mul (a u t : A F) : D.mkE (a * u) (a * t) = ι a * D.mkE u t := by
  simp only [Dat.mkE, map_mul]; ring

private theorem co_add (x y : A E) (i : Fin 2) : D.co (x + y) i = D.co x i + D.co y i := by
  simp [Dat.co, map_add]

private theorem co_mul (a : A F) (z : A E) (i : Fin 2) : D.co (ι a * z) i = a * D.co z i := by
  have : ι a * z = a • z := by
    rw [Algebra.smul_def, AdeleBaseChange.algebraMap_adeleRing]
  rw [this]
  simp [Dat.co, map_smul]

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

private theorem adeleMap_norm_eq (z : A E) : ι (Algebra.norm (A F) z) = z * D.bar z := by
  conv_rhs => rw [← mkE_co D z]
  conv_lhs => rw [← mkE_co D z]
  rw [norm_mkE, bar_mkE, mkE_mul_bar]

private theorem eq_zero_of_neg_eq {t : A F} (h : -t = t) : t = 0 := by
  have h2 : rt (2 : F) * t = 0 := by
    have : rt (2 : F) = 2 := map_ofNat _ 2
    rw [this, two_mul]
    nth_rw 1 [← h]
    simp
  have h3 : rt (2⁻¹ : F) * (rt (2 : F) * t) = t := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one, one_mul]
  rw [← h3, h2, mul_zero]

private theorem mkE_of_fixed {z : A E} (h : D.bar z = z) : D.mkE (D.co z 0) 0 = z := by
  have h1 : D.mkE (D.co z 0) (-D.co z 1) = D.mkE (D.co z 0) (D.co z 1) := by
    rw [← bar_mkE, mkE_co, h]
  have h2 := congrArg (fun y => D.co y 1) h1
  simp only [coordinate_embedNorm_one] at h2
  have h3 := eq_zero_of_neg_eq h2
  conv_rhs => rw [← mkE_co D z, h3]

private noncomputable def st (X : Matrix (Fin 2) (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E) := (X.map D.bar)ᵀ

private theorem st_mul (X Y : Matrix (Fin 2) (Fin 2) (A E)) : st D (X * Y) = st D Y * st D X := by
  simp only [st, Matrix.map_mul, Matrix.transpose_mul]

private theorem st_one : st D 1 = 1 := by
  simp [st, Matrix.map_one]

private theorem bar_bar (z : A E) : D.bar (D.bar z) = z := by
  conv_lhs => rw [← mkE_co D z]
  rw [bar_mkE, bar_mkE, neg_neg, mkE_co]

private theorem st_st (X : Matrix (Fin 2) (Fin 2) (A E)) : st D (st D X) = X := by
  ext i j
  simp [st, bar_bar]

private theorem st_herm (v : V4 F) : st D (D.herm v) = D.herm v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [st, Dat.herm, bar_mkE]

private theorem unherm_herm (v : V4 F) : D.unherm (D.herm v) = v := by
  funext i
  fin_cases i <;> simp [Dat.unherm, Dat.herm, coordinate_embedNorm_zero, coordinate_embedNorm_one]

private theorem herm_unherm {X : Matrix (Fin 2) (Fin 2) (A E)} (h : st D X = X) :
    D.herm (D.unherm X) = X := by
  have e : ∀ i j, D.bar (X j i) = X i j := fun i j => congrFun (congrFun h i) j
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Dat.herm, Dat.unherm] using mkE_of_fixed D (e 0 0)
  · simpa [Dat.herm, Dat.unherm] using mkE_co D (X 0 1)
  · have := bar_mkE D (D.co (X 0 1) 0) (D.co (X 0 1) 1)
    rw [mkE_co, e] at this
    simpa [Dat.herm, Dat.unherm] using this.symm
  · simpa [Dat.herm, Dat.unherm] using mkE_of_fixed D (e 1 1)

private theorem act_eq (h : GL (Fin 2) (A E)) (v : V4 F) :
    D.act h v = D.unherm (h.val * D.herm v * st D h.val) := rfl

private theorem herm_act (h : GL (Fin 2) (A E)) (v : V4 F) :
    D.herm (D.act h v) = h.val * D.herm v * st D h.val := by
  rw [act_eq]
  apply herm_unherm
  rw [st_mul, st_mul, st_st, st_herm, mul_assoc]

private theorem act_one (v : V4 F) : D.act 1 v = v := by
  rw [act_eq, Units.val_one, st_one, one_mul, mul_one, unherm_herm]

private theorem act_mul (h h' : GL (Fin 2) (A E)) (v : V4 F) :
    D.act (h * h') v = D.act h (D.act h' v) := by
  rw [act_eq, act_eq D h, herm_act, Units.val_mul, st_mul]
  simp only [mul_assoc]

private theorem herm_add (v w : V4 F) : D.herm (v + w) = D.herm v + D.herm w := by
  have h0 : ∀ a b : A F, D.mkE (a + b) 0 = D.mkE a 0 + D.mkE b 0 := fun a b => by
    simpa using mkE_add D a 0 b 0
  have h1 := mkE_add D (v 2) (v 3) (w 2) (w 3)
  have h2 := mkE_add D (v 2) (-v 3) (w 2) (-w 3)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dat.herm, h0, h1, ← h2, neg_add, add_comm]

private theorem herm_smul (a : A F) (v : V4 F) : D.herm (a • v) = ι a • D.herm v := by
  have h0 : ∀ b : A F, D.mkE (a * b) 0 = ι a * D.mkE b 0 := fun b => by
    simpa using mkE_mul D a b 0
  have h1 := mkE_mul D a (v 2) (v 3)
  have h2 := mkE_mul D a (v 2) (-v 3)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dat.herm, h0, h1, ← h2]

private theorem unherm_add (X Y : Matrix (Fin 2) (Fin 2) (A E)) :
    D.unherm (X + Y) = D.unherm X + D.unherm Y := by
  funext i
  fin_cases i <;> simp [Dat.unherm, co_add]

private theorem unherm_smul (a : A F) (X : Matrix (Fin 2) (Fin 2) (A E)) :
    D.unherm (ι a • X) = a • D.unherm X := by
  funext i
  fin_cases i <;> simp [Dat.unherm, co_mul]

private theorem act_add (h : GL (Fin 2) (A E)) (v w : V4 F) :
    D.act h (v + w) = D.act h v + D.act h w := by
  simp only [act_eq, herm_add, mul_add, add_mul, unherm_add]

private theorem act_smul (h : GL (Fin 2) (A E)) (a : A F) (v : V4 F) :
    D.act h (a • v) = a • D.act h v := by
  simp only [act_eq, herm_smul, Matrix.mul_smul, Matrix.smul_mul, unherm_smul]

private noncomputable def actL (h : GL (Fin 2) (A E)) : V4 F →ₗ[A F] V4 F where
  toFun := D.act h
  map_add' := act_add D h
  map_smul' a v := act_smul D h a v

private theorem det_herm (v : V4 F) : (D.herm v).det = -ι (q4 D.δ v) := by
  rw [Matrix.det_fin_two]
  have h := mkE_mul_bar D (v 2) (v 3)
  have h0 : ∀ a : A F, D.mkE a 0 = ι a := fun a => by simp [Dat.mkE]
  simp only [Dat.herm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, h, h0]
  simp only [q4, map_sub, map_mul]
  ring

private theorem det_st (X : Matrix (Fin 2) (Fin 2) (A E)) : (st D X).det = D.bar X.det := by
  rw [st, Matrix.det_transpose, RingHom.map_det]
  rfl

private theorem adeleMap_nu (h : GL (Fin 2) (A E)) : ι (nu F h : A F) = h.val.det * D.bar h.val.det := by
  have : ((nu F h : (A F)ˣ) : A F) = Algebra.norm (A F) h.val.det := rfl
  rw [this, adeleMap_norm_eq]

private theorem q_act (h : GL (Fin 2) (A E)) (v : V4 F) :
    q4 D.δ (D.act h v) = (nu F h : A F) * q4 D.δ v := by
  apply AdeleBaseChange.adeleMap_injective (K := F) (L := E)
  have h1 := det_herm D (D.act h v)
  rw [herm_act, Matrix.det_mul, Matrix.det_mul, det_st, det_herm] at h1
  rw [map_mul, adeleMap_nu D]
  linear_combination h1

private theorem B_eq (δ : F) (v v' : V4 F) : B4 δ v v' = q4 δ (v + v') - q4 δ v - q4 δ v' := by
  simp only [B4, q4, Pi.add_apply]
  ring

end UpperTheory.ConvolutionTheory.R2.D.actionMatrixCoordinates

open UpperTheory.ConvolutionTheory.R2.D.actionMatrixCoordinates in
theorem UpperTheory.ConvolutionTheory.R2.D.actMat :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E), ∃ ρ : GL (Fin 2) (A E) →* GL (Fin 4) (A F), (∀ h v, D.act h v = (ρ h).val *ᵥ v) ∧
    (∀ h v, q4 D.δ (D.act h v) = (nu F h : A F) * q4 D.δ v) ∧ ∀ h v v', B4 D.δ (D.act h v) (D.act h v') = (nu F h : A F) * B4 D.δ v v' := by
  intro F E _ _ _ _ _ D
  let m : GL (Fin 2) (A E) →* Matrix (Fin 4) (Fin 4) (A F) :=
    { toFun := fun h => LinearMap.toMatrixAlgEquiv' (actL D h)
      map_one' := by
        have : actL D (1 : GL (Fin 2) (A E)) = 1 := LinearMap.ext (act_one D)
        rw [this, map_one]
      map_mul' := fun h h' => by
        have : actL D (h * h') = actL D h * actL D h' := LinearMap.ext (act_mul D h h')
        rw [this, map_mul] }
  refine ⟨m.toHomUnits, fun h v => ?_, q_act D, fun h v v' => ?_⟩
  · change D.act h v = LinearMap.toMatrixAlgEquiv' (actL D h) *ᵥ v
    rw [← Matrix.toLinAlgEquiv'_apply, Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
    rfl
  · rw [B_eq, B_eq, ← act_add, q_act, q_act, q_act]
    ring

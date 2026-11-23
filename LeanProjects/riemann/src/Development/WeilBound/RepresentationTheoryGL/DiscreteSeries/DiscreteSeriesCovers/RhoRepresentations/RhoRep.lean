import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

noncomputable section

open Finset Matrix

namespace PositivityTheory.RgDs.K

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma rr_toMK_one (ε : Fin n → Bool) : toMK (1 : KG ε) = 1 := rfl

lemma rr_toMK_mul {ε : Fin n → Bool} (k k' : KG ε) : toMK (k * k') = toMK k * toMK k' := rfl

lemma rr_toMK_inv {ε : Fin n → Bool} (k : KG ε) : (toMK k)⁻¹ = toMK k⁻¹ := by
  show _ = ((((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
  rw [Matrix.coe_units_inv]

lemma rr_adC_one (p q : Fin n × Fin n) : adC (1 : Matrix (Fin n) (Fin n) ℂ) p q = if p = q then 1 else 0 := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp only [adC, inv_one, Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1, h2, eq_comm]

lemma rr_adC_mul (A B : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n × Fin n) :
    adC (A * B) p q = ∑ r : Fin n × Fin n, adC B p r * adC A r q := by
  simp only [adC, Matrix.mul_inv_rev, Matrix.mul_apply, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r1 _ => Finset.sum_congr rfl fun r2 _ => ?_
  ring

lemma rr_prod_ite {l : ℕ} (w x : Fin l → Fin n × Fin n) :
    (∏ i, (if w i = x i then (1 : ℂ) else 0)) = if w = x then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma rr_op_one {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : T.op 1 = 1 := by
  simp [KType.op]

lemma rr_op_mul {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k k' : KG ε) (v : T.V) :
    T.op (k * k') v = T.op k (T.op k' v) := by
  simp [KType.op]

theorem rho_representation_holds : PositivityTheory.RgDs.K.RhoRep := by
  intro n ε Λ T m
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a
    funext x'
    simp only [rhoA, rr_toMK_one, rr_adC_one, rr_prod_ite, rr_op_one, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  · intro k k' a
    funext x'
    simp only [rhoA, map_sum, map_smul, Finset.smul_sum, smul_smul]
    refine Eq.trans ?_ (Finset.sum_comm (s := (Finset.univ : Finset (Fin x'.1 → Fin n × Fin n))) (t := (Finset.univ : Finset (Fin x'.1 → Fin n × Fin n)))).symm
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_smul, rr_op_mul]
    congr 1
    simp only [rr_toMK_mul, rr_adC_mul]
    rw [Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    ring
  · intro k a a'
    funext x'
    simp only [rhoA, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  · intro k c a
    funext x'
    simp only [rhoA, Pi.smul_apply, map_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [smul_comm]
  · intro a
    have hK : Continuous fun k : KG ε => toMK k :=
      (continuous_toM ε).comp continuous_subtype_val
    have hKi : Continuous fun k : KG ε => (toMK k)⁻¹ := by
      simp only [rr_toMK_inv]
      exact hK.comp continuous_inv
    have hop : ∀ v : T.V, Continuous fun k : KG ε => T.op k v := fun v =>
      (continuous_subtype_val.comp T.cont).clm_apply continuous_const
    refine continuous_pi fun x' => ?_
    simp only [rhoA]
    refine continuous_finsetSum _ fun w _ => ?_
    refine Continuous.smul ?_ (hop _)
    refine continuous_finsetProd _ fun i _ => ?_
    simp only [adC]
    exact ((continuous_apply _).comp ((continuous_apply _).comp hK)).mul
      ((continuous_apply _).comp ((continuous_apply _).comp hKi))

end PositivityTheory.RgDs.K

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupExpTwoSidedInverseUniqueStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogChain

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.LogJacobian

noncomputable section

variable {C : Type} [Field C] [CharZero C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def substSecondBlockZero (d : ℕ) : Fin d ⊕ Fin d → MvPowerSeries (Fin d) C :=
  Sum.elim (fun b => X b) (fun _ => 0)

theorem constantCoeff_substSecondBlockZero (d : ℕ) (s : Fin d ⊕ Fin d) : constantCoeff (substSecondBlockZero (C := C) d s) = 0 := by
  cases s <;> simp [substSecondBlockZero]

theorem hasSubst_substSecondBlockZero (d : ℕ) : HasSubst (substSecondBlockZero (C := C) d) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_substSecondBlockZero d)

def jacEntry (G : LogFGL v d) (k l : Fin d) : MvPowerSeries (Fin d) C :=
  subst (substSecondBlockZero d) (pderiv C (Sum.inr k) (G.F l))

theorem natCast_int (n : ℕ) : IsIntV v (n : C) := by
  induction n with
  | zero => simp [IsIntV]
  | succ n ih =>
    unfold IsIntV at *
    push_cast
    exact le_trans (le_min ih (by rw [v.map_one])) (v.map_add _ _)

theorem mvIsInt_pderiv {σ : Type} {f : MvPowerSeries σ C} (hf : MvIsInt v f) (i : σ) :
    MvIsInt v (pderiv C i f) := by
  intro n
  unfold IsIntV
  rw [coeff_pderiv, v.map_mul]
  have h2 : ((n i : C) + 1) = ((n i + 1 : ℕ) : C) := by push_cast; ring
  rw [h2]
  exact add_nonneg (hf _) (natCast_int _)

theorem mvIsInt_substSecondBlockZero (d : ℕ) (s : Fin d ⊕ Fin d) : MvIsInt v (substSecondBlockZero (C := C) d s) := by
  intro n
  unfold IsIntV
  cases s with
  | inl b => simp only [substSecondBlockZero, Sum.elim_inl]; rw [coeff_X]; split_ifs <;> simp
  | inr b => simp [substSecondBlockZero]

theorem jacEntry_int (G : LogFGL v d) (k l : Fin d) : MvIsInt v (jacEntry G k l) :=
  ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (mvIsInt_pderiv (G.F_int l) _) (mvIsInt_substSecondBlockZero d) (constantCoeff_substSecondBlockZero d)

theorem subst_zero_eq (g : MvPowerSeries (Fin d) C) :
    subst (fun _ : Fin d => (0 : MvPowerSeries (Fin d) C)) g = MvPowerSeries.C (constantCoeff g) := by
  have : (fun _ : Fin d => (0 : MvPowerSeries (Fin d) C)) = ((0 : Fin d → C) • X) := by
    funext i; simp
  rw [this, ← rescale_eq_subst, rescale_zero_apply]

theorem subst_substSecondBlockZero_firstBlock_log (G : LogFGL v d) (a : Fin d) :
    subst (substSecondBlockZero (C := C) d) (subst (fun b => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) (G.lg a))
      = G.lg a := by
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (fun b => constantCoeff_X _)) (hasSubst_substSecondBlockZero d)]
  have : (fun b : Fin d => subst (substSecondBlockZero (C := C) d) (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C))
      = fun b => X b := by
    funext b; rw [subst_X (hasSubst_substSecondBlockZero d)]; rfl
  rw [this, subst_self]; rfl

theorem subst_substSecondBlockZero_secondBlock (G : LogFGL v d) (g : MvPowerSeries (Fin d) C) :
    subst (substSecondBlockZero (C := C) d) (subst (fun b => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) g)
      = MvPowerSeries.C (constantCoeff g) := by
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (fun b => constantCoeff_X _)) (hasSubst_substSecondBlockZero d)]
  have : (fun b : Fin d => subst (substSecondBlockZero (C := C) d) (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C))
      = fun _ => 0 := by
    funext b; rw [subst_X (hasSubst_substSecondBlockZero d)]; rfl
  rw [this, subst_zero_eq]

theorem formalGroupLaw_subst_secondBlock_zero (G : LogFGL v d) (l : Fin d) : subst (substSecondBlockZero (C := C) d) (G.F l) = (X l : MvPowerSeries (Fin d) C) := by
  obtain ⟨⟨hE0, hlgE⟩, hElg, -⟩ := GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v d G
  have hF0c : ∀ l, constantCoeff (subst (substSecondBlockZero (C := C) d) (G.F l)) = 0 := fun l =>
    constantCoeff_subst_eq_zero (hasSubst_substSecondBlockZero d) (constantCoeff_substSecondBlockZero d) (G.F_const l)
  have hF0 : HasSubst (fun l => subst (substSecondBlockZero (C := C) d) (G.F l)) := hasSubst_of_constantCoeff_zero hF0c
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.lg_const
  have key : ∀ a, subst (fun l => subst (substSecondBlockZero (C := C) d) (G.F l)) (G.lg a) = G.lg a := by
    intro a
    rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero G.F_const) (hasSubst_substSecondBlockZero d), G.lg_F a,
      subst_add (hasSubst_substSecondBlockZero d), subst_substSecondBlockZero_firstBlock_log, subst_substSecondBlockZero_secondBlock G, G.lg_const a, map_zero, add_zero]
  have e1 : subst (fun l => subst (substSecondBlockZero (C := C) d) (G.F l)) (X l : MvPowerSeries (Fin d) C)
      = subst (substSecondBlockZero d) (G.F l) := subst_X hF0 l
  rw [← e1, ← hElg l, subst_comp_subst_apply hlg hF0]
  simp only [key, hElg]

theorem jac_lg_mul_jacEntry (G : LogFGL v d) (a k : Fin d) :
    ∑ l, pderiv C l (G.lg a) * jacEntry G k l = if a = k then 1 else 0 := by
  classical
  have h := congrArg (pderiv C (Sum.inr k)) (G.lg_F a)
  rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst G.F_const, map_add,
    ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst (fun b => constantCoeff_X _),
    ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst (fun b => constantCoeff_X _)] at h
  simp only [pderiv_X, Pi.single_apply, reduceCtorEq, if_false, mul_zero, Finset.sum_const_zero,
    zero_add, Sum.inr.injEq, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  have h2 := congrArg (subst (substSecondBlockZero (C := C) d)) h
  rw [subst_substSecondBlockZero_secondBlock G, ← coe_substAlgHom (hasSubst_substSecondBlockZero d), map_sum] at h2
  simp only [map_mul, coe_substAlgHom] at h2
  simp only [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero G.F_const) (hasSubst_substSecondBlockZero d), formalGroupLaw_subst_secondBlock_zero,
    subst_self, id] at h2
  have hc : constantCoeff (pderiv C k (G.lg a)) = if a = k then 1 else 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add, G.lg_lin]; simp
  simp only [jacEntry]
  rw [h2, hc]
  split_ifs <;> simp

theorem pderiv_expOf (G : LogFGL v d) (l k : Fin d) :
    pderiv C k (expOf G l) = subst (expOf G) (jacEntry G k l) := by
  classical
  obtain ⟨⟨hE0, hlgE⟩, -, -⟩ := GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v d G
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hE0
  let J : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) C) :=
    Matrix.of fun a l => subst (expOf G) (pderiv C l (G.lg a))
  let M : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) C) :=
    Matrix.of fun l k => pderiv C k (expOf G l)
  let N : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) C) :=
    Matrix.of fun l k => subst (expOf G) (jacEntry G k l)
  have hJM : J * M = 1 := by
    ext a k
    have h := congrArg (pderiv C k) (hlgE a)
    rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst hE0, pderiv_X, Pi.single_apply] at h
    simp only [J, M, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, h]
  have hJN : J * N = 1 := by
    refine Matrix.ext fun a k => ?_
    have h := congrArg (subst (expOf G)) (jac_lg_mul_jacEntry G a k)
    rw [← coe_substAlgHom hE, map_sum] at h
    simp only [map_mul, coe_substAlgHom] at h
    simp only [J, N, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, h]
    split_ifs
    · rw [← substAlgHom_apply hE, map_one]
    · rw [← substAlgHom_apply hE, map_zero]
  have hNJ : N * J = 1 := mul_eq_one_comm.mp hJN
  have hMN : M = N := by
    calc M = (N * J) * M := by rw [hNJ, Matrix.one_mul]
      _ = N * (J * M) := Matrix.mul_assoc _ _ _
      _ = N := by rw [hJM, Matrix.mul_one]
  exact congrFun (congrFun hMN l) k

end

theorem exists_integral_invariant_derivation : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (G : LogFGL v d), ∃ D : Fin d → Fin d → MvPowerSeries (Fin d) C, (∀ k l, MvIsInt v (D k l)) ∧ ∀ (f : MvPowerSeries (Fin d) C) (k : Fin d) (α : Fin d →₀ ℕ), ((α k : C) + 1) * coeff (α + Finsupp.single k 1) (subst (expOf G) f) = coeff α (subst (expOf G) (∑ l, D k l * (show MvPowerSeries (Fin d) C from fun β => ((β l : C) + 1) * coeff (β + Finsupp.single l 1) f))) := by
  intro C _ _ v d G
  refine ⟨jacEntry G, jacEntry_int G, fun f k α => ?_⟩
  obtain ⟨⟨hE0, -⟩, -, -⟩ := GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v d G
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hE0
  have hP : ∀ l, (show MvPowerSeries (Fin d) C from
      fun β => ((β l : C) + 1) * coeff (β + Finsupp.single l 1) f) = pderiv C l f := by
    intro l; ext β; rw [coeff_pderiv, mul_comm]; rfl
  simp only [hP]
  rw [mul_comm, ← coeff_pderiv, ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst hE0]
  simp only [pderiv_expOf]
  congr 1
  rw [← substAlgHom_apply hE, map_sum]
  simp only [map_mul, substAlgHom_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end GlobalTheory.LogJacobian

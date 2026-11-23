import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EnInParamKProd

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section IntRL

variable {ι K : Type} [Field K] {R : Subring K}

theorem en_IntR_mul {f g : MvPowerSeries ι K} (hf : IntR R f) (hg : IntR R g) : IntR R (f * g) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact R.sum_mem fun x _ => R.mul_mem (hf _) (hg _)

theorem en_IntR_one : IntR R (1 : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

theorem en_IntR_X (i : ι) : IntR R (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

theorem en_IntR_pow {f : MvPowerSeries ι K} (hf : IntR R f) (k : ℕ) : IntR R (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact en_IntR_one
  | succ k ih => rw [pow_succ]; exact en_IntR_mul ih hf

theorem en_IntR_prod {α : Type} (s : Finset α) (f : α → MvPowerSeries ι K) (h : ∀ a ∈ s, IntR R (f a)) :
    IntR R (∏ a ∈ s, f a) :=
  Finset.prod_induction f (IntR R) (fun _ _ => en_IntR_mul) en_IntR_one h

end IntRL

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

theorem en_places_add (j : ℕ) (i0 : X.Pl → ℕ) (gP : X.Pl → ℚ) (hLow : ∀ v, LowAtI X Y j v (i0 v) (gP v))
    (U1 : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc) (hU1 : IntR Y.Oc (inParamK p Y.Kc U1)) (I : X.ColCh j) :
    geP Y (applyD (X.PI j I i0) (X.ThZA Y.Kc j ((∏ v, en_F X Y j v) * U1))) ((∑ v, gP v : ℚ) : ℝ) := by
  classical
  have e1 : X.ThZA Y.Kc j ((∏ v, en_F X Y j v) * U1) = (∏ v, X.ThZA Y.Kc j (en_F X Y j v)) *
      MvPowerSeries.subst (fun i => X.ThZA Y.Kc j (en_Ec p Y.Kc i)) (inParamK p Y.Kc U1) := by
    rw [en_ThZA_mul, en_ThZA_prod]
    congr 1
    conv_lhs => rw [← en_Ec_inParamK p Y.Kc U1]
    unfold Sys.ThZA
    rw [MvPowerSeries.subst_comp_subst_apply (en_Ec_hs p Y.Kc) (en_coordZA_hs X Y.Kc j)]
  have ha : MvPowerSeries.HasSubst (fun i => X.ThZA Y.Kc j (en_Ec p Y.Kc i)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      MvPowerSeries.constantCoeff_subst_eq_zero (en_coordZA_hs X Y.Kc j) (en_coordZA_zero X Y.Kc j)
        (en_Ec_zero p Y.Kc i)
  rw [en_applyD_eq, e1]
  obtain ⟨B, hB⟩ := Gen.jp_subst_expand (en_mapP Y.Kc (X.ZA j) (X.FrI j) (X.PI j I i0))
    (∏ v, X.ThZA Y.Kc j (en_F X Y j v)) (fun i => X.ThZA Y.Kc j (en_Ec p Y.Kc i)) ha (inParamK p Y.Kc U1)
  rw [hB]
  refine valuation_coeff_ge_sum Y _ _ _ fun β _ => valuation_coeff_ge_smul Y (hU1 β) ?_
  set Ub : X.Pl → MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc := fun v =>
    ∏ i ∈ β.support.filter (fun i => en_pi X j i = v), (en_Ec p Y.Kc i) ^ (β i) with hUb
  have e2 : (β.prod fun i e => X.ThZA Y.Kc j (en_Ec p Y.Kc i) ^ e) = ∏ v, X.ThZA Y.Kc j (Ub v) := by
    unfold Finsupp.prod
    rw [← Finset.prod_fiberwise β.support (en_pi X j)]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hUb, en_ThZA_prod]
    exact Finset.prod_congr rfl fun i _ => (en_ThZA_pow X Y.Kc j _ _).symm
  have e3 : (∏ v, X.ThZA Y.Kc j (en_F X Y j v)) * ∏ v, X.ThZA Y.Kc j (Ub v) =
      ∏ v, X.ThZA Y.Kc j (en_F X Y j v * Ub v) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => (en_ThZA_mul X Y.Kc j _ _).symm
  have hG : ∀ v, X.ThZA Y.Kc j (en_F X Y j v * Ub v) ∈ Gen.SuppOn (Sigma.fst : X.ZA j → X.Pl) v := fun v =>
    en_ThZA_supp X Y.Kc j v (Subring.mul_mem _ (en_F_supp X Y j v) (Subring.prod_mem _ fun i hi =>
      Subring.pow_mem _ (by
        have := en_Ec_supp p Y.Kc (en_pi X j) i
        rw [(Finset.mem_filter.1 hi).2] at this
        exact this) _))
  have e4 : ∏ v, X.ThZA Y.Kc j (en_F X Y j v * Ub v) =
      ∏ v, Gen.atP v (Gen.resP v (X.ThZA Y.Kc j (en_F X Y j v * Ub v))) :=
    Finset.prod_congr rfl fun v _ => Gen.eq_atP v _ (hG v)
  have e5 : en_mapP Y.Kc (X.ZA j) (X.FrI j) (X.PI j I i0) =
      ∏ v, MvPolynomial.rename (Sigma.mk v) (en_Ploc X Y j I i0 v) := by
    rw [PI_eq_prod, map_prod]
    exact Finset.prod_congr rfl fun v _ => en_mapP_PIvS X Y j I i0 v
  rw [e2, e3, e4, e5, Gen.jp_prod]
  refine valuation_coeff_ge_prod_rat Y _ _ _ fun v _ => ?_
  have e6 : Gen.jp (en_Ploc X Y j I i0 v) (Gen.resP v (X.ThZA Y.Kc j (en_F X Y j v * Ub v))) =
      applyD (PIvS X j I (fun _ => i0 v) v) (X.ThZA Y.Kc j (en_F X Y j v * Ub v)) := by
    rw [en_applyD_eq, ← PIvS_congr, en_mapP_PIvS]
    conv_rhs => rw [Gen.eq_atP v _ (hG v)]
    rw [Gen.jp_rename]
  rw [e6]
  have hint : IntR Y.Oc (inParamK p Y.Kc (Ub v)) := by
    rw [hUb, en_inParamK_prod]
    refine en_IntR_prod _ _ fun i _ => ?_
    rw [en_inParamK_pow, en_inParamK_Ec]
    exact en_IntR_pow (en_IntR_X i) _
  exact fun n => hLow v (Ub v) hint I n

def KernelProductForm (D : Formalism.BasicNotions.D7) : Prop :=
  admitted D X Y → ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Y.Frm j La La'), ∃ U1 : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc, IntR Y.Oc (inParamK p Y.Kc U1) ∧
      Y.ThA j La La' φ = (∏ v, en_F X Y j v) * U1

variable {X Y}

theorem restPlaces_of (D : Formalism.BasicNotions.D7) (h : KernelProductForm X Y D) : RestPlaces X Y D := by
  intro hA j hj i0 gP hLow La La' h1 h2 φ I n
  obtain ⟨U1, hU1, e⟩ := h hA j hj La La' h1 h2 φ
  rw [e]
  have := en_places_add X Y j i0 gP hLow U1 hU1 I n
  push_cast at this
  exact this

end Formalism.MainNotions.FormalGroupSystem.Pf

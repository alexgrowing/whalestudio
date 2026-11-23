import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.FacEmbDomain

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section LogInv

variable (p : ℕ) [Fact p.Prime] (K1 : Type) [Field K1] [Algebra (K0 p) K1]

def en_L : PowerSeries K1 := PowerSeries.map (algebraMap (K0 p) K1) (logF p)

theorem en_logF_zero : PowerSeries.constantCoeff (logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, logF, PowerSeries.coeff_mk]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  simp [hp.ne']

theorem en_logF_one : PowerSeries.coeff 1 (logF p) = 1 := by
  rw [logF, PowerSeries.coeff_mk]
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have h1 : (1 : ℕ) ≠ p ^ (2 * 1) := by
    have : 1 < p ^ (2 * 1) := Nat.one_lt_pow (by norm_num) hp
    omega
  rw [if_neg h1]
  simp

theorem en_L_zero : PowerSeries.constantCoeff (en_L p K1) = 0 := by
  rw [en_L, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, en_logF_zero, map_zero]

theorem en_L_one : IsUnit (PowerSeries.coeff 1 (en_L p K1)) := by
  rw [en_L, PowerSeries.coeff_map, en_logF_one, map_one]
  exact isUnit_one

def en_E : PowerSeries K1 := (en_L p K1).substInvOfIsUnit (en_L_one p K1)

theorem en_E_zero : PowerSeries.constantCoeff (en_E p K1) = 0 :=
  PowerSeries.constantCoeff_substInvOfIsUnit _ _

variable {ι : Type}

def en_aL (i : ι) : MvPowerSeries ι K1 := PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1) (en_L p K1)

def en_Ec (i : ι) : MvPowerSeries ι K1 := PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1) (en_E p K1)

theorem en_inParamK_eq (f : MvPowerSeries ι K1) : inParamK p K1 f = MvPowerSeries.subst (en_aL p K1) f := rfl

theorem en_aL_zero (i : ι) : MvPowerSeries.constantCoeff (en_aL p K1 i) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) _ (en_L_zero p K1)

theorem en_Ec_zero (i : ι) : MvPowerSeries.constantCoeff (en_Ec p K1 i) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) _ (en_E_zero p K1)

variable [Finite ι]

theorem en_aL_hs : MvPowerSeries.HasSubst (en_aL p K1 : ι → MvPowerSeries ι K1) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (en_aL_zero p K1)

theorem en_Ec_hs : MvPowerSeries.HasSubst (en_Ec p K1 : ι → MvPowerSeries ι K1) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (en_Ec_zero p K1)

theorem en_aL_Ec (i : ι) : MvPowerSeries.subst (en_aL p K1) (en_Ec p K1 i) = (MvPowerSeries.X i : MvPowerSeries ι K1) := by
  have h1 : MvPowerSeries.subst (en_aL p K1) (en_Ec p K1 i) =
      PowerSeries.subst (en_aL p K1 i) (en_E p K1) := by
    unfold en_Ec PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X i).const (en_aL_hs p K1)]
    simp only [MvPowerSeries.subst_X (en_aL_hs p K1)]
  rw [h1, en_aL, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (en_L_zero p K1)) (PowerSeries.HasSubst.X i), en_E,
    PowerSeries.subst_substInvOfIsUnit_left _ (en_L_zero p K1), PowerSeries.subst_X (PowerSeries.HasSubst.X i)]

theorem en_Ec_aL (i : ι) : MvPowerSeries.subst (en_Ec p K1) (en_aL p K1 i) = (MvPowerSeries.X i : MvPowerSeries ι K1) := by
  have h1 : MvPowerSeries.subst (en_Ec p K1) (en_aL p K1 i) =
      PowerSeries.subst (en_Ec p K1 i) (en_L p K1) := by
    unfold en_aL PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X i).const (en_Ec_hs p K1)]
    simp only [MvPowerSeries.subst_X (en_Ec_hs p K1)]
  rw [h1, en_Ec, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (en_E_zero p K1)) (PowerSeries.HasSubst.X i), en_E,
    PowerSeries.subst_substInvOfIsUnit_right _ (en_L_zero p K1), PowerSeries.subst_X (PowerSeries.HasSubst.X i)]

theorem en_Ec_inParamK (U : MvPowerSeries ι K1) : MvPowerSeries.subst (en_Ec p K1) (inParamK p K1 U) = U := by
  rw [en_inParamK_eq, MvPowerSeries.subst_comp_subst_apply (en_aL_hs p K1) (en_Ec_hs p K1)]
  simp only [en_Ec_aL]
  rw [MvPowerSeries.subst_self]
  rfl

theorem en_inParamK_Ec (i : ι) : inParamK p K1 (en_Ec p K1 i) = (MvPowerSeries.X i : MvPowerSeries ι K1) :=
  en_aL_Ec p K1 i

theorem en_inParamK_mul (f g : MvPowerSeries ι K1) : inParamK p K1 (f * g) = inParamK p K1 f * inParamK p K1 g :=
  MvPowerSeries.subst_mul (en_aL_hs p K1) f g

theorem en_inParamK_prod {α : Type} (s : Finset α) (f : α → MvPowerSeries ι K1) :
    inParamK p K1 (∏ i ∈ s, f i) = ∏ i ∈ s, inParamK p K1 (f i) := by
  simp only [en_inParamK_eq, ← MvPowerSeries.coe_substAlgHom (en_aL_hs p K1), map_prod]

theorem en_inParamK_pow (f : MvPowerSeries ι K1) (n : ℕ) : inParamK p K1 (f ^ n) = inParamK p K1 f ^ n :=
  MvPowerSeries.subst_pow (en_aL_hs p K1) f n

theorem en_Ec_supp {Pl : Type} (π : ι → Pl) (i : ι) : en_Ec p K1 i ∈ Gen.SuppOn (R := K1) π (π i) := by
  unfold en_Ec PowerSeries.subst
  exact Gen.subst_mem (π := fun _ : Unit => π i) (PowerSeries.HasSubst.X i).const (fun _ _ _ _ => rfl)
    (fun _ _ => Gen.X_mem rfl)

end LogInv

theorem en_expS_supp {p : ℕ} [Fact p.Prime] {ι Pl : Type} (π : ι → Pl) (v : Pl) {f : MvPowerSeries ι (K0 p)}
    (hf : f ∈ Gen.SuppOn π v) : expS p f ∈ Gen.SuppOn π v := by
  intro n hn
  have e : MvPowerSeries.coeff n (expS p f) =
      ∑ k ∈ range (n.degree + 1), ((k.factorial : K0 p))⁻¹ * MvPowerSeries.coeff n (f ^ k) := rfl
  rw [e] at hn
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  exact (Subring.pow_mem _ hf k) n (right_ne_zero_of_mul hk)

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

def en_pi (j : ℕ) : X.EA j ⊕ X.EA j → X.Pl := Sum.elim Sigma.fst Sigma.fst

theorem en_coordZA_zero (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (x : X.EA j ⊕ X.EA j) :
    MvPowerSeries.constantCoeff (X.coordZA K' j x) = 0 := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA, map_sum]

theorem en_coordZA_hs (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) : MvPowerSeries.HasSubst (X.coordZA K' j) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (en_coordZA_zero X K' j)

theorem en_coordZA_supp (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (x : X.EA j ⊕ X.EA j) :
    X.coordZA K' j x ∈ Gen.SuppOn (R := K') (Sigma.fst : X.ZA j → X.Pl) (en_pi X j x) := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩
  · exact Subring.sum_mem _ fun s _ => Subring.mul_mem _ (Gen.C_mem _) (Gen.X_mem rfl)
  · exact Subring.sum_mem _ fun s _ => Subring.mul_mem _ (Gen.C_mem _) (Gen.X_mem rfl)

theorem en_ThZA_supp (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (v : X.Pl)
    {f : MvPowerSeries (X.EA j ⊕ X.EA j) K'} (hf : f ∈ Gen.SuppOn (en_pi X j) v) :
    X.ThZA K' j f ∈ Gen.SuppOn (Sigma.fst : X.ZA j → X.Pl) v :=
  Gen.subst_mem (en_coordZA_hs X K' j) hf fun s hs => hs ▸ en_coordZA_supp X K' j s

theorem en_ThZA_mul (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (f g : MvPowerSeries (X.EA j ⊕ X.EA j) K') :
    X.ThZA K' j (f * g) = X.ThZA K' j f * X.ThZA K' j g :=
  MvPowerSeries.subst_mul (en_coordZA_hs X K' j) f g

theorem en_ThZA_prod (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) {α : Type} (s : Finset α)
    (f : α → MvPowerSeries (X.EA j ⊕ X.EA j) K') : X.ThZA K' j (∏ i ∈ s, f i) = ∏ i ∈ s, X.ThZA K' j (f i) := by
  unfold Sys.ThZA
  simp only [← MvPowerSeries.coe_substAlgHom (en_coordZA_hs X K' j), map_prod]

theorem en_ThZA_pow (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (f : MvPowerSeries (X.EA j ⊕ X.EA j) K')
    (n : ℕ) : X.ThZA K' j (f ^ n) = X.ThZA K' j f ^ n :=
  MvPowerSeries.subst_pow (en_coordZA_hs X K' j) f n

def en_F (j : ℕ) (v : X.Pl) : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc :=
  MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v))

theorem en_PhAt_supp (j : ℕ) (v : X.Pl) : Y.PhAt j v ∈ Gen.SuppOn (en_pi X j) v := by
  unfold Pend.PhAt
  refine Subring.sum_mem _ fun e _ => ?_
  unfold sub2
  refine Gen.subst_mem (π := fun _ : Fin 2 => v) MvPowerSeries.HasSubst.X_X (fun _ _ _ _ => rfl) fun s _ => ?_
  fin_cases s
  · exact Gen.X_mem rfl
  · exact Gen.X_mem rfl

theorem en_F_supp (j : ℕ) (v : X.Pl) : en_F X Y j v ∈ Gen.SuppOn (en_pi X j) v :=
  Gen.map_mem _ (en_expS_supp _ v (Subring.neg_mem _ (en_PhAt_supp X Y j v)))

end Formalism.MainNotions.FormalGroupSystem.Pf

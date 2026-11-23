import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.DworkPowerSeriesWeights
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffEvenDerivativeEqZero

noncomputable section

open scoped BigOperators

namespace Formalism.MainNotions.DIV.Bridge.LetterLogIntegrality

open Formalism.MainNotions Formalism.DworkPowerSeriesWeights Formalism.MainNotions.DIV.Bridge.DworkPowerSeriesWeights

theorem no_low_bidegree_of_vanishing (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]) (h : product_zeroth_first_parts.B3 l d be) :
    NoLowBidegree be := by
  intro n hn
  obtain ⟨h1, h2, h3⟩ := h n hn
  have e1 : (product_zeroth_first_parts.bideg d n).1 = degE n := by
    unfold product_zeroth_first_parts.bideg degE
    simp only [Nat.even_iff]
    exact Finsupp.sum_fintype _ _ (by intro s; split_ifs <;> rfl)
  have e2 : (product_zeroth_first_parts.bideg d n).2 = degO n := by
    unfold product_zeroth_first_parts.bideg degO
    simp only [Nat.even_iff]
    exact Finsupp.sum_fintype _ _ (by intro s; split_ifs <;> rfl)
  refine ⟨Nat.pos_of_ne_zero (e1 ▸ h1), Nat.pos_of_ne_zero (e2 ▸ h2), ?_⟩
  rintro ⟨a, b⟩
  exact h3 (Prod.ext (e1.trans a) (e2.trans b))

theorem exists_prim (l n : ℕ) [Fact l.Prime] (hn : 0 < n) : ∃ ζ : ℂ_[l], IsPrimitiveRoot ζ n := by
  have : NeZero (n : ℂ_[l]) := ⟨by exact_mod_cast hn.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n ℂ_[l])
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 hn).ne')
  exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).mp hζ⟩

theorem prod_X_pow_monomial {σ K : Type} [Field K] [DecidableEq σ] (d : σ →₀ ℕ) :
    (d.prod fun s k => (MvPowerSeries.X s : MvPowerSeries σ K) ^ k) = MvPowerSeries.monomial d 1 := by
  induction d using Finsupp.induction with
  | zero => simp
  | single_add a b f ha hb ih =>
    rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), ih, Finsupp.prod_single_index (by simp),
      MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul]

theorem coeff_subst_scale {σ K : Type} [Field K] [Fintype σ] [DecidableEq σ] (c : σ → K) (f : MvPowerSeries σ K)
    (m : σ →₀ ℕ) : MvPowerSeries.coeff m (MvPowerSeries.subst (fun s => MvPowerSeries.C (c s) * MvPowerSeries.X s) f) =
      (m.prod fun s k => c s ^ k) * MvPowerSeries.coeff m f := by
  have ha : MvPowerSeries.HasSubst (fun s : σ => (MvPowerSeries.C (c s) * MvPowerSeries.X s : MvPowerSeries σ K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by simp)
  rw [MvPowerSeries.coeff_subst ha]
  have hp : ∀ d : σ →₀ ℕ, (d.prod fun s k => (MvPowerSeries.C (c s) * MvPowerSeries.X s : MvPowerSeries σ K) ^ k) =
      MvPowerSeries.C (d.prod fun s k => c s ^ k) * MvPowerSeries.monomial d 1 := by
    intro d
    simp_rw [mul_pow, ← map_pow]
    rw [Finsupp.prod_mul, ← prod_X_pow_monomial]
    congr 1
    simp only [Finsupp.prod, map_prod]
  simp_rw [hp, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_monomial]
  rw [finsum_eq_single _ m]
  · simp [mul_comm]
  · intro d hd
    simp [Ne.symm hd]

theorem lw_twist (l d : ℕ) [Fact l.Prime] [NeZero d] (ζ : ℂ_[l]) (s : ZMod d) : ζ ^ lw l s = product_zeroth_first_parts.twist l d ζ s := by
  unfold lw product_zeroth_first_parts.twist
  by_cases h : Even s.val
  · have h' : s.val % 2 = 0 := Nat.even_iff.mp h
    rw [if_pos h', if_pos h, one_mul]
    exact_mod_cast zpow_natCast ζ (l ^ s.val)
  · have h' : ¬ s.val % 2 = 0 := fun e => h (Nat.even_iff.mpr e)
    rw [if_neg h', if_neg h, neg_one_mul, zpow_neg]
    congr 1

theorem torus_invariant_of_teichmuller (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]) (ζ : ℂ_[l])
    (hζ : IsPrimitiveRoot ζ (l ^ d - 1)) (h : product_zeroth_first_parts.B2 l d be) : MvPowerSeries.subst (torus l ζ) be = be := by
  ext m
  have e : (torus l ζ : ZMod d → MvPowerSeries (ZMod d) ℂ_[l]) =
      fun s => MvPowerSeries.C (ζ ^ lw l s) * MvPowerSeries.X s := rfl
  rw [e, coeff_subst_scale]
  have h1 := h ζ hζ.pow_eq_one m
  rw [mul_comm]
  convert h1 using 2
  unfold Finsupp.prod
  exact Finset.prod_congr rfl (fun s _ => by show (ζ ^ lw l s) ^ m s = product_zeroth_first_parts.twist l d ζ s ^ m s; rw [lw_twist])

theorem prod_X_rename {σ τ K : Type} [Field K] [DecidableEq τ] (r : σ ≃ τ) (d : σ →₀ ℕ) :
    (d.prod fun w k => (MvPowerSeries.X (r w) : MvPowerSeries τ K) ^ k) =
      MvPowerSeries.monomial (Finsupp.equivMapDomain r d) 1 := by
  rw [← prod_X_pow_monomial, Finsupp.prod_equivMapDomain]

theorem coeff_subst_rename {σ τ K : Type} [Field K] [DecidableEq τ] [Finite σ] (r : σ ≃ τ) (f : MvPowerSeries σ K)
    (n : τ →₀ ℕ) : MvPowerSeries.coeff n (MvPowerSeries.subst (fun w => (MvPowerSeries.X (r w) : MvPowerSeries τ K)) f) =
      MvPowerSeries.coeff (Finsupp.equivMapDomain r.symm n) f := by
  have ha : MvPowerSeries.HasSubst (fun w : σ => (MvPowerSeries.X (r w) : MvPowerSeries τ K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by simp)
  rw [MvPowerSeries.coeff_subst ha]
  simp_rw [prod_X_rename, MvPowerSeries.coeff_monomial]
  rw [finsum_eq_single _ (Finsupp.equivMapDomain r.symm n)]
  · simp [← Finsupp.equivMapDomain_trans]
  · intro d hd
    have : n ≠ Finsupp.equivMapDomain r d := by
      intro h; apply hd; rw [h, ← Finsupp.equivMapDomain_trans]; simp
    simp [this]

def eV (d : ℕ) : Bool × ZMod d ≃ ZMod d × Fin 2 where
  toFun u := (u.2, if u.1 then 1 else 0)
  invFun w := (decide (w.2 = 1), w.1)
  left_inv u := by rcases u with ⟨c, s⟩; cases c <;> rfl
  right_inv w := by rcases w with ⟨s, i⟩; fin_cases i <;> rfl

theorem eV_false (d : ℕ) (s : ZMod d) : eV d (false, s) = (s, 0) := rfl
theorem eV_true (d : ℕ) (s : ZMod d) : eV d (true, s) = (s, 1) := rfl

section Subst
variable {σ τ K : Type} [Field K]

theorem subst_add' {b : σ → MvPowerSeries τ K} (hb : MvPowerSeries.HasSubst b) (f g : MvPowerSeries σ K) :
    MvPowerSeries.subst b (f + g) = MvPowerSeries.subst b f + MvPowerSeries.subst b g := by
  rw [← MvPowerSeries.coe_substAlgHom hb, map_add]

theorem subst_sub' {b : σ → MvPowerSeries τ K} (hb : MvPowerSeries.HasSubst b) (f g : MvPowerSeries σ K) :
    MvPowerSeries.subst b (f - g) = MvPowerSeries.subst b f - MvPowerSeries.subst b g := by
  rw [← MvPowerSeries.coe_substAlgHom hb, map_sub]

theorem subst_zero' {b : σ → MvPowerSeries τ K} (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (0 : MvPowerSeries σ K) = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom hb, map_zero]

end Subst

theorem hasSubst_XeV (l d : ℕ) [Fact l.Prime] [NeZero d] :
    MvPowerSeries.HasSubst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun u => by simp)

theorem cobX_eq (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]) :
    product_zeroth_first_parts.cobX l d be = MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
      MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) (de1 be) := by
  have hb := hasSubst_XeV l d
  unfold de1
  rw [subst_sub' hb, subst_sub' hb,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun s => by unfold s1; split_ifs <;> simp)) hb,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by simp [s0])) hb,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun s => by unfold s2; split_ifs <;> simp)) hb]
  have f1 : (fun s : ZMod d => MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
      MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) (s1 (K := ℂ_[l]) s)) =
      fun s => if Even s.val then (MvPowerSeries.X (s, 0) + MvPowerSeries.X (s, 1) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l])
        else MvPowerSeries.X (s, 0) := by
    funext s
    unfold s1
    by_cases h : Even s.val
    · have h' : s.val % 2 = 0 := Nat.even_iff.mp h
      rw [if_pos h', if_pos h, subst_add' hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb, eV_false, eV_true]
    · have h' : ¬ s.val % 2 = 0 := fun e => h (Nat.even_iff.mpr e)
      rw [if_neg h', if_neg h, add_zero, MvPowerSeries.subst_X hb, eV_false]
  have f0 : (fun s : ZMod d => MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
      MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) (s0 (K := ℂ_[l]) s)) =
      fun s => (MvPowerSeries.X (s, 0) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l]) := by
    funext s
    unfold s0
    rw [MvPowerSeries.subst_X hb, eV_false]
  have f2 : (fun s : ZMod d => MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
      MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) (s2 (K := ℂ_[l]) s)) =
      fun s => if Even s.val then (MvPowerSeries.X (s, 1) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l])
        else MvPowerSeries.X (s, 0) := by
    funext s
    unfold s2
    by_cases h : Even s.val
    · have h' : s.val % 2 = 0 := Nat.even_iff.mp h
      rw [if_pos h', if_pos h, MvPowerSeries.subst_X hb, eV_true]
    · have h' : ¬ s.val % 2 = 0 := fun e => h (Nat.even_iff.mpr e)
      rw [if_neg h', if_neg h, MvPowerSeries.subst_X hb, eV_false]
  rw [f1, f0, f2]
  rfl

theorem cobY_eq (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]) :
    product_zeroth_first_parts.cobY l d be = MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
      MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) (de2 be) := by
  have hb := hasSubst_XeV l d
  unfold de2
  rw [subst_sub' hb, subst_sub' hb,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun s => by unfold s1'; split_ifs <;> simp)) hb,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by simp [s0])) hb,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun s => by unfold s2'; split_ifs <;> simp)) hb]
  have f1 : (fun s : ZMod d => MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
      MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) (s1' (K := ℂ_[l]) s)) =
      fun s => if Even s.val then (MvPowerSeries.X (s, 0) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l])
        else MvPowerSeries.X (s, 0) + MvPowerSeries.X (s, 1) := by
    funext s
    unfold s1'
    by_cases h : Even s.val
    · have h' : s.val % 2 = 0 := Nat.even_iff.mp h
      rw [if_pos h', if_pos h, add_zero, MvPowerSeries.subst_X hb, eV_false]
    · have h' : ¬ s.val % 2 = 0 := fun e => h (Nat.even_iff.mpr e)
      rw [if_neg h', if_neg h, subst_add' hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb, eV_false, eV_true]
  have f0 : (fun s : ZMod d => MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
      MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) (s0 (K := ℂ_[l]) s)) =
      fun s => (MvPowerSeries.X (s, 0) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l]) := by
    funext s
    unfold s0
    rw [MvPowerSeries.subst_X hb, eV_false]
  have f2 : (fun s : ZMod d => MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
      MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) (s2' (K := ℂ_[l]) s)) =
      fun s => if Even s.val then (MvPowerSeries.X (s, 0) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l])
        else MvPowerSeries.X (s, 1) := by
    funext s
    unfold s2'
    by_cases h : Even s.val
    · have h' : s.val % 2 = 0 := Nat.even_iff.mp h
      rw [if_pos h', if_pos h, MvPowerSeries.subst_X hb, eV_false]
    · have h' : ¬ s.val % 2 = 0 := fun e => h (Nat.even_iff.mpr e)
      rw [if_neg h', if_neg h, MvPowerSeries.subst_X hb, eV_true]
  rw [f1, f0, f2]
  rfl

theorem jetLog_rename (l d : ℕ) [Fact l.Prime] [NeZero d] (u : Bool × ZMod d) :
    MvPowerSeries.subst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) : MvPowerSeries (V2 d) ℂ_[l]))
      (Formalism.BasicNotions.jetLogG l d (β := Fin 2) (eV d u)) = letterLog (K := ℂ_[l]) l u := by
  ext n
  rw [coeff_subst_rename, Equiv.symm_symm]
  have hdeg : Formalism.BasicNotions.JetTdeg (Finsupp.equivMapDomain (eV d) n) = n.degree := by
    unfold Formalism.BasicNotions.JetTdeg
    rw [Finsupp.sum_equivMapDomain, Finsupp.degree]
    rfl
  change (Formalism.BasicNotions.jetLogG l d (β := Fin 2) (eV d u)) (Finsupp.equivMapDomain (eV d) n) = (letterLog (K := ℂ_[l]) l u) n
  unfold Formalism.BasicNotions.jetLogG letterLog
  rw [hdeg]
  apply Finset.sum_congr rfl
  intro e _
  have hx : ((eV d u).1 - 2 * (e : ZMod d), (eV d u).2) = eV d (u.1, u.2 - 2 * (e : ZMod d)) := by
    rcases u with ⟨c, s⟩; cases c <;> rfl
  rw [hx]
  by_cases h : n = Finsupp.single (u.1, u.2 - 2 * (e : ZMod d)) ((l ^ 2) ^ e)
  · have h' : Finsupp.equivMapDomain (eV d) n = Finsupp.single (eV d (u.1, u.2 - 2 * (e : ZMod d))) ((l ^ 2) ^ e) := by
      rw [h, Finsupp.equivMapDomain_single]
    rw [if_pos h', if_pos h]
  · have h' : ¬ Finsupp.equivMapDomain (eV d) n =
        Finsupp.single (eV d (u.1, u.2 - 2 * (e : ZMod d))) ((l ^ 2) ^ e) := by
      intro h2
      apply h
      have := congrArg (Finsupp.equivMapDomain (eV d).symm) h2
      simpa [← Finsupp.equivMapDomain_trans] using this
    rw [if_neg h', if_neg h]

theorem letterLog_cc (l d : ℕ) [Fact l.Prime] [NeZero d] (x : V2 d) :
    MvPowerSeries.constantCoeff (letterLog (K := ℂ_[l]) l x) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  change (letterLog (K := ℂ_[l]) l x) 0 = 0
  unfold letterLog
  simp
  intro h; exact absurd h.symm (Finsupp.single_ne_zero.mpr one_ne_zero)

theorem jetLogG_cc (l d : ℕ) [Fact l.Prime] [NeZero d] (v : ZMod d × Fin 2) :
    MvPowerSeries.constantCoeff (Formalism.BasicNotions.jetLogG l d (β := Fin 2) v) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  change (Formalism.BasicNotions.jetLogG l d (β := Fin 2) v) 0 = 0
  unfold Formalism.BasicNotions.jetLogG
  simp [Formalism.BasicNotions.JetTdeg]
  intro h; exact absurd h.symm (Finsupp.single_ne_zero.mpr one_ne_zero)

theorem integral_letter_log_exp (l d : ℕ) [Fact l.Prime] [NeZero d] (D : MvPowerSeries (V2 d) ℂ_[l])
    (hD0 : MvPowerSeries.constantCoeff D = 0)
    (h : product_zeroth_first_parts.OverWOne l (MvPowerSeries.subst (Formalism.BasicNotions.jetLogG l d (β := Fin 2))
      (product_zeroth_first_parts.expS ℂ_[l] (MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
        MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) D)))) :
    Integral (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp D)) ∧
      MvPowerSeries.constantCoeff (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp D)) = 1 := by
  have hb := hasSubst_XeV l d
  have hbs : MvPowerSeries.HasSubst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) :
      MvPowerSeries (V2 d) ℂ_[l])) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by simp)
  have hJ : MvPowerSeries.HasSubst (Formalism.BasicNotions.jetLogG l d (β := Fin 2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (jetLogG_cc l d)
  have hD : MvPowerSeries.HasSubst (fun _ : Unit => D) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hD0)
  have hLr : MvPowerSeries.HasSubst (fun v : ZMod d × Fin 2 => letterLog (K := ℂ_[l]) l ((eV d).symm v)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => letterLog_cc l d _)
  have hrn : (fun v : ZMod d × Fin 2 => MvPowerSeries.subst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) :
      MvPowerSeries (V2 d) ℂ_[l])) (Formalism.BasicNotions.jetLogG l d (β := Fin 2) v)) =
      fun v => letterLog (K := ℂ_[l]) l ((eV d).symm v) := by
    funext v
    have := jetLog_rename l d ((eV d).symm v)
    rwa [Equiv.apply_symm_apply] at this
  have hexp : product_zeroth_first_parts.expS ℂ_[l] (MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
        MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) D) =
      MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
        MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) (mvExp D) := by
    unfold product_zeroth_first_parts.expS mvExp PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply hD hb]
  have key : MvPowerSeries.subst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) :
      MvPowerSeries (V2 d) ℂ_[l])) (MvPowerSeries.subst (Formalism.BasicNotions.jetLogG l d (β := Fin 2))
        (product_zeroth_first_parts.expS ℂ_[l] (MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
          MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) D))) =
      MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp D) := by
    rw [hexp, MvPowerSeries.subst_comp_subst_apply hJ hbs, hrn, MvPowerSeries.subst_comp_subst_apply hb hLr]
    congr 1
    funext u
    rw [MvPowerSeries.subst_X hLr, Equiv.symm_apply_apply]
  refine ⟨fun n => ?_, ?_⟩
  · rw [← key, coeff_subst_rename]
    exact (h.1 _).2
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← key, coeff_subst_rename, Finsupp.equivMapDomain_zero,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h.2

theorem unipotent_exp_haar_sqrt_bound (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l])
    (h0 : MvPowerSeries.constantCoeff be = 0) (h : product_zeroth_first_parts.B4 l d be) :
    (Integral (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp (de1 be))) ∧
      MvPowerSeries.constantCoeff (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp (de1 be))) = 1) ∧
    (Integral (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp (de2 be))) ∧
      MvPowerSeries.constantCoeff (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp (de2 be))) = 1) := by
  obtain ⟨hX, hY⟩ := h
  rw [cobX_eq] at hX
  rw [cobY_eq] at hY
  exact ⟨integral_letter_log_exp l d _ (constantCoeff_evenDerivative_eq_zero h0) hX, integral_letter_log_exp l d _ (constantCoeff_oddDerivative_eq_zero h0) hY⟩

theorem constant_coeff_zero_of_vanishing (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]) (h : product_zeroth_first_parts.B3 l d be) :
    MvPowerSeries.constantCoeff be = 0 := by
  by_contra hne
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at hne
  have := (h 0 hne).1
  simp [product_zeroth_first_parts.bideg] at this

theorem integrality_of_letter_log (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]) (h3 : product_zeroth_first_parts.B3 l d be)
    (h4 : product_zeroth_first_parts.B4 l d be) :
    (Integral (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp (de1 be))) ∧
      MvPowerSeries.constantCoeff (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp (de1 be))) = 1) ∧
    (Integral (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp (de2 be))) ∧
      MvPowerSeries.constantCoeff (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp (de2 be))) = 1) :=
  unipotent_exp_haar_sqrt_bound l d be (constant_coeff_zero_of_vanishing l d be h3) h4

end Formalism.MainNotions.DIV.Bridge.LetterLogIntegrality

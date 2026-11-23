import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQHW
import Formalism.PieriBlockIdeals.StatementLD
import Formalism.PieriBlockIdeals.PieriColumnMinors.DividedPowerZeroZeroVector

open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility

def resVar (R : Type*) [CommRing R] (p q : ℕ) (v : Fin (p + q) × Fin (p + q)) : MvPolynomial (Fin q × Fin q) R :=
  Fin.addCases (motive := fun _ => MvPolynomial (Fin q × Fin q) R)
    (fun a => Fin.addCases (motive := fun _ => MvPolynomial (Fin q × Fin q) R)
      (fun s => if a = s then 1 else 0) (fun _ => 0) v.2)
    (fun b => Fin.addCases (motive := fun _ => MvPolynomial (Fin q × Fin q) R)
      (fun _ => 0) (fun t => X (b, t)) v.2) v.1

def res (R : Type*) [CommRing R] (p q : ℕ) :
    MvPolynomial (Fin (p + q) × Fin (p + q)) R →ₐ[R] MvPolynomial (Fin q × Fin q) R :=
  aeval (resVar R p q)

def liftWord (p : ℕ) {q : ℕ} (ω : List (Fin q × Fin q × ℕ)) : List (Fin (p + q) × Fin (p + q) × ℕ) :=
  ω.map fun x => (Fin.natAdd p x.1, Fin.natAdd p x.2.1, x.2.2)

section
variable (R : Type*) [CommRing R] (p q : ℕ)

theorem lrb_var_ll (a s : Fin p) :
    resVar R p q (Fin.castAdd q a, Fin.castAdd q s) = if a = s then 1 else 0 := by
  simp [resVar]

theorem lrb_var_lr (a : Fin p) (t : Fin q) : resVar R p q (Fin.castAdd q a, Fin.natAdd p t) = 0 := by
  simp [resVar]

theorem lrb_var_rl (b : Fin q) (s : Fin p) : resVar R p q (Fin.natAdd p b, Fin.castAdd q s) = 0 := by
  simp [resVar]

theorem lrb_var_rr (b t : Fin q) : resVar R p q (Fin.natAdd p b, Fin.natAdd p t) = X (b, t) := by
  simp [resVar]

theorem lrb_res_X (v : Fin (p + q) × Fin (p + q)) : res R p q (X v) = resVar R p q v := by
  simp [res]

theorem lrb_cast_ne_nat (a : Fin p) (b : Fin q) : Fin.castAdd q a ≠ Fin.natAdd p b := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  have := a.isLt
  omega

theorem lrb_mapC (v : Fin (p + q) × Fin (p + q)) :
    Polynomial.mapAlgHom (res R p q) (Polynomial.C (X v)) = Polynomial.C (resVar R p q v) := by
  rw [Polynomial.coe_mapAlgHom, Polynomial.map_C]
  exact congrArg _ (lrb_res_X R p q v)

theorem lrb_mapX : Polynomial.mapAlgHom (res R p q) Polynomial.X = Polynomial.X := by
  rw [Polynomial.coe_mapAlgHom, Polynomial.map_X]

theorem lrb_rowGen (b b' : Fin q) :
    (Polynomial.mapAlgHom (res R p q)).comp (rowGen R (Fin.natAdd p b) (Fin.natAdd p b')) =
      (rowGen R b b').comp (res R p q) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  obtain ⟨x, s⟩ := v
  simp only [AlgHom.comp_apply, lrb_res_X]
  rw [rowGen, aeval_X]
  refine Fin.addCases (fun a => ?_) (fun c => ?_) x
  · rw [if_neg (lrb_cast_ne_nat p q a b'), add_zero, lrb_mapC]
    refine Fin.addCases (fun s' => ?_) (fun t => ?_) s
    · rw [lrb_var_ll]
      split_ifs <;> simp
    · rw [lrb_var_lr]
      simp
  · refine Fin.addCases (fun s' => ?_) (fun t => ?_) s
    · rw [map_add, lrb_mapC, lrb_var_rl]
      split_ifs
      · rw [map_mul, lrb_mapC, lrb_var_rl]
        simp
      · simp
    · rw [map_add, lrb_mapC, lrb_var_rr, rowGen, aeval_X]
      simp only [Fin.natAdd_inj]
      split_ifs
      · rw [map_mul, lrb_mapC, lrb_mapX, lrb_var_rr]
      · simp

theorem res_rowDiv (b b' : Fin q) (k : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) R) :
    res R p q (rowDiv R (Fin.natAdd p b) (Fin.natAdd p b') k f) = rowDiv R b b' k (res R p q f) := by
  have h := congrArg (fun φ => (φ f).coeff k) (lrb_rowGen R p q b b')
  simp only [AlgHom.comp_apply, Polynomial.coeff_mapAlgHom_apply] at h
  exact h

theorem res_applyWord (ω : List (Fin q × Fin q × ℕ)) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) R) :
    res R p q (applyWord R (liftWord p ω) f) = applyWord R ω (res R p q f) := by
  induction ω with
  | nil => rfl
  | cons x ω ih =>
    change res R p q (rowDiv R _ _ _ (applyWord R (liftWord p ω) f)) = rowDiv R _ _ _ (applyWord R ω (res R p q f))
    rw [res_rowDiv, ih]

theorem res_eval_id (f : MvPolynomial (Fin (p + q) × Fin (p + q)) R) :
    eval (idFrame R q q) (res R p q f) = eval (idFrame R (p + q) (p + q)) f := by
  have h : ((aeval (idFrame R q q) : MvPolynomial (Fin q × Fin q) R →ₐ[R] R).comp (res R p q)) =
      (aeval (idFrame R (p + q) (p + q)) : MvPolynomial (Fin (p + q) × Fin (p + q)) R →ₐ[R] R) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    obtain ⟨x, s⟩ := v
    simp only [AlgHom.comp_apply, lrb_res_X, aeval_X]
    refine Fin.addCases (fun a => ?_) (fun c => ?_) x <;> refine Fin.addCases (fun s' => ?_) (fun t => ?_) s
    · rw [lrb_var_ll]
      simp only [idFrame, Fin.val_castAdd, Fin.val_inj]
      split_ifs <;> simp
    · rw [lrb_var_lr]
      have := a.isLt
      simp only [idFrame, Fin.val_castAdd, Fin.val_natAdd, map_zero]
      rw [if_neg (by omega)]
    · rw [lrb_var_rl]
      have := s'.isLt
      simp only [idFrame, Fin.val_castAdd, Fin.val_natAdd, map_zero]
      rw [if_neg (by omega)]
    · rw [lrb_var_rr, aeval_X]
      simp only [idFrame, Fin.val_natAdd, add_right_inj]
  have h2 := congrArg (fun φ => φ f) h
  simpa [AlgHom.comp_apply, aeval_eq_eval] using h2

end

section
variable (R : Type*) [CommRing R] (p q : ℕ)

theorem lrb_aeval_hom {σ τ Mo : Type*} [AddCommMonoid Mo] (w : τ → Mo) (φ : σ → MvPolynomial τ R) (ω : σ → Mo)
    (hφ : ∀ v, IsWeightedHomogeneous w (φ v) (ω v)) (x : MvPolynomial σ R) (κ : Mo)
    (hx : IsWeightedHomogeneous ω x κ) : IsWeightedHomogeneous w (aeval φ x) κ := by
  conv => enter [2, 2]; rw [x.as_sum]
  rw [map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [aeval_monomial, ← hx (mem_support_iff.mp hd), Finsupp.weight_apply, MvPolynomial.algebraMap_eq]
  refine IsWeightedHomogeneous.C_mul ?_ _
  unfold Finsupp.prod Finsupp.sum
  exact IsWeightedHomogeneous.prod _ _ _ fun v _ => (hφ v).pow _

theorem lrb_proj {σ M M' : Type*} [AddCommMonoid M] [AddCommMonoid M'] (π : M →+ M') (w : σ → M)
    (x : MvPolynomial σ R) (κ : M) (hx : IsWeightedHomogeneous w x κ) :
    IsWeightedHomogeneous (fun v => π (w v)) x (π κ) := by
  intro d hd
  rw [← hx hd, Finsupp.weight_apply, Finsupp.weight_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun v _ => ?_
  rw [map_nsmul]

def lrbPi : (Fin (p + q) → ℕ) →+ (Fin q → ℕ) where
  toFun g := fun t => g (Fin.natAdd p t)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem lrb_pi_single_cast (a : Fin p) : lrbPi p q (Pi.single (Fin.castAdd q a) 1) = 0 := by
  funext t
  change (Pi.single (Fin.castAdd q a) 1 : Fin (p + q) → ℕ) (Fin.natAdd p t) = 0
  rw [Pi.single_eq_of_ne (lrb_cast_ne_nat p q a t).symm]

theorem lrb_pi_single_nat (c : Fin q) : lrbPi p q (Pi.single (Fin.natAdd p c) 1) = Pi.single c 1 := by
  funext t
  change (Pi.single (Fin.natAdd p c) 1 : Fin (p + q) → ℕ) (Fin.natAdd p t) = _
  by_cases h : t = c
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun h' => h (by simpa using h'))]

theorem lrb_var_col (v : Fin (p + q) × Fin (p + q)) :
    IsWeightedHomogeneous (colW q q) (resVar R p q v) (lrbPi p q (colW (p + q) (p + q) v)) := by
  obtain ⟨x, s⟩ := v
  refine Fin.addCases (fun a => ?_) (fun c => ?_) x <;> refine Fin.addCases (fun s' => ?_) (fun t => ?_) s
  · rw [lrb_var_ll]
    change IsWeightedHomogeneous _ _ (lrbPi p q (Pi.single (Fin.castAdd q s') 1))
    rw [lrb_pi_single_cast]
    split_ifs
    · exact isWeightedHomogeneous_one _ _
    · exact isWeightedHomogeneous_zero _ _ _
  · rw [lrb_var_lr]
    exact isWeightedHomogeneous_zero _ _ _
  · rw [lrb_var_rl]
    exact isWeightedHomogeneous_zero _ _ _
  · rw [lrb_var_rr]
    change IsWeightedHomogeneous _ _ (lrbPi p q (Pi.single (Fin.natAdd p t) 1))
    rw [lrb_pi_single_nat]
    exact isWeightedHomogeneous_X _ _ _

theorem lrb_var_row (v : Fin (p + q) × Fin (p + q)) :
    IsWeightedHomogeneous (rowW q q) (resVar R p q v) (lrbPi p q (rowW (p + q) (p + q) v)) := by
  obtain ⟨x, s⟩ := v
  refine Fin.addCases (fun a => ?_) (fun c => ?_) x <;> refine Fin.addCases (fun s' => ?_) (fun t => ?_) s
  · rw [lrb_var_ll]
    change IsWeightedHomogeneous _ _ (lrbPi p q (Pi.single (Fin.castAdd q a) 1))
    rw [lrb_pi_single_cast]
    split_ifs
    · exact isWeightedHomogeneous_one _ _
    · exact isWeightedHomogeneous_zero _ _ _
  · rw [lrb_var_lr]
    exact isWeightedHomogeneous_zero _ _ _
  · rw [lrb_var_rl]
    exact isWeightedHomogeneous_zero _ _ _
  · rw [lrb_var_rr]
    change IsWeightedHomogeneous _ _ (lrbPi p q (Pi.single (Fin.natAdd p c) 1))
    rw [lrb_pi_single_nat]
    exact isWeightedHomogeneous_X _ _ _

theorem res_rowHom (μ : Fin (p + q) → ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) R)
    (hf : IsWeightedHomogeneous (rowW (p + q) (p + q)) f μ) :
    IsWeightedHomogeneous (rowW q q) (res R p q f) (fun b => μ (Fin.natAdd p b)) :=
  lrb_aeval_hom R (rowW q q) (resVar R p q) _ (lrb_var_row R p q) f _ (lrb_proj R (lrbPi p q) _ f μ hf)

theorem res_colHom (μ : Fin (p + q) → ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) R)
    (hf : IsWeightedHomogeneous (colW (p + q) (p + q)) f μ) :
    IsWeightedHomogeneous (colW q q) (res R p q f) (fun b => μ (Fin.natAdd p b)) :=
  lrb_aeval_hom R (colW q q) (resVar R p q) _ (lrb_var_col R p q) f _ (lrb_proj R (lrbPi p q) _ f μ hf)

def lrbResO : MvPolynomial (Option (Fin (p + q) × Fin (p + q))) R →ₐ[R] MvPolynomial (Option (Fin q × Fin q)) R :=
  aeval fun o => o.elim (X none) fun v => rename some (resVar R p q v)

theorem lrb_resO_some (v : Fin (p + q) × Fin (p + q)) :
    lrbResO R p q (X (some v)) = rename some (resVar R p q v) := by
  simp [lrbResO]

theorem lrb_resO_none : lrbResO R p q (X none) = X none := by
  simp [lrbResO]

theorem lrb_resO_rename :
    (lrbResO R p q).comp (rename some) = (rename some).comp (res R p q) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  simp only [AlgHom.comp_apply, rename_X, lrb_resO_some, lrb_res_X]

theorem lrb_resO_colAdd (l j : Fin q) :
    (lrbResO R p q).comp (colAddGen R (Fin.natAdd p l) (Fin.natAdd p j)) = (colAddGen R l j).comp (res R p q) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  obtain ⟨x, s⟩ := v
  simp only [AlgHom.comp_apply, lrb_res_X]
  rw [colAddGen, aeval_X]
  refine Fin.addCases (fun a => ?_) (fun c => ?_) x <;> refine Fin.addCases (fun s' => ?_) (fun t => ?_) s
  · rw [if_neg (lrb_cast_ne_nat p q s' j), lrb_resO_some, lrb_var_ll]
    split_ifs <;> simp
  · simp only [Fin.natAdd_inj]
    split_ifs
    · rw [map_add, map_mul, lrb_resO_some, lrb_resO_some, lrb_var_lr, lrb_var_lr]
      simp
    · rw [lrb_resO_some, lrb_var_lr]
      simp
  · rw [if_neg (lrb_cast_ne_nat p q s' j), lrb_resO_some, lrb_var_rl]
    simp
  · simp only [Fin.natAdd_inj]
    rw [lrb_var_rr, colAddGen, aeval_X]
    simp only
    split_ifs
    · rw [map_add, map_mul, lrb_resO_some, lrb_resO_some, lrb_resO_none, lrb_var_rr, lrb_var_rr, rename_X, rename_X]
    · rw [lrb_resO_some, lrb_var_rr, rename_X]

theorem res_mem (w : ℕ) (lam2 : Fin q → ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) R)
    (hf : f ∈ dualWeyl R (p + q) (p + q) (LD.blockWt p q w lam2)) : res R p q f ∈ dualWeyl R q q lam2 := by
  rw [rowst_mem_dualWeyl_iff] at hf ⊢
  refine ⟨?_, fun l j hlj => ?_⟩
  · have h := res_colHom R p q _ f hf.1
    have e : (fun b => LD.blockWt p q w lam2 (Fin.natAdd p b)) = lam2 := by
      funext b
      exact Fin.append_right _ _ b
    rwa [e] at h
  · have h := hf.2 (Fin.natAdd p l) (Fin.natAdd p j) (by
      rw [Fin.lt_def] at hlj ⊢
      simpa using hlj)
    have h1 := congrArg (fun φ => φ f) (lrb_resO_colAdd R p q l j)
    have h2 := congrArg (fun φ => φ f) (lrb_resO_rename R p q)
    simp only [AlgHom.comp_apply] at h1 h2
    rw [← h1, h, h2]

end

theorem res_hw (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, lam2 b ≤ w) :
    res ℚ p q (hw ℚ le_rfl (LD.blockWt p q w lam2)) = hw ℚ le_rfl lam2 := by
  have hA := LD.ld_blockWt_anti p q w lam2 ha hb
  have hm := res_mem ℚ p q w lam2 _ (hwMem ℚ (p + q) (p + q) le_rfl _ hA)
  obtain ⟨c, hc⟩ := hwLine ℚ q q le_rfl lam2 ha _ hm (fun a b hab k hk => by
    rw [← res_rowDiv, hwRaise ℚ (p + q) (p + q) le_rfl _ (Fin.natAdd p a) (Fin.natAdd p b) k (by
      rw [Fin.lt_def] at hab ⊢
      simpa using hab) hk, map_zero])
  have h1 := res_eval_id ℚ p q (hw ℚ le_rfl (LD.blockWt p q w lam2))
  rw [lehw_eval_idFrame_hw, hc, smul_eval, lehw_eval_idFrame_hw, mul_one] at h1
  rw [hc, h1, one_smul]

end Formalism.CohomologicalDescent.LR

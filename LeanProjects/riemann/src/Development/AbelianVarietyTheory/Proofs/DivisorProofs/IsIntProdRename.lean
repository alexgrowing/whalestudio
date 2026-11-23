import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupExpTwoSidedInverseUniqueStatement
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth.CharBound

noncomputable section

variable {C : Type} [Field C]

theorem isIntV_add' {v : AddValuation C (WithTop ℝ)} {x y : C} (hx : IsIntV v x) (hy : IsIntV v y) :
    IsIntV v (x + y) :=
  le_trans (le_min hx hy) (v.map_add x y)

theorem isIntV_mul' {v : AddValuation C (WithTop ℝ)} {x y : C} (hx : IsIntV v x) (hy : IsIntV v y) :
    IsIntV v (x * y) := by
  unfold IsIntV at *
  rw [v.map_mul]
  exact add_nonneg hx hy

theorem isIntV_zero' {v : AddValuation C (WithTop ℝ)} : IsIntV v 0 := by
  unfold IsIntV; rw [v.map_zero]; exact le_top

theorem isIntV_one' {v : AddValuation C (WithTop ℝ)} : IsIntV v 1 := by
  unfold IsIntV; rw [v.map_one]

theorem mvIsInt_mul' {v : AddValuation C (WithTop ℝ)} {σ : Type} {F G : MvPowerSeries σ C}
    (hF : MvIsInt v F) (hG : MvIsInt v G) : MvIsInt v (F * G) := by
  classical
  intro α
  rw [coeff_mul]
  exact Finset.sum_induction _ (IsIntV v) (fun _ _ => isIntV_add') isIntV_zero'
    fun p _ => isIntV_mul' (hF _) (hG _)

theorem mvIsInt_one' {v : AddValuation C (WithTop ℝ)} {σ : Type} : MvIsInt v (1 : MvPowerSeries σ C) := by
  classical
  intro α
  rw [coeff_one]
  split_ifs
  exacts [isIntV_one', isIntV_zero']

theorem mvIsInt_X' {v : AddValuation C (WithTop ℝ)} {σ : Type} (s : σ) :
    MvIsInt v (X s : MvPowerSeries σ C) := by
  classical
  intro α
  rw [coeff_X]
  split_ifs
  exacts [isIntV_one', isIntV_zero']

theorem mvIsInt_pow' {v : AddValuation C (WithTop ℝ)} {σ : Type} {F : MvPowerSeries σ C}
    (hF : MvIsInt v F) (n : ℕ) : MvIsInt v (F ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact mvIsInt_one'
  | succ n ih => rw [pow_succ]; exact mvIsInt_mul' ih hF

theorem mvIsInt_subst' {v : AddValuation C (WithTop ℝ)} {σ τ : Type} {a : σ → MvPowerSeries τ C}
    (ha : HasSubst a) (hai : ∀ s, MvIsInt v (a s)) {F : MvPowerSeries σ C} (hF : MvIsInt v F) :
    MvIsInt v (subst a F) := by
  intro β
  rw [coeff_subst ha]
  refine finsum_induction (IsIntV v) isIntV_zero' (fun _ _ => isIntV_add') fun e => ?_
  rw [smul_eq_mul]
  refine isIntV_mul' (hF e) ?_
  exact Finset.prod_induction _ (MvIsInt v) (fun _ _ => mvIsInt_mul') mvIsInt_one'
    (fun s _ => mvIsInt_pow' (hai s) _) β

theorem isInt_prod_rename (v : AddValuation C (WithTop ℝ)) (i d : ℕ)
    (χ : Fin i → MvPowerSeries (Fin d) C) (h : ∀ b, MvIsInt v (χ b)) :
    MvIsInt v (∏ b, subst (fun e : Fin d =>
      (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (χ b)) :=
  Finset.prod_induction _ (MvIsInt v) (fun _ _ => mvIsInt_mul') mvIsInt_one'
    fun b _ => mvIsInt_subst' (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
      (fun _ => mvIsInt_X' _) (h b)

variable [CharZero C]

theorem coeff_mvExp_lin {σ : Type} [Fintype σ] (c : σ → C) (α : σ →₀ ℕ) :
    coeff α (Formalism.L2.Th1.C.mvExp (∑ s, c s • (X s : MvPowerSeries σ C))) =
      α.prod fun s n => c s ^ n / (n.factorial : C) := by
  classical
  set L : MvPowerSeries σ C := ∑ s, c s • (X s : MvPowerSeries σ C) with hLdef
  have hL : constantCoeff L = 0 := by simp [hLdef]
  have hnL : constantCoeff (-L) = 0 := by rw [map_neg, hL, neg_zero]
  let g : MvPowerSeries σ C := fun β => β.prod fun s n => c s ^ n / (n.factorial : C)
  have hg : ∀ β, coeff β g = ∏ s, c s ^ β s / ((β s).factorial : C) := fun β => by
    show (β.prod fun s n => c s ^ n / (n.factorial : C)) = _
    exact Finsupp.prod_fintype _ _ (fun s => by simp)
  have hpL : ∀ i, pderiv C i L = c i • (1 : MvPowerSeries σ C) := fun i => by
    simp [hLdef, pderiv_X, Pi.single_apply]
  have hpg : ∀ i, pderiv C i g = c i • g := fun i => by
    ext β
    rw [coeff_pderiv, hg, coeff_smul, hg, Fintype.prod_eq_mul_prod_compl i,
      Fintype.prod_eq_mul_prod_compl i (fun s => c s ^ β s / ((β s).factorial : C))]
    have hrest : ∏ s ∈ ({i}ᶜ : Finset σ), c s ^ (β + Finsupp.single i 1 : σ →₀ ℕ) s /
        (((β + Finsupp.single i 1 : σ →₀ ℕ) s).factorial : C) =
        ∏ s ∈ ({i}ᶜ : Finset σ), c s ^ β s / ((β s).factorial : C) := by
      refine Finset.prod_congr rfl fun s hs => ?_
      have hs' : s ≠ i := by simpa using hs
      simp [Finsupp.single_apply, Ne.symm hs']
    rw [hrest]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [Nat.factorial_succ]
    have h0 : ((β i).factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h1 : ((β i : C) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
    push_cast
    field_simp
    ring
  have hcg : constantCoeff g = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hg]
    simp
  have key : g * Formalism.L2.Th1.C.mvExp (-L) = 1 := by
    refine pderiv.ext (fun i => ?_) ?_
    · rw [Derivation.leibniz, Formalism.L2.Th1.C.pderiv_mvExp hnL, map_neg, hpL, hpg, pderiv_one]
      simp only [smul_eq_mul, Algebra.smul_def]
      ring
    · rw [map_mul, hcg, Formalism.L2.Th1.C.constantCoeff_mvExp hnL, map_one, mul_one]
  have hE : Formalism.L2.Th1.C.mvExp L = g := by
    calc Formalism.L2.Th1.C.mvExp L = (g * Formalism.L2.Th1.C.mvExp (-L)) * Formalism.L2.Th1.C.mvExp L := by
          rw [key, one_mul]
      _ = g := by rw [mul_assoc, Formalism.L2.Th1.C.mvExp_neg hL, mul_one]
  rw [hE]
  rfl

theorem derivAt0_eq_eval {σ : Type} (P : MvPolynomial σ C) (g : MvPowerSeries σ C) (w : σ → C)
    (hg : ∀ α, coeff α g = α.prod fun s n => w s ^ n / (n.factorial : C)) :
    derivAt0 P g = MvPolynomial.eval w P := by
  rw [MvPolynomial.eval_eq, derivAt0]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [hg, mfact, mul_assoc, ← Finsupp.prod_mul]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  have : (((α s).factorial : ℕ) : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

theorem eval_detPow (i c : ℕ) (H : Matrix (Fin i) (Fin i) C) :
    MvPolynomial.eval (fun x : (Σ _ : Fin i, Fin i) => H x.2 x.1) (detPow C i c) = H.det ^ c := by
  rw [detPow, map_pow, RingHom.map_det]
  congr 2
  ext a b
  simp [RingHom.mapMatrix_apply]

open Formalism.L2.Th1.C in

theorem subst_col (v : AddValuation C (WithTop ℝ)) {i d : ℕ} (G : LogFGL v d) (u : Fin i → Fin d → C)
    (b : Fin i) (w : Fin d → C) (χ : MvPowerSeries (Fin d) C)
    (hχ : ∀ α, coeff α (subst (expOf G) χ) = α.prod fun e n => w e ^ n / (n.factorial : C)) :
    subst (expAlong (fun _ : Fin i => G) (fun _ => u))
        (subst (fun e : Fin d => (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) χ) =
      mvExp (∑ e, w e • ∑ a, u a e • (X (⟨b, a⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) := by
  have hexp := (GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v d G).1
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hexp.1
  have hL : ∀ b' : Fin i, HasSubst (fun e : Fin d => ∑ a, u a e • (X (⟨b', a⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) :=
    fun b' => hasSubst_of_constantCoeff_zero fun e => by simp
  have hEA : HasSubst (expAlong (fun _ : Fin i => G) (fun _ => u)) :=
    hasSubst_of_constantCoeff_zero fun x => constantCoeff_subst_eq_zero (hL x.1) (fun e => by simp) (hexp.1 x.2)
  have hR : HasSubst (fun e : Fin d => (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun e => by simp
  have h1 : subst (expOf G) χ = mvExp (∑ e, w e • (X e : MvPowerSeries (Fin d) C)) := by
    ext α; rw [hχ, coeff_mvExp_lin]
  rw [subst_comp_subst_apply hR hEA]
  have h2 : (fun e : Fin d => subst (expAlong (fun _ : Fin i => G) (fun _ => u))
      (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) =
      fun e => subst (fun e : Fin d => ∑ a, u a e • (X (⟨b, a⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (expOf G e) := by
    funext e; rw [subst_X hEA]; rfl
  rw [h2, ← subst_comp_subst_apply hE (hL b), h1, mvSubst_mvExp (by simp) (hL b)]
  congr 1
  rw [← coe_substAlgHom (hL b), map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul, coe_substAlgHom, subst_X (hL b)]

theorem lin_sum {i d : ℕ} (l : Fin i → Fin d → C) (u : Fin i → Fin d → C) :
    (∑ b, ∑ e, l b e • ∑ a, u a e • (X (⟨b, a⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) =
      ∑ x : (Σ _ : Fin i, Fin i), (∑ e, l x.1 e * u x.2 e) • (X x : MvPowerSeries (Σ _ : Fin i, Fin i) C) := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_smul]

theorem detDepth_le_char : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ)
    (G : LogFGL v d) (u : Fin i → Fin d → C) (l : Fin i → Fin d → C), (∀ b, IsCharLog G (l b)) →
    detDepth G u c ≤ toE (v ((Matrix.det (Matrix.of fun a b => ∑ e, l b e * u a e)) ^ c)) := by
  intro C _ _ v i d c G u l hl
  choose χ hχi hχc using hl
  have hf := isInt_prod_rename v i d χ hχi
  have key : subst (expAlong (fun _ : Fin i => G) (fun _ => u))
      (∏ b, subst (fun e : Fin d =>
        (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (χ b)) =
      Formalism.L2.Th1.C.mvExp (∑ x : (Σ _ : Fin i, Fin i), (∑ e, l x.1 e * u x.2 e) • (X x : MvPowerSeries (Σ _ : Fin i, Fin i) C)) := by
    have hexp := (GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v d G).1
    have hEA : HasSubst (expAlong (fun _ : Fin i => G) (fun _ => u)) :=
      hasSubst_of_constantCoeff_zero fun x => constantCoeff_subst_eq_zero
        (hasSubst_of_constantCoeff_zero fun e => by simp) (fun e => by simp) (hexp.1 x.2)
    rw [← coe_substAlgHom hEA, map_prod, ← lin_sum, Formalism.L2.Th1.C.mvExp_sum _ _ (fun b _ => by simp)]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [coe_substAlgHom, subst_col v G u b (l b) (χ b) (hχc b)]
  unfold detDepth depth
  refine le_trans (iInf_le _ ⟨_, hf⟩) (le_of_eq ?_)
  dsimp only
  rw [key, derivAt0_eq_eval _ _ (fun x : (Σ _ : Fin i, Fin i) => (Matrix.of fun a b => ∑ e, l b e * u a e) x.2 x.1)
    (fun α => by rw [coeff_mvExp_lin]; rfl), eval_detPow]

end

end GlobalTheory.FGDepth.CharBound

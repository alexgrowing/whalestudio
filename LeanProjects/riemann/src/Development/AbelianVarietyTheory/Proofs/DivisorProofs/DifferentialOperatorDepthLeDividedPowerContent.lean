import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EqZeroOrSingleOfDegreeLtTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupExpTwoSidedInverseUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameDualStatement

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth.DepthLeContent

noncomputable section

section Lead

variable {S τ : Type} [CommRing S]

def Near (k n : ℕ) (P Q : MvPowerSeries τ S) : Prop :=
  (n : ℕ∞) ≤ P.order ∧ (n : ℕ∞) ≤ Q.order ∧ ((k + n : ℕ) : ℕ∞) ≤ (P - Q).order + 1

theorem Near.one (k : ℕ) : Near k 0 (1 : MvPowerSeries τ S) 1 := by
  simp [Near]

theorem Near.mul {k n m : ℕ} {P Q P' Q' : MvPowerSeries τ S} (h : Near k n P Q)
    (h' : Near k m P' Q') : Near k (n + m) (P * P') (Q * Q') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · push_cast; exact (add_le_add h1 h1').trans le_order_mul
  · push_cast; exact (add_le_add h2 h2').trans le_order_mul
  · have e : P * P' - Q * Q' = P * (P' - Q') + (P - Q) * Q' := by ring
    rw [e]
    refine le_trans ?_ (add_le_add_left min_order_le_add 1)
    rw [← min_add_add_right]
    refine le_min ?_ ?_
    · refine le_trans ?_ (add_le_add_left le_order_mul 1)
      rw [add_assoc]
      refine le_trans (le_of_eq ?_) (add_le_add h1 h3')
      push_cast; ring
    · refine le_trans ?_ (add_le_add_left le_order_mul 1)
      rw [add_right_comm]
      refine le_trans (le_of_eq ?_) (add_le_add h3 h2')
      push_cast; ring

theorem Near.prod {σ : Type} {k : ℕ} {a b : σ → MvPowerSeries τ S}
    (h : ∀ s, Near k 1 (a s) (b s)) (d : σ →₀ ℕ) :
    Near k d.degree (d.prod fun s e => a s ^ e) (d.prod fun s e => b s ^ e) := by
  induction d using Finsupp.induction_linear with
  | zero => simpa using Near.one k
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
      Finsupp.prod_add_index' (by simp) (by simp [pow_add]), map_add]
    exact hf.mul hg
  | single s n =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp),
      Finsupp.degree_single]
    induction n with
    | zero => simpa using Near.one k
    | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul (h s)

theorem lead_prod (Y : τ → MvPowerSeries τ S) (hY : ∀ s, 2 ≤ (Y s - X s).order) (α : τ →₀ ℕ) :
    ((α.degree + 1 : ℕ) : ℕ∞) ≤ ((α.prod fun s k => Y s ^ k) - monomial α 1).order := by
  classical
  have hc : ∀ s, Near 2 1 (Y s) (X s) := fun s => by
    have hX : (1 : ℕ∞) ≤ (X s : MvPowerSeries τ S).order :=
      one_le_order_iff_constCoeff_eq_zero.mpr (by simp)
    refine ⟨?_, hX, ?_⟩
    · have : Y s = (Y s - X s) + X s := by ring
      rw [this]
      exact le_trans (le_min ((by norm_num : (1 : ℕ∞) ≤ 2).trans (hY s)) hX) min_order_le_add
    · have := add_le_add (hY s) (le_refl (1 : ℕ∞))
      push_cast
      exact this
  have h := (Near.prod hc α).2.2
  have hm : (α.prod fun s e => (X s : MvPowerSeries τ S) ^ e) = monomial α 1 := by
    have := subst_monomial (R := S) (HasSubst.X (S := S) (σ := τ)) α (1 : S)
    rw [subst_self] at this
    simpa using this.symm
  rw [hm] at h
  have h2 : ((α.degree + 1 : ℕ) : ℕ∞) + 1 = ((2 + α.degree : ℕ) : ℕ∞) := by
    push_cast; ring
  exact (ENat.add_le_add_iff_right (by simp)).mp (h2.le.trans h)

end Lead

section Int

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))

theorem isInt_mul {τ : Type} {f g : MvPowerSeries τ C} (hf : MvIsInt v f) (hg : MvIsInt v g) :
    MvIsInt v (f * g) := by
  classical
  intro α
  unfold IsIntV
  rw [coeff_mul]
  refine Finset.sum_induction _ (fun x => 0 ≤ v x)
    (fun a b ha hb => le_trans (le_min ha hb) (v.map_add a b)) (by simp) ?_
  intro p _
  rw [v.map_mul]
  exact add_nonneg (hf _) (hg _)

open Classical in

def intSub (τ : Type) : Subring (MvPowerSeries τ C) where
  carrier := {f | MvIsInt v f}
  mul_mem' := isInt_mul v
  one_mem' := by
    classical
    intro α; unfold IsIntV; rw [coeff_one]; split_ifs <;> simp
  add_mem' := by
    intro f g hf hg α; unfold IsIntV; rw [map_add]
    exact le_trans (le_min (hf α) (hg α)) (v.map_add _ _)
  zero_mem' := by intro α; unfold IsIntV; simp
  neg_mem' := by intro f hf α; unfold IsIntV; rw [map_neg, v.map_neg]; exact hf α

theorem isInt_smul_X {τ : Type} {c : C} (hc : IsIntV v c) (t : τ) :
    MvIsInt v (c • (X t : MvPowerSeries τ C)) := by
  classical
  intro α; unfold IsIntV
  rw [coeff_smul, coeff_X]
  split_ifs
  · rw [mul_one]; exact hc
  · simp

theorem isInt_prod {σ τ : Type} (L : σ → MvPowerSeries τ C) (hL : ∀ s, MvIsInt v (L s))
    (α : σ →₀ ℕ) : MvIsInt v (α.prod fun s k => L s ^ k) := by
  classical
  show _ ∈ intSub v τ
  unfold Finsupp.prod
  exact prod_mem fun s _ => pow_mem (hL s) _

end Int

theorem coeff_single_exp {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
    (G : LogFGL v d) {ex : Fin d → MvPowerSeries (Fin d) C} (h : IsExp G ex) (a b : Fin d) :
    coeff (Finsupp.single b 1) (ex a) = if a = b then 1 else 0 := by
  have e := congrArg (coeff (Finsupp.single b 1)) (h.2 a)
  rw [GlobalTheory.FormalSeries.coeff_single_subst h.1] at e
  simp only [G.lg_lin, smul_eq_mul, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, coeff_X] at e
  rw [e]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Finsupp.single_left_inj one_ne_zero, Ne.symm hab]

theorem depth_le_content : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (κ : Type) [Fintype κ] [DecidableEq κ] (d n : κ → ℕ) (G : ∀ b, LogFGL v (d b))
    (u : ∀ b, Fin (n b) → Fin (d b) → C) (P : MvPolynomial (Σ b, Fin (n b)) C) (D : ℕ),
    P.IsHomogeneous D → (∀ b, IsSatFrame v (u b)) →
      depth G (ι := fun b => Fin (n b)) u P ≤ content v P := by
  intro C _ _ v κ _ _ d n G u P D hP hu
  classical
  choose l hlint hldual using fun b => GlobalTheory.T.exists_integral_dual_frame_of_isSatFrame C v (n b) (d b) (u b) (hu b)
  have hexp : ∀ b, IsExp (G b) (expOf (G b)) := fun b => (GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v (d b) (G b)).1
  have hlin0 : ∀ b (e : Fin (d b)), constantCoeff
      (∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, Fin (n b)) C)) = 0 := by
    intro b e; simp
  have hlin1 : ∀ b (e : Fin (d b)) (y : Σ b, Fin (n b)), coeff (Finsupp.single y 1)
      (∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, Fin (n b)) C)) =
        ∑ a, u b a e * if y = ⟨b, a⟩ then 1 else 0 := by
    intro b e y
    simp only [map_sum, coeff_smul, coeff_X, Finsupp.single_left_inj one_ne_zero, smul_eq_mul]
  set A := expAlong G u with hAdef
  have hA0 : ∀ x, constantCoeff (A x) = 0 := fun x =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (hlin0 x.1)) (hlin0 x.1)
      ((hexp x.1).1 x.2)
  have hA1 : ∀ x y, coeff (Finsupp.single y 1) (A x) =
      ∑ a, u x.1 a x.2 * if y = ⟨x.1, a⟩ then 1 else 0 := by
    intro x y
    show coeff (Finsupp.single y 1) (subst _ (expOf (G x.1) x.2)) = _
    rw [GlobalTheory.FormalSeries.coeff_single_subst (hlin0 x.1)]
    simp only [coeff_single_exp (G x.1) (hexp x.1), hlin1, smul_eq_mul, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  set Y : (Σ b, Fin (n b)) → MvPowerSeries (Σ b, Fin (n b)) C :=
    fun y => ∑ e, l y.1 y.2 e • A ⟨y.1, e⟩ with hYdef
  have hY : ∀ y, 2 ≤ (Y y - X y).order := by
    intro y
    rw [GlobalTheory.FormalSeries.two_le_order_iff]
    refine ⟨by simp [hYdef, hA0], fun z => ?_⟩
    rw [map_sub, hYdef]
    simp only [map_sum, coeff_smul, hA1, smul_eq_mul, coeff_X,
      Finsupp.single_left_inj one_ne_zero]
    simp_rw [Finset.mul_sum]
    rw [sub_eq_zero]
    have key : ∀ a : Fin (n y.1), ∑ e, l y.1 y.2 e * (u y.1 a e * if z = ⟨y.1, a⟩ then (1 : C) else 0)
        = (if y.2 = a then 1 else 0) * if z = ⟨y.1, a⟩ then 1 else 0 := by
      intro a
      rw [← hldual y.1 y.2 a, Finset.sum_mul]
      exact Finset.sum_congr rfl fun e _ => by ring
    have key2 : ∑ e : Fin (d y.1), ∑ a : Fin (n y.1),
        l y.1 y.2 e * (u y.1 a e * if z = ⟨y.1, a⟩ then (1 : C) else 0) = if z = y then 1 else 0 := by
      rw [Finset.sum_comm]
      simp_rw [key, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact key2
  have hAs : HasSubst A := hasSubst_of_constantCoeff_zero hA0
  unfold content
  refine le_iInf₂ fun α hα => ?_
  set L : (Σ b, Fin (n b)) → MvPowerSeries (Σ b, Fin (d b)) C :=
    fun y => ∑ e, l y.1 y.2 e • X ⟨y.1, e⟩ with hLdef
  have hLint : ∀ y, MvIsInt v (L y) := fun y =>
    (intSub v _).sum_mem fun e _ => isInt_smul_X v (hlint y.1 y.2 e) _
  set f := α.prod fun y k => L y ^ k with hfdef
  have hfint : MvIsInt v f := isInt_prod v L hLint α
  have hsub : subst A f = α.prod fun y k => Y y ^ k := by
    rw [hfdef, ← coe_substAlgHom hAs, map_finsuppProd]
    simp only [map_pow, hLdef, hYdef, map_sum, map_smul, substAlgHom_X]
  have hord := lead_prod Y hY α
  rw [← hsub] at hord
  have hdeg : ∀ β ∈ P.support, β.degree = D := fun β hβ => by
    have := hP (MvPolynomial.mem_support_iff.mp hβ)
    rw [← this, Finsupp.degree_eq_weight_one]; rfl
  have hval : derivAt0 P (subst A f) = P.coeff α * mfact α := by
    unfold derivAt0
    rw [Finset.sum_eq_single α]
    · rw [GlobalTheory.FormalSeries.coeff_eq_of_le_order_sub hord (Nat.lt_succ_self _),
        coeff_monomial_same, mul_one]
    · intro β hβ hne
      rw [GlobalTheory.FormalSeries.coeff_eq_of_le_order_sub hord
        (by rw [hdeg β hβ, ← hdeg α hα]; exact Nat.lt_succ_self _), coeff_monomial,
        if_neg hne, mul_zero]
    · intro h; exact absurd hα h
  unfold depth
  refine (iInf_le _ ⟨f, hfint⟩).trans (le_of_eq ?_)
  rw [← hAdef, hval]

end

end GlobalTheory.FGDepth.DepthLeContent

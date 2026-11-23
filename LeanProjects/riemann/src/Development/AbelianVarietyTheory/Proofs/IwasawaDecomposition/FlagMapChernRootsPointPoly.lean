import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchubGamApply
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.SchubertPoint

theorem sign_revPerm_real (n : ℕ) :
    ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : ℝ) = (-1) ^ (∑ i : Fin n, (i : ℕ)) := by
  induction n with
  | zero =>
    rw [Subsingleton.elim (Fin.revPerm : Equiv.Perm (Fin 0)) 1]; simp
  | succ n ih =>
    have key : finRotate (n + 1) * (Fin.revPerm : Equiv.Perm (Fin (n + 1))) =
        Equiv.Perm.decomposeFin.symm (0, (Fin.revPerm : Equiv.Perm (Fin n))) := by
      ext i
      cases i using Fin.cases with
      | zero => simp
      | succ j =>
        simp [Equiv.Perm.decomposeFin_symm_apply_succ, Fin.rev_succ]
    have hs := congrArg Equiv.Perm.sign key
    rw [Equiv.Perm.sign_mul, sign_finRotate, Equiv.Perm.decomposeFin.symm_sign] at hs
    simp only [if_true, one_mul, Nat.add_sub_cancel] at hs
    rw [Fin.sum_univ_castSucc, pow_add]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [← ih]
    have : Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (n + 1))) =
        (-1) ^ n * Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) := by
      rw [← hs, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
    rw [this]; push_cast; ring

theorem esymm_self (n : ℕ) : esymm (Fin n) ℝ n = ∏ i : Fin n, X i := by
  have h : Finset.powersetCard n (Finset.univ : Finset (Fin n)) = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  rw [esymm, h]
  simp

def revTail (p q : ℕ) : Equiv.Perm (Fin (p + q)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr 1 Fin.revPerm)

theorem revTail_castAdd (p q : ℕ) (i : Fin p) : revTail p q (Fin.castAdd q i) = Fin.castAdd q i := by
  simp [revTail, Equiv.permCongr_apply]

theorem revTail_natAdd (p q : ℕ) (j : Fin q) : revTail p q (Fin.natAdd p j) = Fin.natAdd p (Fin.rev j) := by
  simp [revTail, Equiv.permCongr_apply]

theorem sign_revTail (p q : ℕ) :
    ((Equiv.Perm.sign (revTail p q) : ℤ) : ℝ) = (-1) ^ (∑ j : Fin q, (j : ℕ)) := by
  rw [revTail, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_one, one_mul]
  exact sign_revPerm_real q

theorem sum_tail (q : ℕ) : ∑ j : Fin q, (q - 1 - (j : ℕ)) = ∑ j : Fin q, (j : ℕ) := by
  refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
  simp [Fin.val_rev]; omega

def tailSgn (p q : ℕ) (k : Fin (p + q)) : ℝ := if (k : ℕ) < p then (-1) ^ (p + q - 1 - (k : ℕ)) else 1

theorem schubPoint_eq (ι : Type) [Fintype ι] [DecidableEq ι] (p q : ℕ) :
    (∏ τ : ι, ((∏ i : Fin p, (-X (τ, Fin.castAdd q i) : MvPolynomial (ι × Fin (p + q)) ℝ) ^ (p + q - 1 - (i : ℕ))) *
      ∏ j : Fin q, X (τ, Fin.natAdd p j) ^ (j : ℕ))) =
    C (∏ x : ι × Fin (p + q), tailSgn p q x.2) * monomial (Formalism.DegreeFormula.permExp (fun _ : ι => revTail p q)) 1 := by
  have h : C (∏ x : ι × Fin (p + q), tailSgn p q x.2) * monomial (Formalism.DegreeFormula.permExp (fun _ : ι => revTail p q)) 1 =
      ∏ x : ι × Fin (p + q), (C (tailSgn p q x.2) * X x ^ (Formalism.DegreeFormula.permExp (fun _ : ι => revTail p q) x)) := by
    rw [Finset.prod_mul_distrib, ← map_prod, monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by intro i; simp)]
  rw [h, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [tailSgn, Formalism.DegreeFormula.permExp, revTail_castAdd, Finsupp.equivFunOnFinite_symm_apply_apply,
      Fin.coe_castAdd]
    rw [if_pos i.2, neg_pow, map_pow, map_neg, map_one]
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp only [tailSgn, Formalism.DegreeFormula.permExp, revTail_natAdd, Finsupp.equivFunOnFinite_symm_apply_apply,
      Fin.coe_natAdd, Fin.val_rev]
    rw [if_neg (by omega), C_1, one_mul]
    congr 1
    omega

theorem degFl_schubPoint (ι : Type) [Fintype ι] [DecidableEq ι] (p q : ℕ) :
    Formalism.DegreeFormula.degFl ι (p + q) (∏ τ : ι, ((∏ i : Fin p, (-X (τ, Fin.castAdd q i) : MvPolynomial (ι × Fin (p + q)) ℝ) ^
      (p + q - 1 - (i : ℕ))) * ∏ j : Fin q, X (τ, Fin.natAdd p j) ^ (j : ℕ))) = 1 := by
  rw [schubPoint_eq]
  unfold Formalism.DegreeFormula.degFl
  rw [Finset.sum_eq_single (fun _ => revTail p q)]
  · rw [coeff_C_mul, coeff_monomial, if_pos rfl, mul_one]
    have hA : ∏ x : ι × Fin (p + q), tailSgn p q x.2 =
        ((-1 : ℝ) ^ (∑ i : Fin p, (p + q - 1 - (i : ℕ)))) ^ Fintype.card ι := by
      rw [Fintype.prod_prod_type]
      dsimp only
      rw [Finset.prod_const, Finset.card_univ]
      congr 1
      rw [Fin.prod_univ_add]
      simp [tailSgn, Finset.prod_pow_eq_pow_sum]
    have hB : ∏ τ : ι, ((Equiv.Perm.sign ((fun _ : ι => revTail p q) τ) : ℤ) : ℝ) =
        ((-1 : ℝ) ^ (∑ j : Fin q, (j : ℕ))) ^ Fintype.card ι := by
      rw [Finset.prod_const, sign_revTail, Finset.card_univ]
    have hD : Formalism.DegreeFormula.dimFl ι (p + q) =
        Fintype.card ι * ((∑ i : Fin p, (p + q - 1 - (i : ℕ))) + ∑ j : Fin q, (j : ℕ)) := by
      unfold Formalism.DegreeFormula.dimFl
      congr 1
      rw [← Formalism.DegreeFormula.PermutationPointDegree.sum_delta, Fin.sum_univ_add, ← sum_tail]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Fin.coe_natAdd]; omega
    have e : ∀ a b c : ℕ, (-1 : ℝ) ^ (c * (a + b)) * (((-1) ^ b) ^ c * ((-1) ^ a) ^ c) = 1 := by
      intro a b c
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      exact Even.neg_one_pow ⟨c * (a + b), by ring⟩
    rw [hA, hB, hD]
    exact e _ _ _
  · intro σ _ hσ
    rw [coeff_C_mul, coeff_monomial, if_neg, mul_zero, mul_zero]
    intro h
    exact hσ (Formalism.DegreeFormula.PermutationPointDegree.permExp_inj _ _ h).symm
  · simp

section Host

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def conjOff (H : Host E) : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} ≃ GlobalTheory.AllWt.Psi H where
  toFun τ := ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩
  invFun τ := ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
  left_inv τ := Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1)
  right_inv τ := Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1)

theorem flagMap_chernRoots_pointPoly {H : Host E} (Dw : Datum H) :
    GlobalTheory.Schubert.flagMap Dw (GlobalTheory.GoodMetric.chernRoots Dw.mult (GlobalTheory.LieBase.pointPoly H Dw)) =
      ∏ τ : GlobalTheory.AllWt.Psi H, (∏ i : Fin Dw.p, (-X (τ, Fin.castAdd Dw.q i))) ^ Dw.q := by
  rw [GlobalTheory.LieBase.pointPoly, map_prod, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.PointChern.mult_of_mem Dw τ.2
  have he : Dw.p + Dw.q - Dw.mult τ.1 = Dw.q := by omega
  rw [he, map_pow, map_pow]
  congr 1
  simp only [map_mul, GlobalTheory.GoodMetric.chernRoots, GlobalTheory.Schubert.flagMap, aeval_C, aeval_X, algebraMap_eq,
    esymm_self, map_prod, rename_X]
  have h1 : ∀ i : Fin (Dw.mult τ.1), GlobalTheory.Schubert.flagRoot Dw ⟨τ.1, i⟩ =
      X (τ, Fin.castAdd Dw.q (finCongr hm i)) := by
    intro i
    rw [GlobalTheory.Schubert.flagRoot, dif_pos τ.2]
    rfl
  simp only [h1]
  have h2 : (∏ i : Fin (Dw.mult τ.1), (-X (τ, Fin.castAdd Dw.q (finCongr hm i)) : MvPolynomial _ ℝ)) =
      C ((-1 : ℝ) ^ Dw.mult τ.1) * ∏ i : Fin (Dw.mult τ.1), X (τ, Fin.castAdd Dw.q (finCongr hm i)) := by
    simp only [← neg_one_mul (X _ : MvPolynomial _ ℝ), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, map_pow, map_neg, map_one]
  rw [← h2]
  exact Fintype.prod_equiv (finCongr hm) _ _ fun i => rfl

theorem flagMap_fibrePoint {H : Host E} (Dw : Datum H) :
    GlobalTheory.Schubert.flagMap Dw (GlobalTheory.GoodMetric.fibrePoint Dw.mult) =
      (∏ τ : GlobalTheory.AllWt.Psi H, ∏ i : Fin Dw.p, (-X (τ, Fin.castAdd Dw.q i)) ^ (Dw.p - 1 - (i : ℕ))) *
        ∏ τ : GlobalTheory.AllWt.Psi H, ∏ j : Fin Dw.q, X (τ, Fin.natAdd Dw.p j) ^ (j : ℕ) := by
  rw [GlobalTheory.GoodMetric.fibrePoint, map_prod]
  simp only [map_pow, map_neg, GlobalTheory.Schubert.flagMap, aeval_X]
  rw [Fintype.prod_sigma, ← Fintype.prod_subtype_mul_prod_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.PointChern.mult_of_mem Dw τ.2
    refine Fintype.prod_equiv (finCongr hm) _ _ fun i => ?_
    rw [GlobalTheory.Schubert.flagRoot, dif_pos τ.2]
    congr 1
    simp only [finCongr_apply, Fin.coe_cast]
    omega
  · refine Fintype.prod_equiv (conjOff H) _ _ fun τ => ?_
    have hm : Dw.mult τ.1 = Dw.q := GlobalTheory.PointChern.mult_of_not_mem Dw τ.2
    refine Fintype.prod_equiv ((finCongr hm).trans Fin.revPerm) _ _ fun i => ?_
    rw [GlobalTheory.Schubert.flagRoot, dif_neg τ.2, neg_neg]
    have hi : (i : ℕ) < Dw.q := hm ▸ i.2
    congr 1
    · congr 1
      refine Prod.ext rfl (Fin.ext ?_)
      simp [Fin.val_rev]
      omega
    · simp [Fin.val_rev]
      omega

end Host

theorem schubGam_pointPoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H),
    GlobalTheory.Schubert.schubGam Dw (GlobalTheory.LieBase.pointPoly H Dw) = 1 := by
  intro E _ _ _ H Dw
  rw [GlobalTheory.Schubert.schubGam_apply, map_mul, flagMap_chernRoots_pointPoly, flagMap_fibrePoint]
  have h : (∏ τ : GlobalTheory.AllWt.Psi H, (∏ i : Fin Dw.p, (-X (τ, Fin.castAdd Dw.q i) : MvPolynomial _ ℝ)) ^ Dw.q) *
      ((∏ τ : GlobalTheory.AllWt.Psi H, ∏ i : Fin Dw.p, (-X (τ, Fin.castAdd Dw.q i)) ^ (Dw.p - 1 - (i : ℕ))) *
        ∏ τ : GlobalTheory.AllWt.Psi H, ∏ j : Fin Dw.q, X (τ, Fin.natAdd Dw.p j) ^ (j : ℕ)) =
      ∏ τ : GlobalTheory.AllWt.Psi H, ((∏ i : Fin Dw.p, (-X (τ, Fin.castAdd Dw.q i)) ^ (Dw.p + Dw.q - 1 - (i : ℕ))) *
        ∏ j : Fin Dw.q, X (τ, Fin.natAdd Dw.p j) ^ (j : ℕ)) := by
    rw [← mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add]
    congr 1
    have := i.2
    omega
  rw [h]
  exact degFl_schubPoint _ _ _

end GlobalTheory.SchubertPoint

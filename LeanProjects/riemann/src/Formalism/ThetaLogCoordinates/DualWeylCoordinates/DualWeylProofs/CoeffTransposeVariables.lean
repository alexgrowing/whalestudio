import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.TransposeVariables
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQHW

open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

theorem qn_coeff_X_pderiv {σ : Type*} (i : σ) (f : MvPolynomial σ ℚ) (m : σ →₀ ℕ) :
    coeff m (X i * pderiv i f) = (m i : ℚ) * coeff m f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial s c =>
    have h : X i * pderiv i (monomial s c) = (s i : ℚ) • monomial s c := by
      rw [pderiv_monomial]
      by_cases hs : s i = 0
      · simp [hs]
      · have h1 : Finsupp.single i 1 + (s - Finsupp.single i 1) = s :=
          add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hs))
        rw [X, monomial_mul, h1, smul_monomial, one_mul, smul_eq_mul, mul_comm]
    rw [h, coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with hsm
    · rw [hsm]
    · simp
  | add p q hp hq => rw [map_add, mul_add, coeff_add, coeff_add, hp, hq, mul_add]

def qn_wt {n : ℕ} (m : Fin n × Fin n →₀ ℕ) : Fin n → ℤ := fun a => ((∑ l : Fin n, m (l, a) : ℕ) : ℤ)

theorem qn_coeff_E (n : ℕ) (a : Fin n) (f : MvPolynomial (Fin n × Fin n) ℚ) (m : Fin n × Fin n →₀ ℕ) :
    coeff m (glOps ℚ n (rowLetters n) Set.univ a a f) = (qn_wt m a : ℚ) * coeff m f := by
  rw [qn_E_eq, qn_D_apply, coeff_sum]
  simp only [qn_coeff_X_pderiv]
  rw [← Finset.sum_mul]
  simp [qn_wt]

theorem qn_mem_weightSp (n : ℕ) (w : Fin n → ℤ) (z : MvPolynomial (Fin n × Fin n) ℚ) :
    z ∈ weightSp (glOps ℚ n (rowLetters n) Set.univ) w ↔
      ∀ a, glOps ℚ n (rowLetters n) Set.univ a a z = (w a : ℚ) • z := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]

theorem qn_monomial_mem (n : ℕ) (m : Fin n × Fin n →₀ ℕ) (c : ℚ) :
    monomial m c ∈ weightSp (glOps ℚ n (rowLetters n) Set.univ) (qn_wt m) := by
  classical
  rw [qn_mem_weightSp]
  intro a
  ext m'
  rw [qn_coeff_E, coeff_smul, coeff_monomial, smul_eq_mul]
  split_ifs with h
  · rw [h]
  · simp

theorem qn_weightSp_coeff (n : ℕ) (w : Fin n → ℤ) (z : MvPolynomial (Fin n × Fin n) ℚ)
    (hz : z ∈ weightSp (glOps ℚ n (rowLetters n) Set.univ) w) (m : Fin n × Fin n →₀ ℕ) (hm : qn_wt m ≠ w) :
    coeff m z = 0 := by
  rw [qn_mem_weightSp] at hz
  by_contra hne
  apply hm
  funext a
  have h := congrArg (coeff m) (hz a)
  rw [qn_coeff_E, coeff_smul, smul_eq_mul] at h
  have := mul_right_cancel₀ hne h
  exact_mod_cast this

theorem qn_otherWts_coeff (n : ℕ) (lam : Fin n → ℤ) (z : MvPolynomial (Fin n × Fin n) ℚ)
    (hz : z ∈ otherWts (glOps ℚ n (rowLetters n) Set.univ) lam) (m : Fin n × Fin n →₀ ℕ) (hm : qn_wt m = lam) :
    coeff m z = 0 := by
  have hle : otherWts (glOps ℚ n (rowLetters n) Set.univ) lam ≤ LinearMap.ker (lcoeff ℚ m) := by
    unfold otherWts
    refine iSup₂_le fun mu hmu => ?_
    intro y hy
    rw [LinearMap.mem_ker, lcoeff_apply]
    exact qn_weightSp_coeff n mu y hy m (by rw [hm]; exact fun h => hmu h.symm)
  have := hle hz
  rwa [LinearMap.mem_ker, lcoeff_apply] at this

theorem qn_mem_otherWts (n : ℕ) (lam : Fin n → ℤ) (g : MvPolynomial (Fin n × Fin n) ℚ)
    (hg : ∀ m ∈ g.support, qn_wt m ≠ lam) : g ∈ otherWts (glOps ℚ n (rowLetters n) Set.univ) lam := by
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  unfold otherWts
  exact Submodule.mem_iSup_of_mem (qn_wt m) (Submodule.mem_iSup_of_mem (hg m hm) (qn_monomial_mem n m _))

theorem qn_swap_apply {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (a l : Fin n) :
    (Finsupp.mapDomain Prod.swap m) (a, l) = m (l, a) :=
  Finsupp.mapDomain_apply Prod.swap_injective m (l, a)

theorem coeff_transposeVariables (n : ℕ) (g : MvPolynomial (Fin n × Fin n) ℚ) (m : Fin n × Fin n →₀ ℕ) :
    coeff (Finsupp.mapDomain Prod.swap m) (transposeVariables ℚ n g) = coeff m g :=
  coeff_rename_mapDomain Prod.swap Prod.swap_injective g m

theorem qn_mem_otherWts' (n : ℕ) (ν : Fin n → ℕ) (g : MvPolynomial (Fin n × Fin n) ℚ)
    (hg : weightedHomogeneousComponent (rowW n n) ν (transposeVariables ℚ n g) = 0) :
    g ∈ otherWts (glOps ℚ n (rowLetters n) Set.univ) (fun a => (ν a : ℤ)) := by
  classical
  refine qn_mem_otherWts n _ g fun m hm hwt => ?_
  have h1 := congrArg (coeff (Finsupp.mapDomain Prod.swap m)) hg
  have hw : Finsupp.weight (rowW n n) (Finsupp.mapDomain Prod.swap m) = ν := by
    funext a
    rw [lehw_weight_rowW, rowDeg]
    simp only [qn_swap_apply]
    have := congrFun hwt a
    simp only [qn_wt] at this
    exact_mod_cast this
  rw [coeff_weightedHomogeneousComponent, if_pos hw, coeff_transposeVariables, coeff_zero] at h1
  exact (mem_support_iff.mp hm) h1

theorem qn_otherWts_coeff' (n : ℕ) (ν : Fin n → ℕ) (z : MvPolynomial (Fin n × Fin n) ℚ)
    (hz : z ∈ otherWts (glOps ℚ n (rowLetters n) Set.univ) (fun a => (ν a : ℤ))) :
    coeff (lhwline_mnu (le_refl n) ν) (transposeVariables ℚ n z) = 0 := by
  classical
  have h := coeff_transposeVariables n (transposeVariables ℚ n z) (lhwline_mnu (le_refl n) ν)
  rw [transposeVariables_involutive] at h
  rw [← h]
  refine qn_otherWts_coeff n _ z hz _ ?_
  funext a
  simp only [qn_wt, qn_swap_apply, lhwline_mnu_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    have : a.val ≠ b.val := fun h => hb (Fin.ext h).symm
    simp [this]
  · simp

theorem qn_rowNu (n : ℕ) (ν : Fin n → ℕ) : rowNu (r := n) ν = ν := by
  funext a
  simp [rowNu]

theorem qn_eval_eq_coeff (n : ℕ) (ν : Fin n → ℕ) (F : MvPolynomial (Fin n × Fin n) ℚ)
    (hF : IsWeightedHomogeneous (colW n n) F ν) :
    eval (idFrame ℚ n n) F = coeff (lhwline_mnu (le_refl n) ν) F := by
  have hD : ∀ (a : Fin n) (j : Fin n), a.val ≠ j.val → idFrame ℚ n n (a, j) = 0 := by
    intro a j h
    simp [idFrame, h]
  rw [lhwline_diag (le_refl n) ν F hF (idFrame ℚ n n) hD]
  have : ∏ v, idFrame ℚ n n v ^ (lhwline_mnu (le_refl n) ν) v = 1 := by
    refine Finset.prod_eq_one fun v _ => ?_
    obtain ⟨a, j⟩ := v
    rw [lhwline_mnu_apply]
    by_cases h : a.val = j.val
    · simp [idFrame, h]
    · simp [h]
  rw [this, mul_one]

theorem qn_colHom (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ) (F : MvPolynomial (Fin n × Fin n) R)
    (hF : F ∈ dualWeyl R n n ν) : IsWeightedHomogeneous (colW n n) F ν :=
  (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hF).1

theorem qn_comp (n : ℕ) (ν : Fin n → ℕ) (hν : Antitone ν) (F : MvPolynomial (Fin n × Fin n) ℚ)
    (hF : F ∈ dualWeyl ℚ n n ν) :
    weightedHomogeneousComponent (rowW n n) ν F = eval (idFrame ℚ n n) F • hw ℚ (le_refl n) ν := by
  classical
  set G := weightedHomogeneousComponent (rowW n n) ν F with hGdef
  have hG : G ∈ dualWeyl ℚ n n ν := dualWeylRowGraded ℚ n n ν _ F hF
  have hGh : IsWeightedHomogeneous (rowW n n) G (rowNu (r := n) ν) := by
    rw [qn_rowNu]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  obtain ⟨c, hc⟩ := hwLine ℚ n n (le_refl n) ν hν G hG
    (fun a b hab k hk => lehw_kill (le_refl n) ν hν G hG hGh a b hab k hk)
  have hHW := hwRowWeight ℚ n n (le_refl n) ν hν
  rw [qn_rowNu] at hHW
  have hH1 : coeff (lhwline_mnu (le_refl n) ν) (hw ℚ (le_refl n) ν) = 1 := by
    rw [← qn_eval_eq_coeff n ν _ (qn_colHom ℚ n ν _ (hwMem ℚ n n (le_refl n) ν hν))]
    exact lehw_eval_idFrame_hw (le_refl n) ν
  have hwt : Finsupp.weight (rowW n n) (lhwline_mnu (le_refl n) ν) = ν :=
    hHW (by rw [hH1]; exact one_ne_zero)
  have h1 : coeff (lhwline_mnu (le_refl n) ν) F = c := by
    have e : coeff (lhwline_mnu (le_refl n) ν) F = coeff (lhwline_mnu (le_refl n) ν) G := by
      rw [hGdef, coeff_weightedHomogeneousComponent, if_pos hwt]
    rw [e, hc, coeff_smul, hH1, smul_eq_mul, mul_one]
  rw [qn_eval_eq_coeff n ν F (qn_colHom ℚ n ν F hF), h1, hc]

end Formalism.InvariantFactorPaths.ColumnFamilies

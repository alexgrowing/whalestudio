import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.SameSign

noncomputable section

open MvPolynomial

namespace FockRL

variable {p q r s : ℕ}

theorem omAct_eq_sum (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) :
    FockH1Action.omAct p q r s M = ∑ l, ∑ l', M l l' • FockH1Action.omE l l' := by
  first
  | (simp only [FockH1Action.omAct, LinearMap.coeFn_sum, Finset.sum_apply,
      LinearMap.smulRight_apply, Matrix.entryLinearMap_apply]; done)
  | (simp only [FockH1Action.omAct, LinearMap.sum_apply,
      LinearMap.smulRight_apply, Matrix.entryLinearMap_apply]; done)

theorem omE_apply (l l' : FockH1Action.Ln p q r s) (P : FockH1Action.Pol p q r s) :
    FockH1Action.omE l l' P = FockH1Action.raiB l (FockH1Action.lowB l' P) + if l = l' then (1 / 2 : ℂ) • P else 0 := by
  simp only [FockH1Action.omE]
  split_ifs <;> rfl

private theorem raiB_apply_of_linePos_eq_true {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = true) (P : FockH1Action.Pol p q r s) :
    FockH1Action.raiB l P = X l * P := by
  first
  | (rw [FockH1Action.raiB, if_pos h]; done)
  | (rw [FockH1Action.raiB, if_pos h]; rfl)

private theorem lowB_apply_of_linePos_eq_false {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = false) (P : FockH1Action.Pol p q r s) :
    FockH1Action.lowB l P = X l * P := by
  have h' : ¬ (FockH1Action.linePos l = true) := by simp [h]
  first
  | (rw [FockH1Action.lowB, if_neg h']; done)
  | (rw [FockH1Action.lowB, if_neg h']; rfl)

theorem omE_pos_neg {l l' : FockH1Action.Ln p q r s} (h1 : FockH1Action.linePos l = true)
    (h2 : FockH1Action.linePos l' = false) (P : FockH1Action.Pol p q r s) :
    FockH1Action.omE l l' P = X l * (X l' * P) := by
  have hne : l ≠ l' := by
    rintro rfl
    simp_all
  rw [omE_apply, if_neg hne, add_zero, lowB_apply_of_linePos_eq_false h2, raiB_apply_of_linePos_eq_true h1]

private theorem raiB_apply_of_linePos_eq_false {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = false) (P : FockH1Action.Pol p q r s) :
    FockH1Action.raiB l P = -(pderiv l P) := by
  have h' : ¬ (FockH1Action.linePos l = true) := by simp [h]
  first
  | (rw [FockH1Action.raiB, if_neg h']; done)
  | (rw [FockH1Action.raiB, if_neg h']; rfl)

private theorem lowB_apply_of_linePos_eq_true {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = true) (P : FockH1Action.Pol p q r s) :
    FockH1Action.lowB l P = pderiv l P := by
  first
  | (rw [FockH1Action.lowB, if_pos h]; done)
  | (rw [FockH1Action.lowB, if_pos h]; rfl)

theorem omE_neg_pos {l l' : FockH1Action.Ln p q r s} (h1 : FockH1Action.linePos l = false)
    (h2 : FockH1Action.linePos l' = true) (P : FockH1Action.Pol p q r s) :
    FockH1Action.omE l l' P = -(pderiv l (pderiv l' P)) := by
  have hne : l ≠ l' := by
    rintro rfl
    simp_all
  rw [omE_apply, if_neg hne, add_zero, lowB_apply_of_linePos_eq_true h2, raiB_apply_of_linePos_eq_false h1]

private theorem mem_homog_iff_isHomogeneous' {σ : Type} {d : ℕ} {P : MvPolynomial σ ℂ} :
    P ∈ FockH1Action.homog σ d ↔ P.IsHomogeneous d := by
  exact mem_homogeneousSubmodule d P

private theorem isHomogeneous_X_complex {σ : Type} (l : σ) : (X l : MvPolynomial σ ℂ).IsHomogeneous 1 := by
  exact isHomogeneous_X ℂ l

private theorem exists_forall_isHomogeneous_monomial {σ : Type} (u : σ →₀ ℕ) :
    ∃ k : ℕ, ∀ c : ℂ, (monomial u c).IsHomogeneous k := by
  exact ⟨_, fun c => isHomogeneous_monomial c rfl⟩

private theorem homogeneousComponent_eq_ite_of_isHomogeneous {σ : Type} {m n : ℕ} {P : MvPolynomial σ ℂ}
    (h : P.IsHomogeneous m) : homogeneousComponent n P = if m = n then P else 0 := by
  have h' : P ∈ homogeneousSubmodule σ ℂ m := mem_homog_iff_isHomogeneous'.mpr h
  first
  | exact homogeneousComponent_of_mem h'
  | exact homogeneousComponent_homogeneous_polynomial m n P h'
  | (by_cases hmn : m = n
     · subst hmn
       rw [if_pos rfl]
       ext d
       rw [coeff_homogeneousComponent]
       split_ifs with hd
       · rfl
       · exact (h.coeff_eq_zero hd).symm
     · rw [if_neg hmn]
       ext d
       rw [coeff_homogeneousComponent, coeff_zero]
       split_ifs with hd
       · exact h.coeff_eq_zero (by omega)
       · rfl)

private theorem homogeneousComponent_pderiv_monomial {σ : Type} (l : σ) (e : ℕ) (u : σ →₀ ℕ) (a : ℂ) :
    homogeneousComponent e (pderiv l (monomial u a)) =
      pderiv l (homogeneousComponent (e + 1) (monomial u a)) := by
  by_cases hu : u l = 0
  · obtain ⟨k, hk⟩ := exists_forall_isHomogeneous_monomial u
    have h0 : pderiv l (monomial u a) = 0 := by
      rw [pderiv_monomial, hu]
      simp
    rw [h0, map_zero, homogeneousComponent_eq_ite_of_isHomogeneous (hk a)]
    split_ifs
    · exact h0.symm
    · exact (map_zero _).symm
  · obtain ⟨k, hk⟩ := exists_forall_isHomogeneous_monomial (u - Finsupp.single l 1)
    have huv : u - Finsupp.single l 1 + Finsupp.single l 1 = u := by
      exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hu))
    have hmul : monomial u a = monomial (u - Finsupp.single l 1) a * X l := by
      rw [X, monomial_mul, huv, mul_one]
    have hu' : (monomial u a).IsHomogeneous (k + 1) := by
      rw [hmul]
      exact (hk a).mul (isHomogeneous_X_complex l)
    rw [pderiv_monomial, homogeneousComponent_eq_ite_of_isHomogeneous (hk _), homogeneousComponent_eq_ite_of_isHomogeneous hu']
    by_cases hke : k = e
    · subst hke
      rw [if_pos rfl, if_pos rfl, pderiv_monomial]
    · rw [if_neg hke, if_neg (show ¬ (k + 1 = e + 1) by omega), map_zero]

private theorem homogeneousComponent_pderiv {σ : Type} (l : σ) (e : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent e (pderiv l P) = pderiv l (homogeneousComponent (e + 1) P) := by
  rw [P.as_sum]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun u _ => homogeneousComponent_pderiv_monomial l e u _

theorem pderiv_homog_zero {σ : Type} (l : σ) {P : MvPolynomial σ ℂ} (h : P.IsHomogeneous 0) :
    pderiv l P = 0 := by
  rw [← sum_homogeneousComponent (pderiv l P)]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [homogeneousComponent_pderiv, homogeneousComponent_eq_ite_of_isHomogeneous h,
    if_neg (show ¬ (0 = e + 1) by omega), map_zero]

private theorem isHomogeneous_zero_complex {σ : Type} (n : ℕ) : (0 : MvPolynomial σ ℂ).IsHomogeneous n :=
  mem_homog_iff_isHomogeneous'.mp (Submodule.zero_mem _)

private theorem isHomogeneous_pderiv_of_isHomogeneous_succ {σ : Type} (l : σ) {n : ℕ} {P : MvPolynomial σ ℂ}
    (h : P.IsHomogeneous (n + 1)) : (pderiv l P).IsHomogeneous n := by
  have hP : homogeneousComponent (n + 1) P = P := by
    rw [homogeneousComponent_eq_ite_of_isHomogeneous h, if_pos rfl]
  rw [← hP, ← homogeneousComponent_pderiv]
  exact homogeneousComponent_isHomogeneous _ _

theorem X_mul_pderiv_homog {σ : Type} (l l' : σ) {d : ℕ} {P : MvPolynomial σ ℂ}
    (h : P.IsHomogeneous d) : (X l * pderiv l' P).IsHomogeneous d := by
  cases d with
  | zero =>
    rw [pderiv_homog_zero l' h, mul_zero]
    exact isHomogeneous_zero_complex 0
  | succ n =>
    have h' := (isHomogeneous_X_complex l).mul (isHomogeneous_pderiv_of_isHomogeneous_succ l' h)
    rwa [Nat.add_comm 1 n] at h'

theorem pderiv_X_mul_homog {σ : Type} (l l' : σ) {d : ℕ} {P : MvPolynomial σ ℂ}
    (h : P.IsHomogeneous d) : (pderiv l (X l' * P)).IsHomogeneous d := by
  apply isHomogeneous_pderiv_of_isHomogeneous_succ
  have h' := (isHomogeneous_X_complex l').mul h
  rwa [Nat.add_comm 1 d] at h'

theorem blockDiagonalPreservesDegree : KCStep := by
  intro p q r s M hM d P hP
  have hP' : P.IsHomogeneous d := mem_homog_iff_isHomogeneous'.mp hP
  rw [omAct_eq_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  refine Submodule.sum_mem _ fun l _ => Submodule.sum_mem _ fun l' _ => ?_
  by_cases h0 : M l l' = 0
  · rw [h0, zero_smul]
    exact Submodule.zero_mem _
  refine Submodule.smul_mem _ _ ?_
  have hll := hM l l' h0
  rw [omE_apply]
  refine Submodule.add_mem _ ?_ ?_
  · cases h1 : FockH1Action.linePos l
    · have h2 : FockH1Action.linePos l' = false := by
        exact hll.symm.trans h1
      rw [raiB_apply_of_linePos_eq_false h1, lowB_apply_of_linePos_eq_false h2]
      exact neg_mem (mem_homog_iff_isHomogeneous'.mpr (pderiv_X_mul_homog l l' hP'))
    · have h2 : FockH1Action.linePos l' = true := by
        exact hll.symm.trans h1
      rw [raiB_apply_of_linePos_eq_true h1, lowB_apply_of_linePos_eq_true h2]
      exact mem_homog_iff_isHomogeneous'.mpr (X_mul_pderiv_homog l l' hP')
  · split_ifs
    · exact Submodule.smul_mem _ _ hP
    · exact Submodule.zero_mem _

def Rop (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) : Module.End ℂ (FockH1Action.Pol p q r s) :=
  ∑ l, ∑ l', if FockH1Action.linePos l = true ∧ FockH1Action.linePos l' = false then M l l' • FockH1Action.omE l l'
    else 0

def Lop (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) : Module.End ℂ (FockH1Action.Pol p q r s) :=
  ∑ l, ∑ l', if FockH1Action.linePos l = false ∧ FockH1Action.linePos l' = true then M l l' • FockH1Action.omE l l'
    else 0

theorem omAct_eq_Rop_add_Lop (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ)
    (hM : OppSign M) : FockH1Action.omAct p q r s M = Rop M + Lop M := by
  rw [omAct_eq_sum]
  unfold Rop Lop
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l' _ => ?_
  by_cases h0 : M l l' = 0
  · simp [h0]
  · have hd := hM l l' h0
    cases h1 : FockH1Action.linePos l <;>
      cases h2 : FockH1Action.linePos l' <;> simp_all

theorem Rop_apply (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) (P : FockH1Action.Pol p q r s) :
    Rop M P = ∑ l, ∑ l', if FockH1Action.linePos l = true ∧ FockH1Action.linePos l' = false then
      M l l' • (X l * (X l' * P)) else 0 := by
  unfold Rop
  simp only [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  split_ifs with h
  · rw [LinearMap.smul_apply, omE_pos_neg h.1 h.2]
  · rfl

theorem Lop_apply (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) (P : FockH1Action.Pol p q r s) :
    Lop M P = ∑ l, ∑ l', if FockH1Action.linePos l = false ∧ FockH1Action.linePos l' = true then
      M l l' • (-(pderiv l (pderiv l' P))) else 0 := by
  unfold Lop
  simp only [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  split_ifs with h
  · rw [LinearMap.smul_apply, omE_neg_pos h.1 h.2]
  · rfl

theorem Rop_raise (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) (d : ℕ)
    (P : FockH1Action.Pol p q r s) (hP : P ∈ FockH1Action.homog (FockH1Action.Ln p q r s) d) :
    Rop M P ∈ FockH1Action.homog (FockH1Action.Ln p q r s) (d + 2) := by
  rw [Rop_apply]
  refine Submodule.sum_mem _ fun l _ => Submodule.sum_mem _ fun l' _ => ?_
  split_ifs
  · refine Submodule.smul_mem _ _ (mem_homog_iff_isHomogeneous'.mpr ?_)
    have h := (isHomogeneous_X_complex l).mul ((isHomogeneous_X_complex l').mul (mem_homog_iff_isHomogeneous'.mp hP))
    rwa [show 1 + (1 + d) = d + 2 by omega] at h
  · exact Submodule.zero_mem _

theorem hc_pderiv {σ : Type} (l : σ) (e : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent e (pderiv l P) = pderiv l (homogeneousComponent (e + 1) P) :=
  homogeneousComponent_pderiv l e P

theorem Lop_shift (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) (e : ℕ)
    (P : FockH1Action.Pol p q r s) :
    homogeneousComponent e (Lop M P) = Lop M (homogeneousComponent (e + 2) P) := by
  rw [show e + 2 = e + 1 + 1 from rfl, Lop_apply, Lop_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun l' _ => ?_
  split_ifs
  · rw [map_smul, map_neg, hc_pderiv, hc_pderiv]
  · exact map_zero _

theorem pcStep_of (hS : PMSplit) : PCStep := by
  intro p q r s M hM P
  have h := hS _ (Rop M) (Lop M) (Rop_raise M)
    (Lop_shift M) P
  rw [omAct_eq_Rop_add_Lop M hM, h.1, h.2, LinearMap.add_apply]

section Inner

variable {σ : Type}

theorem fi_zero_left (Q : MvPolynomial σ ℂ) : FockH1Action.fockInner 0 Q = 0 := by
  simp [FockH1Action.fockInner]

theorem fi_zero_right (P : MvPolynomial σ ℂ) : FockH1Action.fockInner P 0 = 0 := by
  simp [FockH1Action.fockInner]

theorem fi_smul_left (hL : FockLinL) (c : ℂ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (c • P) Q = (starRingEnd ℂ) c * FockH1Action.fockInner P Q := by
  have h := hL σ c P 0 Q
  simp only [add_zero, fi_zero_left] at h
  exact h

theorem fi_add_left (hL : FockLinL) (P₁ P₂ Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (P₁ + P₂) Q = FockH1Action.fockInner P₁ Q + FockH1Action.fockInner P₂ Q := by
  have h := hL σ 1 P₁ P₂ Q
  simp only [one_smul, map_one, one_mul] at h
  exact h

theorem fi_smul_right (hR : FockLinR) (c : ℂ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (c • Q) = c * FockH1Action.fockInner P Q := by
  have h := hR σ c P Q 0
  simp only [add_zero, fi_zero_right] at h
  exact h

theorem fi_add_right (hR : FockLinR) (P Q₁ Q₂ : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (Q₁ + Q₂) = FockH1Action.fockInner P Q₁ + FockH1Action.fockInner P Q₂ := by
  have h := hR σ 1 P Q₁ Q₂
  simp only [one_smul, one_mul] at h
  exact h

theorem fi_sum_left {ι : Type} (hL : FockLinL) (t : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (∑ i ∈ t, f i) Q = ∑ i ∈ t, FockH1Action.fockInner (f i) Q := by
  classical
  induction t using Finset.induction_on
  · simp only [Finset.sum_empty, fi_zero_left]
  · rename_i a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fi_add_left hL, ih]

private theorem fockInner_neg_right' (hR : FockLinR) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (-Q) = -FockH1Action.fockInner P Q := by
  have h := fi_smul_right hR (-1 : ℂ) P Q
  rw [neg_one_smul, neg_one_mul] at h
  exact h

theorem fi_sum_right {ι : Type} (hR : FockLinR) (t : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (P : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (∑ i ∈ t, f i) = ∑ i ∈ t, FockH1Action.fockInner P (f i) := by
  classical
  induction t using Finset.induction_on
  · simp only [Finset.sum_empty, fi_zero_right]
  · rename_i a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fi_add_right hR, ih]

end Inner

theorem fi_Rop (hL : FockLinL) (hX : FockXAdj)
    (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) (P Q : FockH1Action.Pol p q r s) :
    FockH1Action.fockInner (Rop M P) Q = ∑ l, ∑ l', if FockH1Action.linePos l = true ∧ FockH1Action.linePos l' = false
      then (starRingEnd ℂ) (M l l') * FockH1Action.fockInner P (pderiv l' (pderiv l Q)) else 0 := by
  rw [Rop_apply, fi_sum_left hL]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [fi_sum_left hL]
  refine Finset.sum_congr rfl fun l' _ => ?_
  split_ifs
  · rw [fi_smul_left hL, hX _ l, hX _ l']
  · exact fi_zero_left Q

theorem fi_Lop (hR : FockLinR)
    (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) (P Q : FockH1Action.Pol p q r s) :
    FockH1Action.fockInner P (Lop M Q) = ∑ l, ∑ l', if FockH1Action.linePos l = false ∧ FockH1Action.linePos l' = true
      then -(M l l' * FockH1Action.fockInner P (pderiv l (pderiv l' Q))) else 0 := by
  rw [Lop_apply, fi_sum_right hR]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [fi_sum_right hR]
  refine Finset.sum_congr rfl fun l' _ => ?_
  split_ifs
  · rw [fi_smul_right hR, fockInner_neg_right' hR, mul_neg]
  · exact fi_zero_right P

theorem adjStep_of (hS : PMSplit) (hL : FockLinL) (hR : FockLinR) (hX : FockXAdj) : AdjStep := by
  intro p q r s M M' hM hM' hA P Q
  have e1 := (hS _ (Rop M) (Lop M) (Rop_raise M)
    (Lop_shift M) P).1
  have e2 := (hS _ (Rop M') (Lop M') (Rop_raise M')
    (Lop_shift M') Q).2
  rw [omAct_eq_Rop_add_Lop M hM,
    omAct_eq_Rop_add_Lop M' hM', e1, e2,
    fi_Rop hL hX, fi_Lop hR]
  simp only [← Finset.sum_neg_distrib]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  by_cases h : FockH1Action.linePos l = true ∧ FockH1Action.linePos l' = false
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩, hA l l' h.1 h.2, neg_neg]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩), neg_zero]

end FockRL

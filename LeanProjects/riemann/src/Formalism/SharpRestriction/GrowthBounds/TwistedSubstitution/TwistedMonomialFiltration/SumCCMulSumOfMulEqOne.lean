import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.AlmostEverywhereSpherical

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1

open Formalism.MainNotions.G

def flt_tay (R : Type*) [CommRing R] (σ : Type*) : MvPolynomial σ R →+* MvPolynomial σ (MvPolynomial σ R) :=
  eval₂Hom (C.comp C) (fun v => C (X v) + X v)

def flt_g (R : Type*) [CommRing R] {σ : Type*} (m be : σ →₀ ℕ) : MvPolynomial σ R :=
  monomial (m - be) (((be.prod fun k j => (m k).choose j : ℕ)) : R)

open Classical in
theorem flt_g_pascal (R : Type*) [CommRing R] {σ : Type*} (m be : σ →₀ ℕ) (a : σ) :
    flt_g R (m + Finsupp.single a 1) be =
      flt_g R m be * X a + (if a ∈ be.support then flt_g R m (be - Finsupp.single a 1) else 0) := by
  unfold flt_g
  rw [X, monomial_mul, mul_one]
  by_cases ha : a ∈ be.support
  · rw [if_pos ha]
    have hba : be a ≠ 0 := Finsupp.mem_support_iff.1 ha
    have hsub : (be - Finsupp.single a 1).support ⊆ be.support := by
      intro k hk
      rw [Finsupp.mem_support_iff] at hk ⊢
      rw [Finsupp.tsub_apply] at hk
      omega
    rw [Finsupp.prod_of_support_subset _ hsub _ (fun k _ => Nat.choose_zero_right _)]
    simp only [Finsupp.prod]
    rw [← Finset.mul_prod_erase _ _ ha, ← Finset.mul_prod_erase _ _ ha, ← Finset.mul_prod_erase _ _ ha]
    have hrest1 : ∏ k ∈ be.support.erase a, ((m + Finsupp.single a 1 : σ →₀ ℕ) k).choose (be k) =
        ∏ k ∈ be.support.erase a, (m k).choose (be k) :=
      Finset.prod_congr rfl fun k hk => by
        rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hk).symm, add_zero]
    have hrest2 : ∏ k ∈ be.support.erase a, (m k).choose ((be - Finsupp.single a 1 : σ →₀ ℕ) k) =
        ∏ k ∈ be.support.erase a, (m k).choose (be k) :=
      Finset.prod_congr rfl fun k hk => by
        rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hk).symm, tsub_zero]
    rw [hrest1, hrest2]
    obtain ⟨b, hb⟩ : ∃ b, be a = b + 1 := ⟨be a - 1, by omega⟩
    have hA : (m + Finsupp.single a 1 : σ →₀ ℕ) a = m a + 1 := by simp
    have hB : (be - Finsupp.single a 1 : σ →₀ ℕ) a = b := by rw [Finsupp.tsub_apply, hb]; simp
    rw [hA, hB, hb, Nat.choose_succ_succ]
    rcases Nat.lt_or_ge (m a) b with hlt | hge
    · rw [Nat.choose_eq_zero_of_lt hlt, Nat.choose_eq_zero_of_lt (by omega : m a < b + 1)]
      simp
    · have e3 : m - (be - Finsupp.single a 1) = m + Finsupp.single a 1 - be := by
        ext k
        by_cases hk : k = a
        · subst hk
          simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same, hb]
          omega
        · simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hk)]
          omega
      rcases Nat.lt_or_ge (m a) (b + 1) with hlt2 | hge2
      · rw [Nat.choose_eq_zero_of_lt hlt2, e3]
        simp
      · have e2 : m - be + Finsupp.single a 1 = m + Finsupp.single a 1 - be := by
          ext k
          by_cases hk : k = a
          · subst hk
            simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same, hb]
            omega
          · simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hk)]
            omega
        rw [e2, e3, ← map_add]
        congr 1
        push_cast
        ring
  · rw [if_neg ha, add_zero]
    have hba : be a = 0 := by simpa [Finsupp.mem_support_iff] using ha
    have e2 : m - be + Finsupp.single a 1 = m + Finsupp.single a 1 - be := by
      ext k
      by_cases hk : k = a
      · subst hk
        simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same, hba]
        omega
      · simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hk)]
        omega
    have hc : (be.prod fun k j => ((m + Finsupp.single a 1 : σ →₀ ℕ) k).choose j) = be.prod fun k j => (m k).choose j := by
      simp only [Finsupp.prod]
      refine Finset.prod_congr rfl fun k hk => ?_
      have hka : a ≠ k := fun h => ha (h ▸ hk)
      rw [Finsupp.add_apply, Finsupp.single_apply, if_neg hka, add_zero]
    rw [e2, hc]

theorem flt_tay_monomial (R : Type*) [CommRing R] {σ : Type*} (m : σ →₀ ℕ) :
    ∀ be, coeff be (flt_tay R σ (monomial m 1)) = flt_g R m be := by
  classical
  have htx : ∀ a, flt_tay R σ (X a) = C (X a) + X a := fun a => by simp [flt_tay]
  have step : ∀ m : σ →₀ ℕ, (∀ be, coeff be (flt_tay R σ (monomial m 1)) = flt_g R m be) →
      ∀ a be, coeff be (flt_tay R σ (monomial (m + Finsupp.single a 1) 1)) =
        flt_g R (m + Finsupp.single a 1) be := by
    intro m hm a be
    rw [flt_g_pascal, monomial_add_single, pow_one, map_mul, htx, mul_add, coeff_add,
      mul_comm _ (C (X a)), coeff_C_mul, coeff_mul_X', hm, mul_comm (X a)]
    by_cases ha : a ∈ be.support
    · simp [ha, hm]
    · simp [ha]
  induction m using Finsupp.induction with
  | zero =>
    intro be
    by_cases hbe : be = 0
    · subst hbe
      simp [flt_g]
    · obtain ⟨k, hk⟩ : ∃ k, be k ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hbe (Finsupp.ext hc)
      have hz : (be.prod fun k j => ((Nat.choose 0 j : ℕ) : R)) = 0 := by
        rw [Finsupp.prod]
        exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hk)
          (by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)
      simp [flt_g, hz, coeff_one, Ne.symm hbe]
  | single_add a b f _ hb ih =>
    clear hb
    induction b with
    | zero => simpa using ih
    | succ b ihb =>
      have e : Finsupp.single a (b + 1) + f = (Finsupp.single a b + f) + Finsupp.single a 1 := by
        rw [Finsupp.single_add, add_right_comm]
      rw [e]
      exact step _ ihb a

theorem flt_tay_coeff (R : Type*) [CommRing R] {σ : Type*} (F : MvPolynomial σ R) (be : σ →₀ ℕ) :
    coeff be (flt_tay R σ F) = divDer be F := by
  conv_lhs => rw [F.as_sum]
  rw [map_sum, coeff_sum, divDer]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show monomial m (coeff m F) = C (coeff m F) * monomial m 1 by rw [C_mul_monomial, mul_one], map_mul]
  have hC : flt_tay R σ (C (coeff m F)) = C (C (coeff m F)) := by simp [flt_tay]
  rw [hC, coeff_C_mul, flt_tay_monomial, flt_g, C_mul_monomial]
  split_ifs with hle
  · rfl
  · have hz : (be.prod fun k j => (m k).choose j) = 0 := by
      obtain ⟨k, hk⟩ : ∃ k, m k < be k := by
        by_contra hcon
        push_neg at hcon
        exact hle fun k => hcon k
      rw [Finsupp.prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 (by omega)) (Nat.choose_eq_zero_of_lt hk)
    rw [hz, Nat.cast_zero, mul_zero, monomial_zero]

open Classical in

def flt_Th {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n) :
    MvPolynomial (ι × Fin n) (GLLaurent R n) →+*
      MvPolynomial (ι × Fin n) (MvPolynomial (ι × Fin n) (GLLaurent R n)) :=
  eval₂Hom (C.comp C) fun w => C (X w) +
    (if w.1 ∈ S then
      (if LL.vec w.1 then ∑ c : Fin n, C (C (twistMat R n j (-1) c w.2)) * X (w.1, c)
       else ∑ c : Fin n, C (C (twistMat R n j 1 w.2 c)) * X (w.1, c))
     else X w)

theorem sum_C_C_mul_sum_of_mul_eq_one {B : Type*} [CommRing B] {σ' σ'' : Type*} {n : ℕ} (P Q : Matrix (Fin n) (Fin n) B)
    (h : Q * P = 1) (Y : Fin n → MvPolynomial σ' (MvPolynomial σ'' B)) (d : Fin n) :
    ∑ b, C (C (P b d)) * ∑ c, C (C (Q c b)) * Y c = Y d := by
  simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum]
  have hcd : ∀ c, ∑ b, P b d * Q c b = (1 : Matrix (Fin n) (Fin n) B) c d := fun c => by
    rw [← h, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  simp_rw [hcd, Matrix.one_apply]
  simp

theorem flt_Th_twist {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n) :
    (MvPolynomial.map (twistSub (R := R) LL S j)).comp (flt_tay R (ι × Fin n)) =
      (flt_Th LL S j).comp (twistSub (R := R) LL S j) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [flt_tay, flt_Th, twistSub]
  · intro v
    have hY1 := sum_C_C_mul_sum_of_mul_eq_one (σ' := ι × Fin n) (σ'' := ι × Fin n) (twistMat R n j 1) (twistMat R n j (-1))
      (by simpa using flt_twistMat_mul R n j (-1)) (fun c => X (v.1, c)) v.2
    have hM : twistMat R n j (-1) * twistMat R n j 1 = 1 := by simpa using flt_twistMat_mul R n j (-1)
    have hY2 := sum_C_C_mul_sum_of_mul_eq_one (σ' := ι × Fin n) (σ'' := ι × Fin n) (Matrix.transpose (twistMat R n j (-1)))
      (Matrix.transpose (twistMat R n j 1))
      (by rw [← Matrix.transpose_mul, hM, Matrix.transpose_one]) (fun c => X (v.1, c)) v.2
    simp only [Matrix.transpose_apply] at hY2
    by_cases hS : v.1 ∈ S
    · by_cases hv : LL.vec v.1 = true
      · simp [flt_tay, flt_Th, twistSub, hS, hv, mul_add, Finset.sum_add_distrib, hY1]
      · simp [flt_tay, flt_Th, twistSub, hS, hv, mul_add, Finset.sum_add_distrib, hY2]
    · simp [flt_tay, flt_Th, twistSub, hS]

theorem flt_Th_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) {t : ℤ} {P : MvPolynomial (ι × Fin n) (GLLaurent R n)}
    (hP : P ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t) :
    flt_Th LL S j P ∈ (flt_lift (laurentCoeffFiltration R n (ι × Fin n) e) (flt_cost LL S (!bm))).F t := by
  have hone : ∀ s : ℤ, s = 0 → (1 : GLLaurent R n) ∈ (flt_L (GLCoord R n) e).F s := by
    rintro s rfl
    exact (flt_L (GLCoord R n) e).one_mem
  have hX : ∀ w, flt_Th LL S j (X w) ∈ (flt_lift (laurentCoeffFiltration R n (ι × Fin n) e) (flt_cost LL S (!bm))).F
      ((0 : (ι × Fin n →₀ ℕ) →+ ℤ) (Finsupp.single w 1)) := by
    intro w
    rw [AddMonoidHom.zero_apply]
    have hXw : (X w : MvPolynomial (ι × Fin n) (GLLaurent R n)) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F 0 :=
      flt_monomial_mem (hone _ (by simp))
    simp only [flt_Th, eval₂Hom_X']
    refine AddSubgroup.add_mem _ (flt_C_mem hXw) ?_
    split_ifs with hS hv
    · refine AddSubgroup.sum_mem _ fun c _ => ?_
      rw [show (C (C (twistMat R n j (-1) c w.2)) * X (w.1, c) :
          MvPolynomial (ι × Fin n) (MvPolynomial (ι × Fin n) (GLLaurent R n))) =
          monomial (Finsupp.single (w.1, c) 1) (C (twistMat R n j (-1) c w.2)) by
        rw [X, C_mul_monomial, mul_one]]
      refine flt_monomial_mem (flt_C_mem (flt_twistMat_mem R n j _ _ _ ?_ ?_ _ _)) <;>
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [flt_cost, hS, hv]
    · refine AddSubgroup.sum_mem _ fun c _ => ?_
      rw [show (C (C (twistMat R n j 1 w.2 c)) * X (w.1, c) :
          MvPolynomial (ι × Fin n) (MvPolynomial (ι × Fin n) (GLLaurent R n))) =
          monomial (Finsupp.single (w.1, c) 1) (C (twistMat R n j 1 w.2 c)) by
        rw [X, C_mul_monomial, mul_one]]
      refine flt_monomial_mem (flt_C_mem (flt_twistMat_mem R n j _ _ _ ?_ ?_ _ _)) <;>
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [flt_cost, hS, hv]
    · have h1 : (1 : MvPolynomial (ι × Fin n) (GLLaurent R n)) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F
          (0 - flt_cost LL S (!bm) (Finsupp.single w 1)) := by
        have h0 : flt_cost LL S (!bm) (Finsupp.single w 1) = 0 := by simp [flt_cost, hS]
        rw [h0, sub_zero]
        exact (laurentCoeffFiltration R n (ι × Fin n) e).one_mem
      exact flt_monomial_mem h1
  rw [P.as_sum, map_sum]
  refine AddSubgroup.sum_mem _ fun m _ => ?_
  rw [show monomial m (coeff m P) = C (coeff m P) * monomial m 1 by rw [C_mul_monomial, mul_one], map_mul]
  have hc : coeff m P ∈ (flt_L (GLCoord R n) e).F t := by
    have h3 := (flt_lift_mem.1 hP) m
    simpa using h3
  have h1 : flt_Th LL S j (C (coeff m P)) ∈
      (flt_lift (laurentCoeffFiltration R n (ι × Fin n) e) (flt_cost LL S (!bm))).F t := by
    simp only [flt_Th, eval₂Hom_C, RingHom.comp_apply]
    exact flt_C_mem (flt_C_mem hc)
  have h2 := flt_hom_monomial _ (flt_Th LL S j) 0 hX m
  rw [AddMonoidHom.zero_apply] at h2
  have h4 := (flt_lift (laurentCoeffFiltration R n (ι × Fin n) e) (flt_cost LL S (!bm))).mul_mem h1 h2
  rwa [add_zero] at h4

theorem flt_divDer_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) {t : ℤ} {F : MvPolynomial (ι × Fin n) R}
    (hF : twistSub LL S j F ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t) (be : ι × Fin n →₀ ℕ) :
    twistSub LL S j (divDer be F) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F (t - flt_cost LL S (!bm) be) := by
  have h1 := flt_lift_mem.1 (flt_Th_mem LL S j h hF) be
  have e1 : twistSub LL S j (divDer be F) = coeff be (flt_Th LL S j (twistSub LL S j F)) := by
    have h2 := congrArg (fun φ => coeff be (φ F)) (flt_Th_twist (R := R) LL S j)
    simp only [RingHom.comp_apply, coeff_map] at h2
    rw [← h2, flt_tay_coeff]
  rw [e1]
  exact h1

theorem flt_op_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) {t : ℤ} {F : MvPolynomial (ι × Fin n) R}
    (hF : twistSub LL S j F ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t) (al be : ι × Fin n →₀ ℕ) :
    twistSub LL S j (monomial al 1 * divDer be F) ∈
      (laurentCoeffFiltration R n (ι × Fin n) e).F (t - (flt_cost LL S bm al + flt_cost LL S (!bm) be)) := by
  rw [map_mul]
  have h1 := flt_twist_monomial_mem (R := R) LL S j h al
  have h2 := flt_divDer_mem LL S j h hF be
  have h3 := (laurentCoeffFiltration R n (ι × Fin n) e).mul_mem h1 h2
  rwa [show -flt_cost LL S bm al + (t - flt_cost LL S (!bm) be) =
    t - (flt_cost LL S bm al + flt_cost LL S (!bm) be) by ring] at h3

private theorem flt_cost_false_eq_covDeg {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) :
    flt_cost LL S false al = (covDeg LL S al : ℤ) := by
  simp only [flt_cost, Finsupp.liftAddHom_apply, covDeg, Finsupp.sum]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

private theorem flt_cost_true_eq_vecDeg {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) :
    flt_cost LL S true al = (vecDeg LL S al : ℤ) := by
  simp only [flt_cost, Finsupp.liftAddHom_apply, vecDeg, Finsupp.sum]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

theorem flt_op_mem_val {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    {F : MvPolynomial (ι × Fin n) R} {t : ℤ} (ht : (t : WithTop ℤ) ≤ valS LL S F) (al be : ι × Fin n →₀ ℕ)
    (N : ℕ) (hN : covDeg LL S al + vecDeg LL S be ≤ N) :
    twistSub LL S (lastIdx n) (monomial al 1 * divDer be F) ∈ (laurentCoeffFiltration R n (ι × Fin n) 1).F (t - N) := by
  have hF := (flt_le_valS LL S F t).1 ht
  have hm := flt_op_mem LL S (lastIdx n) (Or.inl ⟨rfl, rfl⟩ : flt_compat 1 false) hF al be
  refine (laurentCoeffFiltration R n (ι × Fin n) 1).anti ?_ hm
  simp only [Bool.not_false, flt_cost_false_eq_covDeg, flt_cost_true_eq_vecDeg]
  have hN' : ((covDeg LL S al + vecDeg LL S be : ℕ) : ℤ) ≤ N := by exact_mod_cast hN
  push_cast at hN'
  linarith

theorem flt_op_mem_lam {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    {F : MvPolynomial (ι × Fin n) R} {M : ℤ} (hM : lam1S LL S F ≤ (M : WithBot ℤ)) (al be : ι × Fin n →₀ ℕ)
    (N : ℕ) (hN : vecDeg LL S al + covDeg LL S be ≤ N) :
    twistSub LL S (0 : Fin n) (monomial al 1 * divDer be F) ∈ (laurentCoeffFiltration R n (ι × Fin n) (-1)).F (-(M + N)) := by
  have hF := (flt_lam1S_le LL S F M).1 hM
  have hm := flt_op_mem LL S (0 : Fin n) (Or.inr ⟨rfl, rfl⟩ : flt_compat (-1) true) hF al be
  refine (laurentCoeffFiltration R n (ι × Fin n) (-1)).anti ?_ hm
  simp only [Bool.not_true, flt_cost_false_eq_covDeg, flt_cost_true_eq_vecDeg]
  have hN' : ((vecDeg LL S al + covDeg LL S be : ℕ) : ℤ) ≤ N := by exact_mod_cast hN
  push_cast at hN'
  linarith

theorem flt_op_valS {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F : MvPolynomial (ι × Fin n) R) (al be : ι × Fin n →₀ ℕ) (N : ℕ)
    (hN : covDeg LL S al + vecDeg LL S be ≤ N) :
    valS LL S F ≤ valS LL S (monomial al 1 * divDer be F) + ((N : ℤ) : WithTop ℤ) := by
  by_contra hcon
  push_neg at hcon
  cases hv : valS LL S (monomial al 1 * divDer be F) with
  | top =>
    rw [hv] at hcon
    simp at hcon
  | coe w =>
    rw [hv] at hcon
    have ht : ((w + N + 1 : ℤ) : WithTop ℤ) ≤ valS LL S F := by
      cases hF : valS LL S F with
      | top => exact le_top
      | coe x =>
        rw [hF] at hcon
        norm_cast at hcon ⊢ <;> omega
    have hm := flt_op_mem_val LL S ht al be N hN
    rw [← flt_le_valS, hv] at hm
    norm_cast at hm <;> omega

theorem flt_op_lam1S {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F : MvPolynomial (ι × Fin n) R) (al be : ι × Fin n →₀ ℕ) (N : ℕ)
    (hN : vecDeg LL S al + covDeg LL S be ≤ N) :
    lam1S LL S (monomial al 1 * divDer be F) ≤ lam1S LL S F + ((N : ℤ) : WithBot ℤ) := by
  by_contra hcon
  push_neg at hcon
  cases hv : lam1S LL S (monomial al 1 * divDer be F) with
  | bot =>
    rw [hv] at hcon
    simp at hcon
  | coe w =>
    rw [hv] at hcon
    have hM : lam1S LL S F ≤ ((w - N - 1 : ℤ) : WithBot ℤ) := by
      cases hF : lam1S LL S F with
      | bot => exact bot_le
      | coe x =>
        rw [hF] at hcon
        norm_cast at hcon ⊢ <;> omega
    have hm := flt_op_mem_lam LL S hM al be N hN
    rw [← flt_lam1S_le, hv] at hm
    norm_cast at hm <;> omega

end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1

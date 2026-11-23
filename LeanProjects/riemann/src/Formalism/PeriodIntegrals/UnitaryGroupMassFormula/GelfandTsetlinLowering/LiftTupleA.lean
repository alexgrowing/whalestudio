import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftDefs
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas

noncomputable section

namespace PI.WGL.LTA

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

def upd {m r : ℕ} (ρ : Fin m → Fin r) (S : Finset (Fin m)) (a : Fin r) : Fin m → Fin r :=
  fun p => if p ∈ S then a else ρ p

def gmin {r c m : ℕ} (ρ : Fin m → Fin r) (κ : Fin m → Fin c) : MvPolynomial (Fin r × Fin c) ℤ :=
  (Matrix.of fun p q : Fin m => (X (ρ p, κ q) : MvPolynomial (Fin r × Fin c) ℤ)).det

theorem rowGen_Xz {r c : ℕ} (a b : Fin r) (v : Fin r × Fin c) :
    rowGen ℤ a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  unfold rowGen
  rw [aeval_X]

theorem rowGen_gmin {r c m : ℕ} (a b : Fin r) (ρ : Fin m → Fin r) (κ : Fin m → Fin c) :
    rowGen ℤ a b (gmin ρ κ) =
      ∑ S : Finset (Fin m), if (∀ p ∈ S, ρ p = b) then
        Polynomial.X ^ S.card * Polynomial.C (gmin (upd ρ S a) κ) else 0 := by
  classical
  set A : Equiv.Perm (Fin m) → Fin m → Polynomial (MvPolynomial (Fin r × Fin c) ℤ) :=
    fun σ i => Polynomial.C (X (ρ i, κ (σ i))) with hA
  set B : Equiv.Perm (Fin m) → Fin m → Polynomial (MvPolynomial (Fin r × Fin c) ℤ) :=
    fun σ i => if ρ i = b then Polynomial.X * Polynomial.C (X (a, κ (σ i))) else 0 with hB
  have h1 : rowGen ℤ a b (gmin ρ κ) =
      ∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ • ∏ i, (B σ i + A σ i) := by
    unfold gmin
    rw [AlgHom.map_det, ← Matrix.det_transpose, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Matrix.transpose_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowGen_Xz,
      hA, hB]
    ring
  have h2 : ∀ S : Finset (Fin m), gmin (upd ρ S a) κ =
      ∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ •
        ∏ i, (X (upd ρ S a i, κ (σ i)) : MvPolynomial (Fin r × Fin c) ℤ) := by
    intro S
    unfold gmin
    rw [← Matrix.det_transpose, Matrix.det_apply]
    rfl
  rw [h1]
  simp only [Finset.prod_add, Finset.smul_sum]
  rw [Finset.sum_comm, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  split_ifs with hS
  · rw [h2, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hBS : ∏ i ∈ S, B σ i =
        Polynomial.X ^ S.card * Polynomial.C (∏ i ∈ S, (X (a, κ (σ i)) : MvPolynomial (Fin r × Fin c) ℤ)) := by
      rw [Finset.prod_congr rfl (fun i hi => show B σ i = Polynomial.X * Polynomial.C (X (a, κ (σ i))) by
        simp [hB, hS i hi])]
      rw [Finset.prod_mul_distrib, Finset.prod_const, map_prod]
    have hAS : ∏ i ∈ Finset.univ \ S, A σ i =
        Polynomial.C (∏ i ∈ Finset.univ \ S, (X (ρ i, κ (σ i)) : MvPolynomial (Fin r × Fin c) ℤ)) := by
      rw [map_prod]
    have hprod : (∏ i ∈ Finset.univ \ S, (X (ρ i, κ (σ i)) : MvPolynomial (Fin r × Fin c) ℤ)) *
        (∏ i ∈ S, (X (a, κ (σ i)) : MvPolynomial (Fin r × Fin c) ℤ)) =
        ∏ i, (X (upd ρ S a i, κ (σ i)) : MvPolynomial (Fin r × Fin c) ℤ) := by
      rw [← Finset.prod_sdiff (Finset.subset_univ S)]
      congr 1
      · refine Finset.prod_congr rfl fun i hi => ?_
        simp [upd, (Finset.mem_sdiff.mp hi).2]
      · refine Finset.prod_congr rfl fun i hi => ?_
        simp [upd, hi]
    rw [hBS, hAS, ← hprod, Units.smul_def, Units.smul_def, map_zsmul, map_mul]
    simp only [zsmul_eq_mul]
    ring
  · push_neg at hS
    obtain ⟨p, hp, hpb⟩ := hS
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [Finset.prod_eq_zero hp (by simp [hB, hpb]), zero_mul, smul_zero]

def Exp {r c n m : ℕ} (e : Fin n → Fin r) (G : (Fin m → Fin n) → MvPolynomial (Fin r × Fin c) ℤ) : Prop :=
  ∀ (a b : Fin n) (ρ : Fin m → Fin n), rowGen ℤ (e a) (e b) (G ρ) =
    ∑ S : Finset (Fin m), if (∀ p ∈ S, ρ p = b) then
      Polynomial.X ^ S.card * Polynomial.C (G (upd ρ S a)) else 0

theorem exp_gmin {r c n m : ℕ} (e : Fin n → Fin r) (he : Function.Injective e) (κ : Fin m → Fin c) :
    Exp e (fun ρ : Fin m → Fin n => gmin (e ∘ ρ) κ) := by
  intro a b ρ
  beta_reduce
  rw [rowGen_gmin]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h1 : (∀ p ∈ S, (e ∘ ρ) p = e b) ↔ (∀ p ∈ S, ρ p = b) := by
    simp only [Function.comp_apply, he.eq_iff]
  have h2 : upd (e ∘ ρ) S (e a) = e ∘ upd ρ S a := by
    funext p
    simp only [upd, Function.comp_apply]
    split_ifs <;> rfl
  by_cases hc : ∀ p ∈ S, ρ p = b
  · rw [if_pos hc, if_pos (h1.mpr hc), h2]
  · rw [if_neg hc, if_neg (fun h => hc (h1.mp h))]

theorem sum_finset_castSucc {M : Type*} [AddCommMonoid M] {m : ℕ} (f : Finset (Fin (m + 1)) → M)
    (hf : ∀ S, Fin.last m ∈ S → f S = 0) :
    ∑ S : Finset (Fin (m + 1)), f S = ∑ S : Finset (Fin m), f (S.map Fin.castSuccEmb) := by
  classical
  have hm : ∑ S : Finset (Fin m), f (S.map Fin.castSuccEmb) =
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin m))).map (Finset.mapEmbedding Fin.castSuccEmb).toEmbedding, f S := by
    rw [Finset.sum_map]
    rfl
  rw [hm]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro S _ hS
  apply hf
  by_contra hl
  apply hS
  rw [Finset.mem_map]
  refine ⟨S.preimage Fin.castSucc (Fin.castSucc_injective m).injOn, Finset.mem_univ _, ?_⟩
  ext x
  simp only [RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply, Finset.mem_map, Finset.mem_preimage,
    Fin.coe_castSuccEmb]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    have hxl : x ≠ Fin.last m := fun h => hl (h ▸ hx)
    exact ⟨x.castPred hxl, by simpa using hx, by simp⟩

def liftR {r n m : ℕ} (e : Fin n → Fin r) (z : Fin r) (ρ : Fin m → Fin n) : Fin (m + 1) → Fin r :=
  fun p => if hp : p.1 < m then e (ρ ⟨p.1, hp⟩) else z

theorem liftR_castSucc {r n m : ℕ} (e : Fin n → Fin r) (z : Fin r) (ρ : Fin m → Fin n) (q : Fin m) :
    liftR e z ρ (Fin.castSucc q) = e (ρ q) := by
  simp [liftR]

theorem liftR_last {r n m : ℕ} (e : Fin n → Fin r) (z : Fin r) (ρ : Fin m → Fin n) :
    liftR e z ρ (Fin.last m) = z := by
  simp [liftR]

theorem exp_lift {r c n m : ℕ} (e : Fin n → Fin r) (he : Function.Injective e) (z : Fin r)
    (hz : ∀ b, e b ≠ z) (κ : Fin (m + 1) → Fin c) :
    Exp e (fun ρ : Fin m → Fin n => gmin (liftR e z ρ) κ) := by
  intro a b ρ
  beta_reduce
  rw [rowGen_gmin, sum_finset_castSucc]
  · refine Finset.sum_congr rfl fun S _ => ?_
    beta_reduce
    have h1 : (∀ p ∈ S.map Fin.castSuccEmb, liftR e z ρ p = e b) ↔ (∀ p ∈ S, ρ p = b) := by
      simp [liftR_castSucc, he.eq_iff]
    have h2 : upd (liftR e z ρ) (S.map Fin.castSuccEmb) (e a) = liftR e z (upd ρ S a) := by
      funext p
      induction p using Fin.lastCases with
      | last =>
        have hl : Fin.last m ∉ S.map Fin.castSuccEmb := by
          simp only [Finset.mem_map, Fin.coe_castSuccEmb, not_exists, not_and]
          intro q _ hq
          exact (Fin.castSucc_lt_last q).ne hq
        simp [upd, hl, liftR_last]
      | cast q =>
        have hm : Fin.castSucc q ∈ S.map Fin.castSuccEmb ↔ q ∈ S := Finset.mem_map' Fin.castSuccEmb
        simp only [upd, liftR_castSucc, hm]
        split_ifs <;> rfl
    by_cases hc : ∀ p ∈ S, ρ p = b
    · rw [if_pos (h1.mpr hc), if_pos hc, h2, Finset.card_map]
    · rw [if_neg (fun h => hc (h1.mp h)), if_neg hc]
  · intro S hS
    beta_reduce
    rw [if_neg]
    intro hall
    exact hz b ((liftR_last e z ρ).symm.trans (hall _ hS)).symm

theorem rowDiv_prod {r c n K : ℕ} (e : Fin n → Fin r) (sz : Fin K → ℕ)
    (G : ∀ k, (Fin (sz k) → Fin n) → MvPolynomial (Fin r × Fin c) ℤ) (hG : ∀ k, Exp e (G k))
    (C0 : MvPolynomial (Fin r × Fin c) ℤ) (a b : Fin n) (hC : rowGen ℤ (e a) (e b) C0 = Polynomial.C C0)
    (t : ℕ) (I : ∀ k, Fin (sz k) → Fin n) :
    rowDiv ℤ (e a) (e b) t (C0 * ∏ k, G k (I k)) =
      ∑ F : (∀ k, Finset (Fin (sz k))), if (∀ k, ∀ p ∈ F k, I k p = b) ∧ ∑ k, (F k).card = t then
        C0 * ∏ k, G k (upd (I k) (F k) a) else 0 := by
  classical
  unfold rowDiv
  rw [map_mul, hC, map_prod, Finset.prod_congr rfl (fun k _ => hG k a b (I k)), Fintype.prod_sum,
    Finset.mul_sum, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [Finset.prod_ite_zero]
  by_cases hA : ∀ k ∈ (Finset.univ : Finset (Fin K)), ∀ p ∈ F k, I k p = b
  · rw [if_pos hA, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← map_prod Polynomial.C]
    rw [show Polynomial.C C0 * (Polynomial.X ^ (∑ k, (F k).card) *
          Polynomial.C (∏ k, G k (upd (I k) (F k) a))) =
        Polynomial.monomial (∑ k, (F k).card) (C0 * ∏ k, G k (upd (I k) (F k) a)) by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul]
      ring]
    rw [Polynomial.coeff_monomial]
    have hA' : ∀ k, ∀ p ∈ F k, I k p = b := fun k => hA k (Finset.mem_univ k)
    by_cases hs : ∑ k, (F k).card = t
    · rw [if_pos hs, if_pos ⟨hA', hs⟩]
    · rw [if_neg hs, if_neg (fun h => hs h.2)]
  · rw [if_neg hA, mul_zero, Polynomial.coeff_zero, if_neg]
    intro h
    exact hA (fun k _ => h.1 k)

def tmat {n K : ℕ} (sz : Fin K → ℕ) (a b : Fin n) (t : ℕ) (I : ∀ k, Fin (sz k) → Fin n) :
    (∀ k, Fin (sz k) → Fin n) →₀ ℤ :=
  ∑ F : (∀ k, Finset (Fin (sz k))), if (∀ k, ∀ p ∈ F k, I k p = b) ∧ ∑ k, (F k).card = t then
    Finsupp.single (fun k => upd (I k) (F k) a) 1 else 0

def tlin {n K : ℕ} (sz : Fin K → ℕ) (a b : Fin n) (t : ℕ) :
    ((∀ k, Fin (sz k) → Fin n) →₀ ℤ) →ₗ[ℤ] ((∀ k, Fin (sz k) → Fin n) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (tmat sz a b t)

theorem rowDiv_comb {r c n K : ℕ} (e : Fin n → Fin r) (sz : Fin K → ℕ)
    (G : ∀ k, (Fin (sz k) → Fin n) → MvPolynomial (Fin r × Fin c) ℤ) (hG : ∀ k, Exp e (G k))
    (C0 : MvPolynomial (Fin r × Fin c) ℤ) (a b : Fin n) (hC : rowGen ℤ (e a) (e b) C0 = Polynomial.C C0)
    (t : ℕ) (d : (∀ k, Fin (sz k) → Fin n) →₀ ℤ) :
    rowDiv ℤ (e a) (e b) t (Finsupp.linearCombination ℤ (fun J => C0 * ∏ k, G k (J k)) d) =
      Finsupp.linearCombination ℤ (fun J => C0 * ∏ k, G k (J k)) (tlin sz a b t d) := by
  classical
  have hsm : ∀ (z : ℤ) (x : MvPolynomial (Fin r × Fin c) ℤ),
      rowDiv ℤ (e a) (e b) t (z • x) = z • rowDiv ℤ (e a) (e b) t x := by
    intro z x
    unfold rowDiv
    rw [map_smul, Polynomial.coeff_smul]
  refine Finsupp.induction_linear d ?_ ?_ ?_
  · unfold rowDiv
    simp
  · intro f g hf hg
    rw [map_add, map_add, map_add]
    unfold rowDiv at hf hg ⊢
    rw [map_add, Polynomial.coeff_add, hf, hg]
  · intro J c
    unfold tlin
    rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul, hsm,
      rowDiv_prod e sz G hG C0 a b hC t J]
    congr 1
    unfold tmat
    rw [map_sum]
    refine Finset.sum_congr rfl fun F _ => ?_
    split_ifs
    · rw [Finsupp.linearCombination_single, one_smul]
    · rw [map_zero]

def twd {n K : ℕ} (sz : Fin K → ℕ) : List (Fin n × Fin n × ℕ) →
    (((∀ k, Fin (sz k) → Fin n) →₀ ℤ) →ₗ[ℤ] ((∀ k, Fin (sz k) → Fin n) →₀ ℤ))
  | [] => LinearMap.id
  | x :: w => (tlin sz x.1 x.2.1 x.2.2).comp (twd sz w)

theorem applyWord_comb {r c n K : ℕ} (e : Fin n → Fin r) (sz : Fin K → ℕ)
    (G : ∀ k, (Fin (sz k) → Fin n) → MvPolynomial (Fin r × Fin c) ℤ) (hG : ∀ k, Exp e (G k))
    (C0 : MvPolynomial (Fin r × Fin c) ℤ)
    (hC : ∀ a b : Fin n, a ≠ b → rowGen ℤ (e a) (e b) C0 = Polynomial.C C0) :
    ∀ (w : List (Fin n × Fin n × ℕ)), OffDiag w → ∀ d,
      applyWord ℤ (w.map fun x => (e x.1, e x.2.1, x.2.2))
        (Finsupp.linearCombination ℤ (fun J => C0 * ∏ k, G k (J k)) d) =
      Finsupp.linearCombination ℤ (fun J => C0 * ∏ k, G k (J k)) (twd sz w d)
  | [], _, _ => rfl
  | x :: w, hw, d => by
    have hx : x.1 ≠ x.2.1 := hw x List.mem_cons_self
    have hw' : OffDiag w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    show rowDiv ℤ (e x.1) (e x.2.1) x.2.2 (applyWord ℤ (w.map fun x => (e x.1, e x.2.1, x.2.2))
        (Finsupp.linearCombination ℤ (fun J => C0 * ∏ k, G k (J k)) d)) = _
    rw [applyWord_comb e sz G hG C0 hC w hw' d, rowDiv_comb e sz G hG C0 x.1 x.2.1 (hC _ _ hx)]
    rfl

end PI.WGL.LTA

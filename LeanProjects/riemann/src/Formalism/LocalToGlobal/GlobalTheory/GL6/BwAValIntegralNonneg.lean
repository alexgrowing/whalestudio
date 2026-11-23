import Formalism.LocalToGlobal.GlobalTheory.GL6.LatticeInclusionOfSubIntegral
import Formalism.GradedWeylDivisibility.FinalD

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField

variable (D : D7) (u : D.what₂.Word)

theorem bwA_T_mem_Pv (A : AtTTied u) (v : (D.mem u).A.vT) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ A.Pv v := by
  show A.res v _ = 0
  rw [map_natCast, ← (D.mem u).A.card_Fv v]
  exact FiniteField.cast_card_eq_zero _

theorem bwA_T_smul_Ld_mem_Lk (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT)
    (c : (D.mem u).C.cls i) (z : Fin (D.R.N i) → D.host.E) (hz : z ∈ Ld D u i hi c) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z ∈ Lk A i hi v c :=
  Submodule.mem_sup_right (Submodule.smul_mem_smul (bwA_T_mem_Pv D u A v) hz)

theorem bwA_embT_eq (τ : D.what₂.Tau) (a : D.host.E) :
    embT D τ a = D.what₂.embLL (D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) a)) := by
  show D.host.φ₀ _ = _
  rw [← D.embE_φ₀]; rfl

section Val

variable {LL : Type} [Field LL] (Pl : Rows.Places LL) (w : Pl.Pl)

theorem bwA_val_nat_nonneg (s : ℕ) : (0 : WithTop ℤ) ≤ Pl.val w (s : LL) := by
  induction s with
  | zero => simp [AddValuation.map_zero]
  | succ k ih =>
    rw [Nat.cast_succ]
    exact le_trans (le_min ih (AddValuation.map_one (Pl.val w)).symm.le) (AddValuation.map_add _ _ _)

theorem bwA_val_int_nonneg (z : ℤ) : (0 : WithTop ℤ) ≤ Pl.val w (z : LL) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · simpa using bwA_val_nat_nonneg Pl w k
  · simpa [AddValuation.map_neg] using bwA_val_nat_nonneg Pl w k

theorem bwA_val_nat_eq_zero (s : ℕ) (hs : ¬ Pl.resChar w ∣ s) : Pl.val w (s : LL) = 0 := by
  have hp := Pl.resChar_prime w
  have hcop : Nat.Coprime (Pl.resChar w) s := (Nat.Prime.coprime_iff_not_dvd hp).mpr hs
  have hbez := Nat.gcd_eq_gcd_ab (Pl.resChar w) s
  rw [hcop.gcd_eq_one] at hbez
  have h1 : (1 : LL) = (Pl.resChar w : LL) * ((Nat.gcdA (Pl.resChar w) s : ℤ) : LL) +
      (s : LL) * ((Nat.gcdB (Pl.resChar w) s : ℤ) : LL) := by
    have := congrArg (fun z : ℤ => (z : LL)) hbez
    push_cast at this
    exact this
  have hnn := bwA_val_nat_nonneg Pl w s
  refine le_antisymm ?_ hnn
  by_contra hpos
  push_neg at hpos
  have hvp : (0 : WithTop ℤ) < Pl.val w (Pl.resChar w : LL) := by
    rw [Pl.val_resChar w]
    have := Pl.ramIdx_pos w
    first
      | exact_mod_cast this
      | exact WithTop.coe_lt_coe.mpr (by exact_mod_cast this)
  have hA := bwA_val_int_nonneg Pl w (Nat.gcdA (Pl.resChar w) s)
  have hB := bwA_val_int_nonneg Pl w (Nat.gcdB (Pl.resChar w) s)
  have h2 : (0 : WithTop ℤ) < Pl.val w ((Pl.resChar w : LL) * ((Nat.gcdA (Pl.resChar w) s : ℤ) : LL)) := by
    rw [AddValuation.map_mul]
    exact lt_of_lt_of_le hvp (le_add_of_nonneg_right hA)
  have h3 : (0 : WithTop ℤ) < Pl.val w ((s : LL) * ((Nat.gcdB (Pl.resChar w) s : ℤ) : LL)) := by
    rw [AddValuation.map_mul]
    exact lt_of_lt_of_le hpos (le_add_of_nonneg_right hB)
  have h4 := AddValuation.map_add (Pl.val w) ((Pl.resChar w : LL) * ((Nat.gcdA (Pl.resChar w) s : ℤ) : LL))
    ((s : LL) * ((Nat.gcdB (Pl.resChar w) s : ℤ) : LL))
  rw [← h1, AddValuation.map_one] at h4
  exact absurd h4 (not_le.mpr (lt_min h2 h3))

theorem bwA_val_integral_nonneg (x : LL) (hx : IsIntegral ℤ x) : (0 : WithTop ℤ) ≤ Pl.val w x := by
  classical
  by_contra hneg
  push_neg at hneg
  obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hneg)
  have hz0 : z < 0 := by
    rw [← hz] at hneg
    exact_mod_cast hneg
  obtain ⟨p, hpm, hpx⟩ := hx
  have hsum : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, ((p.coeff i : ℤ) : LL) * x ^ i := by
    rw [hpm.as_sum] at hpx
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, algebraMap_int_eq, Int.coe_castRingHom] at hpx
    exact eq_neg_of_add_eq_zero_left hpx
  have hlow : ((((p.natDegree : ℤ) - 1) * z : ℤ) : WithTop ℤ) ≤
      Pl.val w (∑ i ∈ Finset.range p.natDegree, ((p.coeff i : ℤ) : LL) * x ^ i) := by
    apply AddValuation.map_le_sum
    intro i hi
    rw [AddValuation.map_mul, AddValuation.map_pow, ← hz]
    have hi' : (i : ℤ) ≤ p.natDegree - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hc := bwA_val_int_nonneg Pl w (p.coeff i)
    calc ((((p.natDegree : ℤ) - 1) * z : ℤ) : WithTop ℤ) ≤ (((i : ℤ) * z : ℤ) : WithTop ℤ) := by
          exact_mod_cast (by nlinarith : ((p.natDegree : ℤ) - 1) * z ≤ (i : ℤ) * z)
      _ = i • (z : WithTop ℤ) := by rw [← WithTop.coe_nsmul, nsmul_eq_mul]
      _ ≤ Pl.val w ((p.coeff i : ℤ) : LL) + i • (z : WithTop ℤ) := le_add_of_nonneg_left hc
  have hxN : Pl.val w (x ^ p.natDegree) = (((p.natDegree : ℤ) * z : ℤ) : WithTop ℤ) := by
    rw [AddValuation.map_pow, ← hz, ← WithTop.coe_nsmul, nsmul_eq_mul]
  rw [hsum, AddValuation.map_neg] at hxN
  rw [hxN] at hlow
  have : ((p.natDegree : ℤ) - 1) * z ≤ (p.natDegree : ℤ) * z := by exact_mod_cast hlow
  linarith

end Val

section Weyl

variable (R : Type) [CommRing R] {r n : ℕ}

private theorem sum_C_one_mul_X_eq_X (v : Fin r × Fin n) :
    ∑ x : Fin r, MvPolynomial.C ((1 : Matrix (Fin r) (Fin r) R) v.1 x) * MvPolynomial.X (x, v.2) =
      (MvPolynomial.X v : MvPolynomial (Fin r × Fin n) R) := by
  rw [Finset.sum_eq_single v.1]
  · simp
  · intro x _ hx
    simp [Matrix.one_apply_ne (Ne.symm hx)]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem sum_C_single_mul_X_eq_ite (a b : Fin r) (c : R) (v : Fin r × Fin n) :
    ∑ x : Fin r, MvPolynomial.C (Matrix.single b a c v.1 x) * MvPolynomial.X (x, v.2) =
      if v.1 = b then MvPolynomial.C c * MvPolynomial.X (a, v.2) else (0 : MvPolynomial (Fin r × Fin n) R) := by
  rw [Finset.sum_eq_single a]
  · by_cases h : v.1 = b
    · simp [Matrix.single_apply, h]
    · simp [Matrix.single_apply, h, Ne.symm h]
  · intro x _ hx
    simp [Matrix.single_apply, Ne.symm hx]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem bwA_rowAct_elem_eq (a b : Fin r) (c : R) (f : MvPolynomial (Fin r × Fin n) R) :
    Formalism.GradedWeylDivisibility.rowAct R (1 + Matrix.single b a c) f =
      Polynomial.eval (MvPolynomial.C c) (Formalism.GradedWeylDivisibility.rowGen R a b f) := by
  apply MvPolynomial.induction_on f
  · intro x
    first
      | simp [Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.rowGen, Polynomial.algebraMap_apply]
      | simp [Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.rowGen]
  · intro p q hp hq
    simp only [map_add, Polynomial.eval_add, hp, hq]
  · intro p v hp
    simp only [map_mul, Polynomial.eval_mul, hp]
    congr 1
    simp only [Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.rowGen, MvPolynomial.aeval_X, Matrix.add_apply, map_add, add_mul,
      Finset.sum_add_distrib, sum_C_one_mul_X_eq_X, sum_C_single_mul_X_eq_ite, Polynomial.eval_add, Polynomial.eval_C]
    split_ifs <;> simp <;> exact mul_comm _ _

private theorem rowDiv_mem_weyl_of_mem (hn : n ≤ r) (ν : Fin n → ℕ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) :
    Formalism.GradedWeylDivisibility.rowDiv R a b k f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  let L : MvPolynomial (Fin r × Fin n) R →ₗ[R] MvPolynomial (Fin r × Fin n) R :=
    { toFun := fun g => Formalism.GradedWeylDivisibility.rowDiv R a b k g
      map_add' := fun x y => by simp [Formalism.GradedWeylDivisibility.rowDiv]
      map_smul' := fun t x => by simp [Formalism.GradedWeylDivisibility.rowDiv] }
  unfold Formalism.GradedWeylDivisibility.weyl at hf ⊢
  have key : Submodule.span R (Set.range fun w : List (Fin r × Fin r × ℕ) => Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) ≤
      (Submodule.span R (Set.range fun w : List (Fin r × Fin r × ℕ) =>
        Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν))).comap L := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    first
      | exact Submodule.subset_span ⟨(a, b, k) :: w, rfl⟩
      | exact Submodule.subset_span ⟨(a, b, k) :: w, by simp [Formalism.GradedWeylDivisibility.applyWord, L]⟩
  exact key hf

theorem bwA_weyl_rowAct_elem (hn : n ≤ r) (ν : Fin n → ℕ) (a b : Fin r) (c : R)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) :
    Formalism.GradedWeylDivisibility.rowAct R (1 + Matrix.single b a c) f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  rw [bwA_rowAct_elem_eq, Polynomial.eval_eq_sum_range]
  refine Submodule.sum_mem _ fun k _ => ?_
  have h1 : (Formalism.GradedWeylDivisibility.rowGen R a b f).coeff k = Formalism.GradedWeylDivisibility.rowDiv R a b k f := rfl
  rw [h1, ← map_pow, mul_comm, ← MvPolynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (rowDiv_mem_weyl_of_mem R hn ν a b k f hf)

theorem bwA_rowAct_one (f : MvPolynomial (Fin r × Fin n) R) : Formalism.GradedWeylDivisibility.rowAct R 1 f = f := by
  have h : (Formalism.GradedWeylDivisibility.rowAct R (n := n) (1 : Matrix (Fin r) (Fin r) R)) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X, AlgHom.id_apply, sum_C_one_mul_X_eq_X]
  rw [h, AlgHom.id_apply]

def bwA_elem : Set (Matrix (Fin r) (Fin r) R) := {g | ∃ (a b : Fin r) (c : R), g = 1 + Matrix.single b a c}

private theorem rowAct_mul_eq_rowAct_rowAct (g h : Matrix (Fin r) (Fin r) R) (f : MvPolynomial (Fin r × Fin n) R) :
    Formalism.GradedWeylDivisibility.rowAct R (g * h) f = Formalism.GradedWeylDivisibility.rowAct R h (Formalism.GradedWeylDivisibility.rowAct R g f) := by
  have key : (Formalism.GradedWeylDivisibility.rowAct R (n := n) (g * h)) = (Formalism.GradedWeylDivisibility.rowAct R h).comp (Formalism.GradedWeylDivisibility.rowAct R g) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Formalism.GradedWeylDivisibility.rowAct, AlgHom.comp_apply, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    first
      | exact Finset.sum_comm
      | rw [Finset.sum_comm]
  rw [key, AlgHom.comp_apply]

theorem bwA_weyl_rowAct_closure (hn : n ≤ r) (ν : Fin n → ℕ) (g : Matrix (Fin r) (Fin r) R)
    (hg : g ∈ Submonoid.closure (bwA_elem R)) (f : MvPolynomial (Fin r × Fin n) R)
    (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) : Formalism.GradedWeylDivisibility.rowAct R g f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  let S : Submonoid (Matrix (Fin r) (Fin r) R) :=
    { carrier := {g | ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν, Formalism.GradedWeylDivisibility.rowAct R g f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν}
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        intro f hf
        rw [bwA_rowAct_one]
        exact hf
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        intro f hf
        rw [rowAct_mul_eq_rowAct_rowAct]
        exact hy _ (hx f hf) }
  have hle : Submonoid.closure (bwA_elem R) ≤ S := by
    rw [Submonoid.closure_le]
    rintro x ⟨a, b, c, rfl⟩
    simp only [SetLike.mem_coe]
    intro f hf
    exact bwA_weyl_rowAct_elem R hn ν a b c f hf
  exact hle hg f hf

end Weyl

theorem bwA_rowGen_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ} (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin n) R) :
    Polynomial.map (MvPolynomial.map φ) (Formalism.GradedWeylDivisibility.rowGen R a b f) = Formalism.GradedWeylDivisibility.rowGen S a b (MvPolynomial.map φ f) := by
  apply MvPolynomial.induction_on f
  · intro x
    first
      | simp [Formalism.GradedWeylDivisibility.rowGen, Polynomial.algebraMap_apply]
      | simp [Formalism.GradedWeylDivisibility.rowGen]
  · intro p q hp hq
    simp only [map_add, Polynomial.map_add, hp, hq]
  · intro p v hp
    simp only [map_mul, Polynomial.map_mul, hp]
    congr 1
    simp only [Formalism.GradedWeylDivisibility.rowGen, MvPolynomial.aeval_X, MvPolynomial.map_X, Polynomial.map_add, Polynomial.map_C]
    split_ifs <;> simp

theorem bwA_rowDiv_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) :
    MvPolynomial.map φ (Formalism.GradedWeylDivisibility.rowDiv R a b k f) = Formalism.GradedWeylDivisibility.rowDiv S a b k (MvPolynomial.map φ f) := by
  unfold Formalism.GradedWeylDivisibility.rowDiv
  rw [← bwA_rowGen_map φ a b f, Polynomial.coeff_map]

section Grade

variable {R : Type} [CommRing R] {r n : ℕ}

def bwA_wZ (r n : ℕ) : Fin r × Fin n → (Fin r → ℤ) := fun v => Pi.single v.1 1

def bwA_del (a b : Fin r) : Fin r → ℤ := Pi.single a 1 - Pi.single b 1

def bwA_G (a b : Fin r) (p : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℤ) : Prop :=
  ∀ k : ℕ, MvPolynomial.IsWeightedHomogeneous (bwA_wZ r n) (Formalism.GradedWeylDivisibility.rowDiv R a b k p) (μ + (k : ℤ) • bwA_del a b)

theorem bwA_G_C (a b : Fin r) (c : R) : bwA_G (n := n) a b (MvPolynomial.C c) 0 := by
  intro k
  have h : Formalism.GradedWeylDivisibility.rowDiv R a b k (MvPolynomial.C c : MvPolynomial (Fin r × Fin n) R) =
      if k = 0 then MvPolynomial.C c else 0 := by
    unfold Formalism.GradedWeylDivisibility.rowDiv
    first
      | simp [Formalism.GradedWeylDivisibility.rowGen, Polynomial.algebraMap_apply, Polynomial.coeff_C]
      | simp [Formalism.GradedWeylDivisibility.rowGen, Polynomial.coeff_C]
  rw [h]
  split_ifs with hk
  · subst hk
    simpa using MvPolynomial.isWeightedHomogeneous_C (bwA_wZ r n) c
  · intro d hd
    exact absurd (MvPolynomial.coeff_zero d) hd

theorem bwA_G_X (a b : Fin r) (v : Fin r × Fin n) : bwA_G (R := R) a b (MvPolynomial.X v) (bwA_wZ r n v) := by
  intro k
  match k with
  | 0 =>
    have h : Formalism.GradedWeylDivisibility.rowDiv R a b 0 (MvPolynomial.X v : MvPolynomial (Fin r × Fin n) R) = MvPolynomial.X v := by
      unfold Formalism.GradedWeylDivisibility.rowDiv
      by_cases hv : v.1 = b <;> simp [Formalism.GradedWeylDivisibility.rowGen, hv]
    rw [h]
    simpa using MvPolynomial.isWeightedHomogeneous_X R (bwA_wZ r n) v
  | 1 =>
    by_cases hv : v.1 = b
    · have h : Formalism.GradedWeylDivisibility.rowDiv R a b 1 (MvPolynomial.X v : MvPolynomial (Fin r × Fin n) R) = MvPolynomial.X (a, v.2) := by
        unfold Formalism.GradedWeylDivisibility.rowDiv
        simp [Formalism.GradedWeylDivisibility.rowGen, hv]
      have hd : bwA_wZ r n v + ((1 : ℕ) : ℤ) • bwA_del a b = bwA_wZ r n (a, v.2) := by
        funext i
        simp only [bwA_wZ, bwA_del, hv, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Nat.cast_one, one_smul, Pi.single_apply]
        split_ifs <;> omega
      rw [h, hd]
      exact MvPolynomial.isWeightedHomogeneous_X R (bwA_wZ r n) (a, v.2)
    · have h : Formalism.GradedWeylDivisibility.rowDiv R a b 1 (MvPolynomial.X v : MvPolynomial (Fin r × Fin n) R) = 0 := by
        unfold Formalism.GradedWeylDivisibility.rowDiv
        simp [Formalism.GradedWeylDivisibility.rowGen, hv]
      rw [h]
      intro d hd
      exact absurd (MvPolynomial.coeff_zero d) hd
  | k + 2 =>
    have h : Formalism.GradedWeylDivisibility.rowDiv R a b (k + 2) (MvPolynomial.X v : MvPolynomial (Fin r × Fin n) R) = 0 := by
      unfold Formalism.GradedWeylDivisibility.rowDiv
      by_cases hv : v.1 = b <;> simp [Formalism.GradedWeylDivisibility.rowGen, hv, Polynomial.coeff_X_mul, Polynomial.coeff_C]
    rw [h]
    intro d hd
    exact absurd (MvPolynomial.coeff_zero d) hd

theorem bwA_G_add (a b : Fin r) {p q : MvPolynomial (Fin r × Fin n) R} {μ : Fin r → ℤ} (hp : bwA_G a b p μ)
    (hq : bwA_G a b q μ) : bwA_G a b (p + q) μ := by
  intro k
  have h : Formalism.GradedWeylDivisibility.rowDiv R a b k (p + q) = Formalism.GradedWeylDivisibility.rowDiv R a b k p + Formalism.GradedWeylDivisibility.rowDiv R a b k q := by
    simp [Formalism.GradedWeylDivisibility.rowDiv]
  rw [h]
  exact (hp k).add (hq k)

theorem bwA_G_mul (a b : Fin r) {p q : MvPolynomial (Fin r × Fin n) R} {μ ν : Fin r → ℤ} (hp : bwA_G a b p μ)
    (hq : bwA_G a b q ν) : bwA_G a b (p * q) (μ + ν) := by
  intro k
  have h : Formalism.GradedWeylDivisibility.rowDiv R a b k (p * q) = ((Formalism.GradedWeylDivisibility.rowGen R a b p) * (Formalism.GradedWeylDivisibility.rowGen R a b q)).coeff k := by
    unfold Formalism.GradedWeylDivisibility.rowDiv
    rw [map_mul]
  rw [h, Polynomial.coeff_mul, ← MvPolynomial.mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun x hx => ?_
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
  have hx' : x.1 + x.2 = k := by
    first
      | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      | simpa using hx
  have hdeg : μ + ν + (k : ℤ) • bwA_del a b = (μ + (x.1 : ℤ) • bwA_del a b) + (ν + (x.2 : ℤ) • bwA_del a b) := by
    rw [← hx']
    simp only [Nat.cast_add, add_smul]
    abel
  rw [hdeg]
  exact (hp x.1).mul (hq x.2)

theorem bwA_G_one (a b : Fin r) : bwA_G (R := R) (n := n) a b 1 0 := by
  simpa [MvPolynomial.C_1] using bwA_G_C (R := R) (n := n) a b (1 : R)

theorem bwA_G_pow (a b : Fin r) {p : MvPolynomial (Fin r × Fin n) R} {μ : Fin r → ℤ} (hp : bwA_G a b p μ) (j : ℕ) :
    bwA_G a b (p ^ j) (j • μ) := by
  induction j with
  | zero => simpa using bwA_G_one (R := R) (n := n) a b
  | succ j ih =>
    rw [pow_succ, succ_nsmul]
    exact bwA_G_mul a b ih hp

theorem bwA_G_monomial (a b : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : R) :
    bwA_G a b (MvPolynomial.monomial m c) (Finsupp.weight (bwA_wZ r n) m) := by
  classical
  have key : ∀ s : Finset (Fin r × Fin n), bwA_G a b (∏ v ∈ s, (MvPolynomial.X v : MvPolynomial (Fin r × Fin n) R) ^ m v)
      (∑ v ∈ s, m v • bwA_wZ r n v) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using bwA_G_one (R := R) (n := n) a b
    · intro v s hv ih
      rw [Finset.prod_insert hv, Finset.sum_insert hv]
      exact bwA_G_mul a b (bwA_G_pow a b (bwA_G_X a b v) (m v)) ih
  have h2 := bwA_G_mul a b (bwA_G_C (n := n) a b c) (key m.support)
  rw [MvPolynomial.monomial_eq]
  convert h2 using 1
  all_goals first
    | rfl
    | (rw [Finsupp.weight_apply]; simp [Finsupp.sum])
    | simp [Finsupp.prod]

theorem bwA_G_of_homog (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℤ)
    (hf : MvPolynomial.IsWeightedHomogeneous (bwA_wZ r n) f μ) : bwA_G a b f μ := by
  classical
  rw [MvPolynomial.as_sum f]
  have h0 : bwA_G a b (0 : MvPolynomial (Fin r × Fin n) R) μ := by
    intro k d hd
    simp [Formalism.GradedWeylDivisibility.rowDiv] at hd
  refine Finset.sum_induction _ (fun p => bwA_G a b p μ) (fun p q hp hq => bwA_G_add a b hp hq) h0 ?_
  intro d hd
  have hw := hf (MvPolynomial.mem_support_iff.mp hd)
  rw [← hw]
  exact bwA_G_monomial a b d _

theorem bwA_weight_cast (m : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (bwA_wZ r n) m = fun i => ((Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) m i : ℕ) : ℤ) := by
  classical
  funext i
  simp only [bwA_wZ, Formalism.GradedWeylDivisibility.rowW, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Nat.cast_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : i = v.1
  · subst h
    simp
  · simp [Pi.single_apply, h]

private theorem isWeightedHomogeneous_bwA_prod_of_forall {ι : Type} (s : Finset ι) (φ : ι → MvPolynomial (Fin r × Fin n) R) (m : ι → Fin r → ℤ)
    (h : ∀ i ∈ s, MvPolynomial.IsWeightedHomogeneous (bwA_wZ r n) (φ i) (m i)) :
    MvPolynomial.IsWeightedHomogeneous (bwA_wZ r n) (∏ i ∈ s, φ i) (∑ i ∈ s, m i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using MvPolynomial.isWeightedHomogeneous_C (bwA_wZ r n) (1 : R)
  · intro i s hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem bwA_applyWord_homog (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (w : List (Fin r × Fin r × ℕ)) :
    ∃ μ : Fin r → ℤ, MvPolynomial.IsWeightedHomogeneous (bwA_wZ r n) (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) μ := by
  classical
  have hmin : ∀ (s : ℕ) (hr : s ≤ r) (hs : s ≤ n), MvPolynomial.IsWeightedHomogeneous (bwA_wZ r n)
      (Formalism.GradedWeylDivisibility.lpMinor R (r := r) (n := n) s hr hs) (∑ p : Fin s, bwA_wZ r n (Fin.castLE hr p, Fin.castLE hs p)) := by
    intro s hr hs
    unfold Formalism.GradedWeylDivisibility.lpMinor
    rw [Matrix.det_apply, ← MvPolynomial.mem_weightedHomogeneousSubmodule]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    refine zsmul_mem ?_ _
    rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
    have h := isWeightedHomogeneous_bwA_prod_of_forall (R := R) Finset.univ
      (fun i : Fin s => (MvPolynomial.X (Fin.castLE hr (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R))
      (fun i => bwA_wZ r n (Fin.castLE hr (σ i), Fin.castLE hs i))
      (fun i _ => MvPolynomial.isWeightedHomogeneous_X R _ _)
    convert h using 1
    all_goals first
      | rfl
      | simp [Matrix.of_apply]
      | (simp only [bwA_wZ]
         exact (Equiv.sum_comp σ (fun i => (Pi.single (Fin.castLE hr i) 1 : Fin r → ℤ))).symm)
  have hhw : ∃ μ, MvPolynomial.IsWeightedHomogeneous (bwA_wZ r n) (Formalism.GradedWeylDivisibility.hw R hn ν) μ := by
    unfold Formalism.GradedWeylDivisibility.hw
    exact ⟨_, isWeightedHomogeneous_bwA_prod_of_forall _ _ _ fun s _ => (hmin _ _ _).pow _⟩
  induction w with
  | nil => simpa [Formalism.GradedWeylDivisibility.applyWord] using hhw
  | cons x w ih =>
    obtain ⟨μ, hμ⟩ := ih
    show ∃ μ, MvPolynomial.IsWeightedHomogeneous _
      (Formalism.GradedWeylDivisibility.rowDiv R x.1 x.2.1 x.2.2 (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν))) μ
    exact ⟨_, bwA_G_of_homog x.1 x.2.1 _ μ hμ x.2.2⟩

end Grade

theorem bwA_rowDeg_le {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (f : MvPolynomial (Fin r × Fin n) ℤ) (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ r n ν)
    (m : Fin r × Fin n →₀ ℕ) (hm : m ∈ f.support) (a : Fin r) :
    Formalism.GradedWeylDivisibility.rowDeg m a ≤ Formalism.GradedWeylDivisibility.rowNu (r := r) ν ⟨0, by have := a.2; omega⟩ := by
  set z : Fin r := ⟨0, by have := a.2; omega⟩ with hz
  set σ : Equiv.Perm (Fin r) := Equiv.swap z a with hσ
  set e : Fin r × Fin n → Fin r × Fin n := fun v => (σ v.1, v.2) with he_def
  have he : Function.Injective e := by
    rintro ⟨x1, x2⟩ ⟨y1, y2⟩ h
    simp only [he_def, Prod.mk.injEq] at h
    exact Prod.ext (σ.injective h.1) h.2
  set g : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun x b => if b = σ x then 1 else 0 with hg_def
  have hg : Formalism.GradedWeylDivisibility.rowAct ℤ (n := n) g = MvPolynomial.rename e := by
    apply MvPolynomial.algHom_ext
    rintro ⟨x1, x2⟩
    simp [Formalism.GradedWeylDivisibility.rowAct, hg_def, he_def, apply_ite MvPolynomial.C, ite_mul, Finset.sum_ite_eq']
  have h1 := Formalism.GradedWeylDivisibility.dualWeylRowStable ℤ r n ν g f hf
  rw [hg] at h1
  have hm' : Finsupp.mapDomain e m ∈ (MvPolynomial.rename e f).support := by
    rw [MvPolynomial.support_rename_of_injective he]; exact Finset.mem_image_of_mem _ hm
  have hd := (Formalism.GradedWeylDivisibility.dualWeylDominanceZ r n ν hn hν _ h1 _ hm').1 1
  have hsum : ∀ h : Fin r → ℕ, (∑ a' : Fin r with a'.val < 1, h a') = h z := by
    intro h
    rw [Finset.sum_filter, Finset.sum_eq_single z]
    · simp [hz]
    · intro b _ hb
      have : ¬ b.val < 1 := fun h' => hb (Fin.ext (by simp [hz]; omega))
      simp [this]
    · simp
  rw [hsum, hsum] at hd
  have hrow : Formalism.GradedWeylDivisibility.rowDeg (Finsupp.mapDomain e m) z = Formalism.GradedWeylDivisibility.rowDeg m a := by
    unfold Formalism.GradedWeylDivisibility.rowDeg
    refine Finset.sum_congr rfl fun s _ => ?_
    have : (z, s) = e (a, s) := by simp [he_def, hσ]
    rw [this, Finsupp.mapDomain_apply he]
  omega

theorem bwA_rowDeg_eq_weight {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Formalism.GradedWeylDivisibility.rowDeg m a = Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) m a := by
  classical
  unfold Formalism.GradedWeylDivisibility.rowDeg
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single a]
    · simp [Formalism.GradedWeylDivisibility.rowW]
    · intro x _ hx
      simp [Formalism.GradedWeylDivisibility.rowW, Pi.single_apply, Ne.symm hx]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro i
    simp

theorem bwA_diag_gen {K : Type} [Field K] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (hn0 : 0 < n)
    (w : List (Fin r × Fin r × ℕ)) (j : Fin r) (p : K) (hp : p ≠ 0) :
    ∃ e : ℕ, e ≤ ν ⟨0, hn0⟩ ∧
      p ^ ν ⟨0, hn0⟩ • Formalism.GradedWeylDivisibility.rowAct K (Matrix.diagonal (Function.update 1 j p⁻¹))
          (MvPolynomial.map (Int.castRingHom K) (Formalism.GradedWeylDivisibility.applyWord ℤ w (Formalism.GradedWeylDivisibility.hw ℤ hn ν))) =
        p ^ (ν ⟨0, hn0⟩ - e) • MvPolynomial.map (Int.castRingHom K) (Formalism.GradedWeylDivisibility.applyWord ℤ w (Formalism.GradedWeylDivisibility.hw ℤ hn ν)) := by
  set g := Formalism.GradedWeylDivisibility.applyWord ℤ w (Formalism.GradedWeylDivisibility.hw ℤ hn ν) with hg_def
  by_cases hg0 : g = 0
  · refine ⟨0, Nat.zero_le _, ?_⟩
    rw [hg0]; simp
  obtain ⟨m, hm⟩ : ∃ m, m ∈ g.support := by
    by_contra h
    push Not at h
    exact hg0 (MvPolynomial.support_eq_empty.1 (Finset.eq_empty_of_forall_notMem h))
  obtain ⟨μ, hμ⟩ := bwA_applyWord_homog (R := ℤ) hn ν hν w
  set μN := Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) m with hμN
  have hhom : MvPolynomial.IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) (MvPolynomial.map (Int.castRingHom K) g) μN := by
    intro m' hm'
    rw [MvPolynomial.coeff_map] at hm'
    have h1 : MvPolynomial.coeff m' g ≠ 0 := fun h => hm' (by rw [h]; simp)
    have e1 := hμ h1
    have e2 := hμ (MvPolynomial.mem_support_iff.1 hm)
    rw [bwA_weight_cast] at e1 e2
    rw [← e2] at e1
    funext i
    exact_mod_cast congrFun e1 i
  have hdw := Formalism.GradedWeylDivisibility.rowActDiagWeight K r n (Function.update 1 j p⁻¹) μN _ hhom
  have hprod : (∏ a, (Function.update (1 : Fin r → K) j p⁻¹ a) ^ μN a) = p⁻¹ ^ μN j := by
    rw [Finset.prod_eq_single j]
    · simp
    · intro b _ hb; simp [Function.update_of_ne hb]
    · simp
  have hmem : g ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ r n ν :=
    Formalism.GradedWeylDivisibility.weylLeDual ℤ r n hn ν hν (Submodule.subset_span ⟨w, rfl⟩)
  have hle := bwA_rowDeg_le hn ν hν g hmem m hm j
  rw [bwA_rowDeg_eq_weight] at hle
  have hnu : Formalism.GradedWeylDivisibility.rowNu (r := r) ν ⟨0, by have := j.2; omega⟩ = ν ⟨0, hn0⟩ := by
    unfold Formalism.GradedWeylDivisibility.rowNu; rw [dif_pos hn0]
  rw [hnu] at hle
  refine ⟨μN j, hle, ?_⟩
  rw [hdw, hprod, smul_smul]
  congr 1
  rw [inv_pow]
  exact (pow_sub₀ _ hp hle).symm

section Span

variable {K : Type} [Field K] (O : Subring K) {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)

def bwA_span : Submodule O (MvPolynomial (Fin r × Fin n) K) :=
  Submodule.span O (MvPolynomial.map (Int.castRingHom K) '' (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν : Set _))

theorem bwA_span_elem (a b : Fin r) (c : K) (hc : c ∈ O) (f : MvPolynomial (Fin r × Fin n) K)
    (hf : f ∈ bwA_span O hn ν) : Formalism.GradedWeylDivisibility.rowAct K (1 + Matrix.single b a c) f ∈ bwA_span O hn ν := by
  have key : bwA_span O hn ν ≤ (bwA_span O hn ν).comap
      ((Formalism.GradedWeylDivisibility.rowAct K (1 + Matrix.single b a c)).toLinearMap.restrictScalars O) := by
    show Submodule.span O _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    show Formalism.GradedWeylDivisibility.rowAct K (1 + Matrix.single b a c) (MvPolynomial.map (Int.castRingHom K) g) ∈ bwA_span O hn ν
    rw [bwA_rowAct_elem_eq, Polynomial.eval_eq_sum_range]
    refine Submodule.sum_mem _ fun k _ => ?_
    have h1 : (Formalism.GradedWeylDivisibility.rowGen K a b (MvPolynomial.map (Int.castRingHom K) g)).coeff k =
        MvPolynomial.map (Int.castRingHom K) (Formalism.GradedWeylDivisibility.rowDiv ℤ a b k g) :=
      (bwA_rowDiv_map (Int.castRingHom K) a b k g).symm
    rw [h1, ← map_pow, mul_comm, ← MvPolynomial.smul_eq_C_mul]
    have hmem : MvPolynomial.map (Int.castRingHom K) (Formalism.GradedWeylDivisibility.rowDiv ℤ a b k g) ∈ bwA_span O hn ν :=
      Submodule.subset_span ⟨_, rowDiv_mem_weyl_of_mem ℤ hn ν a b k g hg, rfl⟩
    exact Submodule.smul_mem _ (⟨c ^ k, pow_mem hc k⟩ : O) hmem
  exact key hf

theorem bwA_span_closure (g : Matrix (Fin r) (Fin r) K)
    (hg : g ∈ Submonoid.closure {g : Matrix (Fin r) (Fin r) K | ∃ (a b : Fin r) (c : K), c ∈ O ∧ g = 1 + Matrix.single b a c})
    (f : MvPolynomial (Fin r × Fin n) K) (hf : f ∈ bwA_span O hn ν) :
    Formalism.GradedWeylDivisibility.rowAct K g f ∈ bwA_span O hn ν := by
  let S : Submonoid (Matrix (Fin r) (Fin r) K) :=
    { carrier := {g | ∀ f ∈ bwA_span O hn ν, Formalism.GradedWeylDivisibility.rowAct K g f ∈ bwA_span O hn ν}
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        intro f hf
        rw [bwA_rowAct_one]
        exact hf
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        intro f hf
        rw [rowAct_mul_eq_rowAct_rowAct]
        exact hy _ (hx f hf) }
  have hle : Submonoid.closure {g : Matrix (Fin r) (Fin r) K | ∃ (a b : Fin r) (c : K), c ∈ O ∧ g = 1 + Matrix.single b a c} ≤ S := by
    rw [Submonoid.closure_le]
    rintro x ⟨a, b, c, hc, rfl⟩
    simp only [SetLike.mem_coe]
    intro f hf
    exact bwA_span_elem O hn ν a b c hc f hf
  exact hle hg f hf

theorem bwA_span_diag (hν : Antitone ν) (hn0 : 0 < n) (j : Fin r) (p : K) (hpO : p ∈ O) (hp : p ≠ 0)
    (f : MvPolynomial (Fin r × Fin n) K) (hf : f ∈ bwA_span O hn ν) :
    p ^ ν ⟨0, hn0⟩ • Formalism.GradedWeylDivisibility.rowAct K (Matrix.diagonal (Function.update 1 j p⁻¹)) f ∈ bwA_span O hn ν := by
  let Tk : MvPolynomial (Fin r × Fin n) K →ₗ[K] MvPolynomial (Fin r × Fin n) K :=
    (p ^ ν ⟨0, hn0⟩) • (Formalism.GradedWeylDivisibility.rowAct K (Matrix.diagonal (Function.update 1 j p⁻¹))).toLinearMap
  let Mz : MvPolynomial (Fin r × Fin n) ℤ →+ MvPolynomial (Fin r × Fin n) K :=
    (MvPolynomial.map (Int.castRingHom K)).toAddMonoidHom
  let Lz : MvPolynomial (Fin r × Fin n) ℤ →ₗ[ℤ] MvPolynomial (Fin r × Fin n) K :=
    (Tk.toAddMonoidHom.comp Mz).toIntLinearMap
  have hz : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν ≤ ((bwA_span O hn ν).restrictScalars ℤ).comap Lz := by
    show Submodule.span ℤ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    show (p ^ ν ⟨0, hn0⟩) • Formalism.GradedWeylDivisibility.rowAct K (Matrix.diagonal (Function.update 1 j p⁻¹))
      (MvPolynomial.map (Int.castRingHom K) (Formalism.GradedWeylDivisibility.applyWord ℤ w (Formalism.GradedWeylDivisibility.hw ℤ hn ν))) ∈ bwA_span O hn ν
    obtain ⟨e, _, heq⟩ := bwA_diag_gen hn ν hν hn0 w j p hp
    rw [heq]
    have hw : Formalism.GradedWeylDivisibility.applyWord ℤ w (Formalism.GradedWeylDivisibility.hw ℤ hn ν) ∈ Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν := by
      unfold Formalism.GradedWeylDivisibility.weyl
      exact Submodule.subset_span ⟨w, rfl⟩
    have hmem : MvPolynomial.map (Int.castRingHom K) (Formalism.GradedWeylDivisibility.applyWord ℤ w (Formalism.GradedWeylDivisibility.hw ℤ hn ν)) ∈ bwA_span O hn ν :=
      Submodule.subset_span ⟨_, hw, rfl⟩
    exact Submodule.smul_mem _ (⟨p ^ (ν ⟨0, hn0⟩ - e), pow_mem hpO _⟩ : O) hmem
  have hO : bwA_span O hn ν ≤ (bwA_span O hn ν).comap (Tk.restrictScalars O) := by
    show Submodule.span O _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    exact hz hg
  exact hO hf

theorem bwA_span_sandwich (hν : Antitone ν) (hn0 : 0 < n) (j : Fin r) (p : K) (hpO : p ∈ O) (hp : p ≠ 0)
    (K₁ K₂ : Matrix (Fin r) (Fin r) K)
    (h₁ : K₁ ∈ Submonoid.closure {g : Matrix (Fin r) (Fin r) K | ∃ (a b : Fin r) (c : K), c ∈ O ∧ g = 1 + Matrix.single b a c})
    (h₂ : K₂ ∈ Submonoid.closure {g : Matrix (Fin r) (Fin r) K | ∃ (a b : Fin r) (c : K), c ∈ O ∧ g = 1 + Matrix.single b a c})
    (f : MvPolynomial (Fin r × Fin n) K) (hf : f ∈ bwA_span O hn ν) :
    p ^ ν ⟨0, hn0⟩ • Formalism.GradedWeylDivisibility.rowAct K (K₁ * Matrix.diagonal (Function.update 1 j p⁻¹) * K₂) f ∈ bwA_span O hn ν := by
  rw [rowAct_mul_eq_rowAct_rowAct, rowAct_mul_eq_rowAct_rowAct]
  have h3 := bwA_span_diag O hn ν hν hn0 j p hpO hp _ (bwA_span_closure O hn ν K₁ h₁ f hf)
  have h4 := bwA_span_closure O hn ν K₂ h₂ _ h3
  rwa [map_smul] at h4

end Span

section Blocks

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

theorem substitution_rename (o : ι → Matrix (Fin N) (Fin N) ℂ) (τ : ι) (q : MvPolynomial (Fin N × Fin N) ℂ) :
    subP o (MvPolynomial.rename (Prod.mk τ) q) = MvPolynomial.rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.rowAct ℂ (o τ) q) := by
  have h : (subP o).comp (MvPolynomial.rename (Prod.mk τ)) =
      (MvPolynomial.rename (Prod.mk τ)).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (o τ)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [subP, Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.rename_X, map_sum]
  have h2 := congrArg (fun F : MvPolynomial (Fin N × Fin N) ℂ →ₐ[ℂ] MvPolynomial (ι × Fin N × Fin N) ℂ => F q) h
  simpa using h2

theorem substitution_tensor (o : ι → Matrix (Fin N) (Fin N) ℂ) (f : ι → MvPolynomial (Fin N × Fin N) ℂ) :
    subP o (Formalism.L2.Forms.ten f) = Formalism.L2.Forms.ten (fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (o τ) (f τ)) := by
  unfold Formalism.L2.Forms.ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => substitution_rename o τ (f τ)

theorem bwA_ten_update (f : ι → MvPolynomial (Fin N × Fin N) ℂ) (τv : ι) (q : MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.L2.Forms.ten (Function.update f τv q) = MvPolynomial.rename (Prod.mk τv) q *
      ∏ τ ∈ Finset.univ.erase τv, MvPolynomial.rename (Prod.mk τ) (f τ) := by
  unfold Formalism.L2.Forms.ten
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τv)]
  congr 1
  · simp [Function.update_apply]
  · exact Finset.prod_congr rfl fun τ hτ => by simp [Function.update_apply, Finset.ne_of_mem_erase hτ]

end Blocks

def bwA_Ow (D : D7) (w : D.what₂.places.Pl) : Subring ℂ := (intW D.what₂.places w).map D.what₂.embLL

open Classical in

theorem bwA_ten_intSpan (D : D7) (w : D.what₂.places.Pl) {N : ℕ} (lam : D.what₂.Tau → DomWeight N) (τv : D.what₂.Tau)
    (f : D.what₂.Tau → MvPolynomial (Fin N × Fin N) ℤ) (hf : ∀ τ, f τ ∈ delSq ℤ N (lam τ))
    (q : MvPolynomial (Fin N × Fin N) ℂ) (hq : q ∈ bwA_span (bwA_Ow D w) le_rfl (lam τv).natW)
    (r : D.what₂.LL) (hr : r ∈ intW D.what₂.places w) :
    D.what₂.embLL r • Formalism.L2.Forms.ten (Function.update (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)) τv q) ∈
      Formalism.L2.Forms.IntSpan D w lam := by
  classical
  obtain ⟨R, hR⟩ : ∃ R, ∀ Q, Formalism.L2.Forms.ten (Function.update (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)) τv Q) =
      MvPolynomial.rename (Prod.mk τv) Q * R := ⟨_, fun Q => bwA_ten_update _ τv Q⟩
  let A : Submodule (bwA_Ow D w) (MvPolynomial (Fin N × Fin N) ℂ) :=
    { carrier := {Q | ∀ r' ∈ intW D.what₂.places w,
        D.what₂.embLL r' • (MvPolynomial.rename (Prod.mk τv) Q * R) ∈ Formalism.L2.Forms.IntSpan D w lam}
      add_mem' := by
        intro Q1 Q2 h1 h2
        simp only [Set.mem_setOf_eq] at h1 h2 ⊢
        intro r' hr'
        rw [map_add, add_mul, smul_add]
        exact add_mem (h1 r' hr') (h2 r' hr')
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        intro r' _
        rw [map_zero, zero_mul, smul_zero]
        exact zero_mem _
      smul_mem' := by
        rintro ⟨o, ho⟩ Q hQ
        simp only [Set.mem_setOf_eq] at hQ ⊢
        intro r' hr'
        obtain ⟨s, hs, rfl⟩ := Subring.mem_map.mp ho
        show D.what₂.embLL r' • (MvPolynomial.rename (Prod.mk τv) (D.what₂.embLL s • Q) * R) ∈ _
        rw [map_smul, smul_mul_assoc, smul_smul, ← map_mul]
        exact hQ _ (mul_mem hr' hs) }
  have hle : bwA_span (bwA_Ow D w) le_rfl (lam τv).natW ≤ A := by
    show Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    show ∀ r' ∈ intW D.what₂.places w, D.what₂.embLL r' •
      (MvPolynomial.rename (Prod.mk τv) (MvPolynomial.map (Int.castRingHom ℂ) g) * R) ∈ Formalism.L2.Forms.IntSpan D w lam
    intro r' hr'
    have e : (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (Function.update f τv g τ)) =
        Function.update (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)) τv (MvPolynomial.map (Int.castRingHom ℂ) g) := by
      funext τ
      by_cases h : τ = τv
      · subst h
        simp
      · simp [Function.update_apply, h]
    rw [← hR, ← e]
    apply AddSubgroup.subset_closure
    refine ⟨r', Function.update f τv g, hr', fun τ => ?_, rfl⟩
    by_cases h : τ = τv
    · subst h
      rw [Function.update_apply, if_pos rfl]
      simp only [delSq]
      exact hg
    · rw [Function.update_apply, if_neg h]
      exact hf τ
  have hq' := hle hq
  rw [hR]
  exact hq' r hr

open Classical in

theorem bwA_intSpan_subP (D : D7) (w : D.what₂.places.Pl) {N : ℕ} (lam : D.what₂.Tau → DomWeight N) (τv : D.what₂.Tau)
    (o : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) (ho : ∀ τ, τ ≠ τv → o τ = 1) (c : ℂ)
    (hB : ∀ g ∈ delSq ℤ N (lam τv),
      c • Formalism.GradedWeylDivisibility.rowAct ℂ (o τv) (MvPolynomial.map (Int.castRingHom ℂ) g) ∈
        bwA_span (bwA_Ow D w) le_rfl (lam τv).natW)
    (P : MvPolynomial (D.what₂.Tau × Fin N × Fin N) ℂ) (hP : P ∈ Formalism.L2.Forms.IntSpan D w lam) :
    c • subP o P ∈ Formalism.L2.Forms.IntSpan D w lam := by
  let φ : MvPolynomial (D.what₂.Tau × Fin N × Fin N) ℂ →+ MvPolynomial (D.what₂.Tau × Fin N × Fin N) ℂ :=
    (c • (subP o).toLinearMap).toAddMonoidHom
  have hle : Formalism.L2.Forms.IntSpan D w lam ≤ (Formalism.L2.Forms.IntSpan D w lam).comap φ := by
    show AddSubgroup.closure _ ≤ _
    rw [AddSubgroup.closure_le]
    rintro _ ⟨r, f, hr, hf, rfl⟩
    show c • subP o (D.what₂.embLL r • Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))) ∈
      Formalism.L2.Forms.IntSpan D w lam
    rw [map_smul, substitution_tensor, smul_comm]
    have hten : c • Formalism.L2.Forms.ten (fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (o τ) (MvPolynomial.map (Int.castRingHom ℂ) (f τ))) =
        Formalism.L2.Forms.ten (Function.update (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)) τv
          (c • Formalism.GradedWeylDivisibility.rowAct ℂ (o τv) (MvPolynomial.map (Int.castRingHom ℂ) (f τv)))) := by
      have e1 := bwA_ten_update (fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (o τ) (MvPolynomial.map (Int.castRingHom ℂ) (f τ))) τv
        (Formalism.GradedWeylDivisibility.rowAct ℂ (o τv) (MvPolynomial.map (Int.castRingHom ℂ) (f τv)))
      rw [Function.update_eq_self] at e1
      rw [e1, bwA_ten_update, map_smul, smul_mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun τ hτ => ?_
      simp only [ho τ (Finset.ne_of_mem_erase hτ), bwA_rowAct_one]
    rw [hten]
    exact bwA_ten_intSpan D w lam τv f hf _ (hB _ (hf τv)) r hr
  exact hle hP

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

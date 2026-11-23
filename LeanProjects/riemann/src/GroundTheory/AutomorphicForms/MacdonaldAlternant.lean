import Mathlib
import GroundTheory.AutomorphicForms.MacdonaldRecursion

noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open AddMonoidAlgebra Finset

variable {n : ℕ}

variable (n) in

def antisymm : LaurentRing n →ₗ[ℂ] LaurentRing n where
  toFun p := ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • permAct σ p
  map_add' p q := by
    simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [map_smul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_comm]

theorem antisymm_apply (p : LaurentRing n) :
    antisymm n p = ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • permAct σ p := rfl

theorem permAct_permAct (σ τ : Equiv.Perm (Fin n)) (p : LaurentRing n) :
    permAct σ (permAct τ p) = permAct (σ * τ) p := by
  rw [permAct_mul]
  rfl

theorem antisymm_permAct (τ : Equiv.Perm (Fin n)) (p : LaurentRing n) :
    antisymm n (permAct τ p) = Equiv.Perm.sign τ • antisymm n p := by
  rw [antisymm_apply, antisymm_apply, Finset.smul_sum]
  simp only [permAct_permAct]
  refine Fintype.sum_equiv (Equiv.mulRight τ) _ _ fun σ => ?_
  simp only [Equiv.coe_mulRight, smul_smul]
  congr 1
  rw [Equiv.Perm.sign_mul, mul_comm (Equiv.Perm.sign σ), ← mul_assoc, Int.units_mul_self, one_mul]

theorem antisymm_eq_zero_of_swap {i j : Fin n} (hij : i ≠ j) {p : LaurentRing n}
    (h : permAct (Equiv.swap i j) p = p) : antisymm n p = 0 := by
  have := antisymm_permAct (Equiv.swap i j) p
  rw [h, Equiv.Perm.sign_swap hij] at this
  simp only [Units.neg_smul, one_smul] at this
  set a := antisymm n p
  have h2 : (2 : ℂ) • a = 0 := by
    rw [two_smul]
    calc a + a = -a + a := by rw [← this]
      _ = 0 := neg_add_cancel a
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

theorem antisymm_mul_of_symm {q : LaurentRing n} (hq : ∀ σ, permAct σ q = q) (p : LaurentRing n) :
    antisymm n (q * p) = q * antisymm n p := by
  rw [antisymm_apply, antisymm_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, hq, mul_smul_comm]

def alternant (μ : Fin n → ℤ) : LaurentRing n := antisymm n (monomial μ)

theorem permAct_monomial (σ : Equiv.Perm (Fin n)) (μ : Fin n → ℤ) :
    permAct σ (monomial μ) = monomial (μ ∘ σ.symm) :=
  permAct_single σ μ 1

theorem alternant_eq_zero {μ : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) (h : μ i = μ j) :
    alternant μ = 0 := by
  refine antisymm_eq_zero_of_swap hij ?_
  rw [permAct_monomial, Equiv.symm_swap]
  congr 1
  funext x
  simp only [Function.comp_apply, Equiv.swap_apply_def]
  split_ifs with h1 h2
  · rw [h1, h]
  · rw [h2, h]
  · rfl

theorem monomial_add (μ ν : Fin n → ℤ) : monomial (μ + ν) = monomial μ * monomial ν := by
  simp only [monomial, single_mul_single, mul_one]

theorem permAct_monomial_const (c : ℤ) (σ : Equiv.Perm (Fin n)) :
    permAct σ (monomial fun _ => c) = monomial fun _ => c := by
  rw [permAct_monomial]
  rfl

theorem alternant_add_const (μ : Fin n → ℤ) (c : ℤ) :
    alternant (μ + fun _ => c) = monomial (fun _ => c) * alternant μ := by
  rw [alternant, alternant, monomial_add, mul_comm, antisymm_mul_of_symm (permAct_monomial_const c)]

theorem alternant_eq_det (μ : Fin n → ℤ) :
    alternant μ = (Matrix.of fun a b : Fin n => monomial (Pi.single a (μ b))).det := by
  rw [alternant, antisymm_apply, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  simp only [Matrix.of_apply, monomial]
  rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one, permAct_single]
  congr 1
  funext x
  simp only [Function.comp_apply, Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_eq_single (σ.symm x)]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (by rw [h, Equiv.symm_apply_apply])
  · intro h
    exact absurd (Finset.mem_univ _) h

variable (n) in

def staircase : Fin n → ℤ := fun i => (n : ℤ) - 1 - i

theorem staircase_injective : Function.Injective (staircase n) := by
  intro i j h
  simp only [staircase] at h
  exact Fin.ext (by omega)

abbrev varL (a : Fin n) : LaurentRing n := monomial (Pi.single a 1)

theorem monomial_single_natCast (a : Fin n) (m : ℕ) :
    monomial (Pi.single a (m : ℤ)) = varL a ^ m := by
  simp only [varL, monomial, single_pow, one_pow]
  congr 1
  funext x
  simp only [Pi.smul_apply, Pi.single_apply, nsmul_eq_mul]
  split_ifs <;> simp

open Polynomial in

def rootPoly (n : ℕ) : (LaurentRing n)[X] := ∏ a : Fin n, (X - C (varL a))

open Polynomial in
theorem rootPoly_monic : (rootPoly n).Monic :=
  monic_prod_of_monic _ _ fun a _ => monic_X_sub_C _

open Polynomial in
theorem natDegree_rootPoly : (rootPoly n).natDegree = n := by
  rw [rootPoly, natDegree_prod_of_monic _ _ fun a _ => monic_X_sub_C _]
  simp

open Polynomial in
theorem eval_rootPoly (a : Fin n) : (rootPoly n).eval (varL a) = 0 := by
  rw [rootPoly, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)

open Polynomial in

def remCoeff (m k : ℕ) : LaurentRing n := ((X ^ m : (LaurentRing n)[X]) %ₘ rootPoly n).coeff k

open Polynomial in

theorem pow_eq_sum_remCoeff (hn : 0 < n) (a : Fin n) (m : ℕ) :
    varL a ^ m = ∑ k : Fin n, remCoeff (n := n) m k * varL a ^ (k : ℕ) := by
  have hne : rootPoly n ≠ 1 := by
    intro h
    have := natDegree_rootPoly (n := n)
    rw [h, natDegree_one] at this
    omega
  have hdeg : ((X ^ m : (LaurentRing n)[X]) %ₘ rootPoly n).natDegree < n := by
    have := natDegree_modByMonic_lt (X ^ m : (LaurentRing n)[X]) rootPoly_monic hne
    rwa [natDegree_rootPoly] at this
  have h1 : (X ^ m : (LaurentRing n)[X]).eval (varL a) =
      ((X ^ m : (LaurentRing n)[X]) %ₘ rootPoly n).eval (varL a) := by
    conv_lhs => rw [← modByMonic_add_div (X ^ m : (LaurentRing n)[X]) (rootPoly n)]
    rw [eval_add, eval_mul, eval_rootPoly, zero_mul, add_zero]
  rw [eval_pow, eval_X, eval_eq_sum_range' hdeg, Finset.sum_range] at h1
  rw [h1]
  rfl

def vdm : Matrix (Fin n) (Fin n) (LaurentRing n) := Matrix.of fun a k => varL a ^ (k : ℕ)

def remMat (m : Fin n → ℕ) : Matrix (Fin n) (Fin n) (LaurentRing n) :=
  Matrix.of fun k b => remCoeff (m b) k

theorem alternant_natCast_eq (hn : 0 < n) (m : Fin n → ℕ) :
    alternant (fun b => (m b : ℤ)) = vdm.det * (remMat m).det := by
  rw [alternant_eq_det, ← Matrix.det_mul]
  congr 1
  refine Matrix.ext fun a b => ?_
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply, vdm, remMat]
  rw [monomial_single_natCast, pow_eq_sum_remCoeff hn a (m b)]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

open Polynomial in
theorem remMat_staircase (hn : 0 < n) :
    remMat (fun b : Fin n => n - 1 - (b : ℕ)) = Fin.revPerm.permMatrix (LaurentRing n) := by
  ext k b
  simp only [remMat, Matrix.of_apply, remCoeff, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Fin.revPerm_apply]
  have hlt : (X ^ (n - 1 - (b : ℕ)) : (LaurentRing n)[X]).degree < (rootPoly n).degree := by
    rw [degree_X_pow, degree_eq_natDegree rootPoly_monic.ne_zero, natDegree_rootPoly]
    exact_mod_cast (show n - 1 - (b : ℕ) < n by omega)
  rw [(modByMonic_eq_self_iff rootPoly_monic).2 hlt, coeff_X_pow]
  by_cases h : (k : ℕ) = n - 1 - (b : ℕ)
  · rw [if_pos h, if_pos]
    exact Fin.ext (by simp [Fin.val_rev]; omega)
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    rw [← h']
    simp [Fin.val_rev]
    omega

theorem staircase_eq_natCast :
    staircase n = fun b : Fin n => ((n - 1 - (b : ℕ) : ℕ) : ℤ) := by
  funext b
  simp only [staircase]
  have := b.2
  omega

theorem exists_alternant_eq_mul (μ : Fin n → ℤ) :
    ∃ q, alternant μ = alternant (staircase n) * q := by
  rcases n.eq_zero_or_pos with hn | hn
  · subst hn
    exact ⟨1, by rw [mul_one]; congr 1; funext i; exact i.elim0⟩

  set s : LaurentRing n := ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : LaurentRing n)
  have hs : s * s = 1 := by
    simp only [s]
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have hδ : alternant (staircase n) = vdm.det * s := by
    rw [staircase_eq_natCast, alternant_natCast_eq hn, remMat_staircase hn, Matrix.det_permutation]
  have hV : vdm.det = alternant (staircase n) * s := by
    rw [hδ, mul_assoc, hs, mul_one]

  set c : ℤ := ∑ i, |μ i|
  have hc : ∀ i, 0 ≤ μ i + c := by
    intro i
    have := Finset.single_le_sum (f := fun i => |μ i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have := neg_abs_le (μ i)
    simp only [c]
    linarith
  have hshift : (μ + fun _ => c) = fun b => (((μ b + c).toNat : ℕ) : ℤ) := by
    funext b
    simp only [Pi.add_apply]
    rw [Int.toNat_of_nonneg (hc b)]
  have h1 := alternant_add_const μ c
  rw [hshift, alternant_natCast_eq hn, hV] at h1
  refine ⟨monomial (fun _ => -c) * s * (remMat fun b => (μ b + c).toNat).det, ?_⟩
  have hinv : monomial (fun _ : Fin n => -c) * monomial (fun _ => c) = 1 := by
    rw [← monomial_add]
    simp only [Pi.add_def, neg_add_cancel]
    rfl
  calc alternant μ = monomial (fun _ : Fin n => -c) * (monomial (fun _ => c) * alternant μ) := by
        rw [← mul_assoc, hinv, one_mul]
    _ = _ := by rw [← h1]; ring

theorem exists_antisymm_eq_mul (p : LaurentRing n) :
    ∃ q, antisymm n p = alternant (staircase n) * q := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨qx, hqx⟩ := hx
    obtain ⟨qy, hqy⟩ := hy
    exact ⟨qx + qy, by rw [map_add, hqx, hqy, mul_add]⟩
  | single μ c =>
    obtain ⟨q, hq⟩ := exists_alternant_eq_mul μ
    refine ⟨c • q, ?_⟩
    have : (single μ c : LaurentRing n) = c • monomial μ := by
      simp [monomial, smul_single']
    rw [this, map_smul, ← alternant, hq, mul_smul_comm]

theorem coeff_alternant_staircase :
    (alternant (staircase n)).coeff (staircase n) = 1 := by
  rw [alternant, antisymm_apply, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [permAct_monomial]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · rw [show (Equiv.symm (1 : Equiv.Perm (Fin n))) = 1 from rfl]
    simp [monomial, AddMonoidAlgebra.coeff_single]
  · intro σ _ hσ
    rw [Units.smul_def, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, monomial,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg, smul_zero]
    intro h
    apply hσ
    refine Equiv.ext fun x => ?_
    have := congrFun h x
    simp only [Function.comp_apply] at this
    have := staircase_injective this
    rw [Equiv.symm_apply_eq] at this
    exact this.symm
  · simp

theorem alternant_staircase_ne_zero : alternant (staircase n) ≠ 0 := by
  intro h
  have := coeff_alternant_staircase (n := n)
  rw [h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
  exact zero_ne_one this

def altQuot (p : LaurentRing n) : LaurentRing n := (exists_antisymm_eq_mul p).choose

theorem alternant_mul_altQuot (p : LaurentRing n) :
    alternant (staircase n) * altQuot p = antisymm n p :=
  (exists_antisymm_eq_mul p).choose_spec.symm

theorem altQuot_eq_of_mul {p q : LaurentRing n} (h : alternant (staircase n) * q = antisymm n p) :
    altQuot p = q :=
  mul_left_cancel₀ alternant_staircase_ne_zero ((alternant_mul_altQuot p).trans h.symm)

theorem altQuot_add (p q : LaurentRing n) : altQuot (p + q) = altQuot p + altQuot q :=
  altQuot_eq_of_mul (by rw [mul_add, alternant_mul_altQuot, alternant_mul_altQuot, map_add])

theorem altQuot_sum {ι : Type*} (s : Finset ι) (f : ι → LaurentRing n) :
    altQuot (∑ i ∈ s, f i) = ∑ i ∈ s, altQuot (f i) :=
  altQuot_eq_of_mul (by rw [Finset.mul_sum, map_sum]; simp only [alternant_mul_altQuot])

theorem altQuot_smul (c : ℂ) (p : LaurentRing n) : altQuot (c • p) = c • altQuot p :=
  altQuot_eq_of_mul (by rw [mul_smul_comm, alternant_mul_altQuot, map_smul])

theorem altQuot_mul_of_symm {q : LaurentRing n} (hq : ∀ σ, permAct σ q = q) (p : LaurentRing n) :
    altQuot (q * p) = q * altQuot p :=
  altQuot_eq_of_mul (by
    rw [antisymm_mul_of_symm hq, ← alternant_mul_altQuot p]
    ring)

theorem altQuot_eq_zero_of_swap {i j : Fin n} (hij : i ≠ j) {p : LaurentRing n}
    (h : permAct (Equiv.swap i j) p = p) : altQuot p = 0 :=
  altQuot_eq_of_mul (by rw [mul_zero, antisymm_eq_zero_of_swap hij h])

def esymmL (n r : ℕ) : LaurentRing n := ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, monomial (lamS S)

theorem lamS_comp_symm (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    lamS S ∘ σ.symm = lamS (S.map σ.toEmbedding) := by
  funext x
  simp only [Function.comp_apply, lamS_apply, Finset.mem_map_equiv]

theorem permAct_esymmL (r : ℕ) (σ : Equiv.Perm (Fin n)) : permAct σ (esymmL n r) = esymmL n r := by
  rw [esymmL, map_sum]
  simp only [permAct_monomial, lamS_comp_symm]
  refine Finset.sum_nbij' (fun S => S.map σ.toEmbedding) (fun S => S.map σ.symm.toEmbedding)
    ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro S hS
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.card_map] at hS ⊢
    exact hS
  · intro S hS
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.card_map] at hS ⊢
    exact hS
  · intro S _
    ext x
    simp [Finset.mem_map_equiv]
  · intro S _
    ext x
    simp [Finset.mem_map_equiv]

theorem esymmL_mul_monomial (r : ℕ) (l : Fin n → ℤ) :
    esymmL n r * monomial l = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      monomial (l + lamS S) := by
  rw [esymmL, Finset.sum_mul]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [add_comm, monomial_add]

theorem esymmL_mul_altQuot (r : ℕ) (l : Fin n → ℤ) (g : LaurentRing n) :
    esymmL n r * altQuot (monomial l * g) = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      altQuot (monomial (l + lamS S) * g) := by
  rw [← altQuot_mul_of_symm (permAct_esymmL r), ← mul_assoc, esymmL_mul_monomial, Finset.sum_mul,
    altQuot_sum]

def schur (l : Fin n → ℤ) : LaurentRing n := altQuot (monomial (l + staircase n))

theorem alternant_mul_schur (l : Fin n → ℤ) :
    alternant (staircase n) * schur l = alternant (l + staircase n) :=
  alternant_mul_altQuot _

theorem esymmL_mul_schur (r : ℕ) (l : Fin n → ℤ) :
    esymmL n r * schur l = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, schur (l + lamS S) := by
  have h := esymmL_mul_altQuot r l (monomial (staircase n))
  simp only [← monomial_add] at h
  rw [schur, h]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [schur, add_right_comm]

theorem schur_eq_zero_of_ascent {μ : Fin n → ℤ} {i j : Fin n} (hij : (j : ℕ) = i + 1)
    (hμ : μ j = μ i + 1) : schur μ = 0 := by
  refine mul_left_cancel₀ (alternant_staircase_ne_zero (n := n)) ?_
  rw [alternant_mul_schur, mul_zero]
  refine alternant_eq_zero (i := i) (j := j) (fun h => by rw [h] at hij; omega) ?_
  simp only [Pi.add_apply, staircase, hμ]
  push_cast [hij]
  ring

def hlFactor (n : ℕ) (t : ℂ) : LaurentRing n :=
  ∏ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2), (varL p.1 - t • varL p.2)

def hlR (t : ℂ) (l : Fin n → ℤ) : LaurentRing n := altQuot (monomial l * hlFactor n t)

theorem esymmL_mul_hlR (t : ℂ) (r : ℕ) (l : Fin n → ℤ) :
    esymmL n r * hlR t l = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, hlR t (l + lamS S) :=
  esymmL_mul_altQuot r l _

theorem altQuot_sub_smul (t : ℂ) (p q : LaurentRing n) :
    altQuot (p - t • q) = altQuot p - t • altQuot q := by
  rw [sub_eq_add_neg, ← neg_smul, altQuot_add, altQuot_smul, neg_smul, ← sub_eq_add_neg]

theorem permAct_varL (σ : Equiv.Perm (Fin n)) (a : Fin n) : permAct σ (varL a) = varL (σ a) := by
  rw [varL, permAct_monomial]
  congr 1
  funext x
  simp only [Function.comp_apply, Pi.single_apply, Equiv.symm_apply_eq]

theorem swap_lt_swap {i j a b : Fin n} (hij : (j : ℕ) = i + 1) (hab : a < b)
    (hne : ¬(a = i ∧ b = j)) : Equiv.swap i j a < Equiv.swap i j b := by
  have hv : ∀ x : Fin n, ((Equiv.swap i j x : Fin n) : ℕ) =
      if (x : ℕ) = i then (j : ℕ) else if (x : ℕ) = j then (i : ℕ) else (x : ℕ) := by
    intro x
    rw [Equiv.swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff]
  rw [Fin.lt_def, hv, hv]
  rw [Fin.lt_def] at hab
  have : ¬((a : ℕ) = i ∧ (b : ℕ) = j) := fun h => hne ⟨Fin.ext h.1, Fin.ext h.2⟩
  split_ifs <;> omega

theorem hlR_swap (t : ℂ) {μ : Fin n → ℤ} {i j : Fin n} (hij : (j : ℕ) = i + 1)
    (hμ : μ j = μ i + 1) : hlR t μ = t • hlR t (μ ∘ Equiv.swap i j) := by
  classical
  set s := Equiv.swap i j with hs
  have hij' : i ≠ j := fun h => by rw [h] at hij; omega
  have hlt : i < j := Fin.lt_def.2 (by omega)
  set P := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2) with hP
  set fac : Fin n × Fin n → LaurentRing n := fun p => varL p.1 - t • varL p.2 with hfac
  have hmem : (i, j) ∈ P := by simp [hP, hlt]
  set D' := ∏ p ∈ P.erase (i, j), fac p with hD'
  have hD : hlFactor n t = fac (i, j) * D' := by
    rw [hD', Finset.mul_prod_erase P fac hmem]
    rfl

  have hsD' : permAct s D' = D' := by
    rw [hD', map_prod]
    refine Finset.prod_nbij' (fun p => (s p.1, s p.2)) (fun p => (s p.1, s p.2)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_erase] at hp ⊢
      obtain ⟨hne, hpP⟩ := hp
      simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hpP ⊢
      have hne' : ¬(p.1 = i ∧ p.2 = j) := fun h => hne (Prod.ext h.1 h.2)
      refine ⟨fun h => ?_, swap_lt_swap hij hpP hne'⟩
      simp only [Prod.mk.injEq] at h
      have h1 : p.1 = j := by
        have := congrArg s h.1
        rwa [hs, Equiv.swap_apply_self, Equiv.swap_apply_left] at this
      have h2 : p.2 = i := by
        have := congrArg s h.2
        rwa [hs, Equiv.swap_apply_self, Equiv.swap_apply_right] at this
      rw [h1, h2] at hpP
      exact absurd hlt (not_lt.2 hpP.le)
    · intro p hp
      rw [Finset.mem_erase] at hp ⊢
      obtain ⟨hne, hpP⟩ := hp
      simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hpP ⊢
      have hne' : ¬(p.1 = i ∧ p.2 = j) := fun h => hne (Prod.ext h.1 h.2)
      refine ⟨fun h => ?_, swap_lt_swap hij hpP hne'⟩
      simp only [Prod.mk.injEq] at h
      have h1 : p.1 = j := by
        have := congrArg s h.1
        rwa [hs, Equiv.swap_apply_self, Equiv.swap_apply_left] at this
      have h2 : p.2 = i := by
        have := congrArg s h.2
        rwa [hs, Equiv.swap_apply_self, Equiv.swap_apply_right] at this
      rw [h1, h2] at hpP
      exact absurd hlt (not_lt.2 hpP.le)
    · intro p _
      simp [hs, Equiv.swap_apply_self]
    · intro p _
      simp [hs, Equiv.swap_apply_self]
    · intro p _
      simp only [hfac, map_sub, map_smul, permAct_varL]

  have hkey : monomial (μ ∘ s) * varL j = monomial μ * varL i := by
    rw [varL, varL, ← monomial_add, ← monomial_add]
    congr 1
    funext x
    simp only [Pi.add_apply, Function.comp_apply, Pi.single_apply, hs, Equiv.swap_apply_def]
    split_ifs with h1 h2 h3 h4 h5 <;> simp_all
  have hss : μ ∘ s ∘ s = μ := by
    funext x
    simp [hs, Equiv.swap_apply_self]
  have hY : permAct s ((monomial μ - t • monomial (μ ∘ s)) * fac (i, j)) =
      (monomial μ - t • monomial (μ ∘ s)) * fac (i, j) := by
    simp only [hfac, map_mul, map_sub, map_smul, permAct_varL]
    rw [permAct_monomial, permAct_monomial,
      show (s.symm : Equiv.Perm (Fin n)) = s from Equiv.symm_swap i j, Function.comp_assoc, hss,
      hs, Equiv.swap_apply_left, Equiv.swap_apply_right, ← hs]
    simp only [Algebra.smul_def]
    linear_combination (1 - algebraMap ℂ (LaurentRing n) t ^ 2) * hkey
  have hzero : altQuot ((monomial μ - t • monomial (μ ∘ s)) * hlFactor n t) = 0 := by
    rw [hD, ← mul_assoc]
    refine altQuot_eq_zero_of_swap hij' ?_
    rw [map_mul, hY, hsD']
  rw [sub_mul, smul_mul_assoc, altQuot_sub_smul] at hzero
  rw [hlR, hlR]
  exact sub_eq_zero.1 hzero

end Spherical

end GroundTheory.Automorphic

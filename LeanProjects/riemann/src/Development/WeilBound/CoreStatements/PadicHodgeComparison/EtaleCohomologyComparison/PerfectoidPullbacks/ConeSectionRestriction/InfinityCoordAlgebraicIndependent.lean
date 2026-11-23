import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K R : Type} [Field K] [CommRing R] [Algebra K R] {n : ℕ}

def u0 (t : Fin (n + 1) → Rˣ) : Fin (n + 1) → Rˣ :=
  Fin.cases (t 0)⁻¹ fun j => t j.succ * (t 0)⁻¹

def infinityDerivation (t : Fin (n + 1) → Rˣ) (D : Fin (n + 1) → Derivation K R R) : Fin (n + 1) → Derivation K R R :=
  Fin.cases (-((t 0 : R) • ∑ k, (t k : R) • D k)) fun j => (t 0 : R) • D j.succ

theorem derivation_sum_apply {ι : Type} (s : Finset ι) (f : ι → Derivation K R R) (x : R) :
    (∑ k ∈ s, f k) x = ∑ k ∈ s, f k x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

theorem infinityDerivation_coord (t : Fin (n + 1) → Rˣ) (D : Fin (n + 1) → Derivation K R R)
    (hD : ∀ k j, D k (t j) = if k = j then 1 else 0) (j l : Fin (n + 1)) :
    infinityDerivation t D j (u0 t l) = if j = l then 1 else 0 := by
  have huv : (t 0 : R) * (((t 0)⁻¹ : Rˣ) : R) = 1 := (t 0).mul_inv
  have hinv : ∀ k, D k (((t 0)⁻¹ : Rˣ) : R) = -(((t 0)⁻¹ : Rˣ) : R) ^ 2 * D k (t 0) := fun k => by
    rw [Derivation.leibniz_of_mul_eq_one (D k) (Units.inv_mul (t 0)), smul_eq_mul]
  induction j using Fin.cases <;> induction l using Fin.cases
  · simp only [infinityDerivation, u0, Fin.cases_zero, Derivation.neg_apply, Derivation.smul_apply, derivation_sum_apply, smul_eq_mul, hinv, hD]
    simp
    linear_combination ((t 0 : R) * (((t 0)⁻¹ : Rˣ) : R) + 1) * huv
  · simp only [infinityDerivation, u0, Fin.cases_zero, Fin.cases_succ, Derivation.neg_apply, Derivation.smul_apply,
      derivation_sum_apply, smul_eq_mul, Units.val_mul, Derivation.leibniz, hinv, hD]
    simp [show ∀ i : Fin n, (0 : Fin (n + 1)) = i.succ ↔ False from fun i => ⟨fun h => Fin.succ_ne_zero i h.symm, False.elim⟩]
    linear_combination ((t _ : R) * ((t 0 : R) * (((t 0)⁻¹ : Rˣ) : R) + 1)) * huv
  · simp [infinityDerivation, u0, Derivation.smul_apply, smul_eq_mul, hinv, hD, (Fin.succ_ne_zero _)]
  · simp only [infinityDerivation, u0, Fin.cases_succ, Derivation.smul_apply, smul_eq_mul, Units.val_mul, Derivation.leibniz,
      hinv, hD]
    simp [Fin.succ_ne_zero]

theorem jacobian_infinityDerivation (t : Fin (n + 1) → Rˣ) (D : Fin (n + 1) → Derivation K R R) (B : Subalgebra K R) :
    ∀ y ∈ jacS B D id, ∃ y' ∈ jacS B (infinityDerivation t D) id, y = -(((t 0)⁻¹ : Rˣ) : R) ^ (n + 2) * y' := by
  set C : Matrix (Fin (n + 1)) (Fin (n + 1)) R := Matrix.of fun j k =>
    Fin.cases (fun k => -((t 0 : R) * t k)) (fun j k => if j.succ = k then (t 0 : R) else 0) j k with hC
  have hCdet : C.det = -(t 0 : R) ^ (n + 2) := by
    rw [Matrix.det_of_isUpperTriangular]
    · rw [Fin.prod_univ_succ]
      simp [hC, Finset.prod_const, pow_succ]
      ring
    · intro i k hki
      induction i using Fin.cases with
      | zero => exact absurd hki (Fin.not_lt_zero k)
      | succ i =>
        simp only [id] at hki
        simp only [hC, Matrix.of_apply, Fin.cases_succ]
        rw [if_neg (show i.succ ≠ k from fun h => by subst h; exact lt_irrefl _ hki)]
  have hM : ∀ bs : Fin (n + 1) → B, (Matrix.of fun k l => infinityDerivation t D (id k) ((bs l : R))) =
      C * Matrix.of fun k l => D (id k) ((bs l : R)) := by
    intro bs; ext j l
    simp only [Matrix.of_apply, id, Matrix.mul_apply, hC]
    induction j using Fin.cases with
    | zero => simp [infinityDerivation, derivation_sum_apply, Finset.mul_sum, mul_assoc]
    | succ j => simp [infinityDerivation]
  have huv : (t 0 : R) * (((t 0)⁻¹ : Rˣ) : R) = 1 := (t 0).mul_inv
  intro y hy
  have key : jacS B D id ≤ (jacS B (infinityDerivation t D) id).map (AddMonoidHom.mulLeft (-(((t 0)⁻¹ : Rˣ) : R) ^ (n + 2))) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨b, bs, rfl⟩
    refine ⟨(b : R) * (Matrix.of fun k l => infinityDerivation t D (id k) ((bs l : R))).det,
      AddSubgroup.subset_closure ⟨b, bs, rfl⟩, ?_⟩
    simp only [AddMonoidHom.coe_mulLeft, hM, Matrix.det_mul, hCdet]
    have hp : (((t 0)⁻¹ : Rˣ) : R) ^ (n + 2) * (t 0 : R) ^ (n + 2) = 1 := by
      rw [← mul_pow, mul_comm, huv, one_pow]
    linear_combination ((b : R) * (Matrix.of fun k l => D (id k) ((bs l : R))).det) * hp
  obtain ⟨y', hy', rfl⟩ := key hy
  exact ⟨y', hy', rfl⟩

section torus

theorem tpow_add' {d : ℕ} (t : Fin d → Rˣ) (m m' : Fin d → ℤ) : tpow t (m + m') = tpow t m * tpow t m' := by
  simp [tpow, zpow_add, Finset.prod_mul_distrib]

theorem tpow_single {d : ℕ} (t : Fin d → Rˣ) (k : Fin d) (z : ℤ) : tpow t (Pi.single k z) = ((t k ^ z : Rˣ) : R) := by
  unfold tpow
  rw [Fintype.prod_eq_single k (fun j hj => by simp [Pi.single_apply, hj])]
  simp

theorem tpow_mem {d : ℕ} (t : Fin d → Rˣ) (S : Finset (Fin (d + 1))) {m : Fin d → ℤ} (hm : m ∈ expS S) :
    tpow t m ∈ torusS K t S :=
  Algebra.subset_adjoin ⟨m, hm, rfl⟩

theorem torusS_le_span {d : ℕ} (t : Fin d → Rˣ) (S : Finset (Fin (d + 1))) :
    (torusS K t S : Set R) ⊆ Submodule.span K (tpow t '' expS S) := by
  let M : Submonoid R :=
    { carrier := tpow t '' expS S
      one_mem' := ⟨0, ⟨fun k _ => le_refl 0, fun _ => by simp⟩, by simp [tpow]⟩
      mul_mem' := by
        rintro _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
        refine ⟨m + m', ⟨fun k hk => ?_, fun h0 => ?_⟩, tpow_add' t m m'⟩
        · have := hm.1 k hk; have := hm'.1 k hk; simp only [Pi.add_apply]; omega
        · have := hm.2 h0; have := hm'.2 h0; simp only [Pi.add_apply, Finset.sum_add_distrib]; omega }
  intro x hx
  have hx' : x ∈ Subalgebra.toSubmodule (Algebra.adjoin K (tpow t '' expS S)) := hx
  rw [Algebra.adjoin_eq_span] at hx'
  exact Submodule.span_mono (Submonoid.closure_le (S := M).2 le_rfl) hx'

theorem mem_exponentSet_zero_iff {n : ℕ} (m : Fin (n + 1) → ℤ) :
    m ∈ expS (Finset.univ.erase (0 : Fin (n + 2))) ↔ ∑ k, m k ≤ 0 := by
  simp [expS, Fin.succ_ne_zero]

def infinityExponent {n : ℕ} (e : Fin (n + 1) → ℕ) : Fin (n + 1) → ℤ := Fin.cons (-(∑ i, (e i : ℤ))) fun j => (e j.succ : ℤ)

theorem sum_u0Exp {n : ℕ} (e : Fin (n + 1) → ℕ) : ∑ k, infinityExponent e k = -(e 0 : ℤ) := by
  simp [infinityExponent, Fin.sum_univ_succ]

theorem infinityCoord_prod_pow (t : Fin (n + 1) → Rˣ) (e : Fin (n + 1) → ℕ) :
    (((∏ i, u0 t i ^ e i : Rˣ)) : R) = tpow t (infinityExponent e) := by
  unfold tpow infinityExponent
  congr 1
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [u0, Fin.cases_zero, Fin.cases_succ, Fin.cons_zero, Fin.cons_succ, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, zpow_natCast, Fin.sum_univ_succ, zpow_neg]
  rw [← Nat.cast_sum, ← Nat.cast_add, zpow_natCast, pow_add, mul_inv]
  simp only [inv_pow]
  ac_rfl

end torus

theorem infinityCoord_monomial_eq (t : Fin (n + 1) → Rˣ) (N : ℕ) (α : Fin (n + 1) → ℕ) (hα : ∑ i, α i ≤ N) :
    (t 0 : R) ^ N * ∏ i, (u0 t i : R) ^ α i =
      ∏ i, (t i : R) ^ (Fin.cons (N - ∑ i, α i) (fun j => α j.succ) : Fin (n + 1) → ℕ) i := by
  have huv : (t 0 : R) * (((t 0)⁻¹ : Rˣ) : R) = 1 := (t 0).mul_inv
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [u0, Fin.cases_zero, Fin.cases_succ, Fin.cons_zero, Fin.cons_succ, Units.val_mul, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [Fin.sum_univ_succ] at hα ⊢
  obtain ⟨k, hk⟩ : ∃ k, N = k + α 0 + ∑ j : Fin n, α j.succ := ⟨N - (α 0 + ∑ j : Fin n, α j.succ), by omega⟩
  have hk' : N - (α 0 + ∑ j : Fin n, α j.succ) = k := by omega
  rw [hk', hk]
  calc (t 0 : R) ^ (k + α 0 + ∑ j : Fin n, α j.succ) *
        ((((t 0)⁻¹ : Rˣ) : R) ^ α 0 * ((∏ j : Fin n, (t j.succ : R) ^ α j.succ) *
          (((t 0)⁻¹ : Rˣ) : R) ^ ∑ j : Fin n, α j.succ))
      = (t 0 : R) ^ k * (∏ j : Fin n, (t j.succ : R) ^ α j.succ) *
          ((t 0 : R) * (((t 0)⁻¹ : Rˣ) : R)) ^ α 0 *
          ((t 0 : R) * (((t 0)⁻¹ : Rˣ) : R)) ^ ∑ j : Fin n, α j.succ := by ring
    _ = _ := by rw [huv, one_pow, one_pow, mul_one, mul_one]

theorem infinityCoord_mem_torus (t : Fin (n + 1) → Rˣ) (j : Fin (n + 1)) :
    (u0 t j : R) ∈ torusS K t (Finset.univ.erase 0) := by
  have h := infinityCoord_prod_pow t (Pi.single j 1)
  rw [Fintype.prod_eq_single j (fun i hi => by simp [Pi.single_apply, hi])] at h
  simp only [Pi.single_eq_same, pow_one] at h
  rw [h]
  exact tpow_mem t _ ((mem_exponentSet_zero_iff _).2 (by rw [sum_u0Exp]; exact neg_nonpos.2 (Nat.cast_nonneg _)))

theorem infinityCoord_inv_mem (t : Fin (n + 1) → Rˣ) (j : Fin n) :
    (((u0 t j.succ)⁻¹ : Rˣ) : R) ∈ torusS K t (Finset.univ.erase 0) := by
  have h : (((u0 t j.succ)⁻¹ : Rˣ) : R) = tpow t (Pi.single 0 1 + Pi.single j.succ (-1)) := by
    rw [tpow_add', tpow_single, tpow_single, ← Units.val_mul]
    congr 1
    simp [u0, mul_comm]
  rw [h]
  exact tpow_mem t _ ((mem_exponentSet_zero_iff _).2 (by simp [Finset.sum_add_distrib]))

theorem infinityCoord_algebraicIndependent (t : Fin (n + 1) → Rˣ) (ht : AlgebraicIndependent K fun k => (t k : R)) :
    Function.Injective (MvPolynomial.aeval fun k => (u0 t k : R) : MvPolynomial (Fin (n + 1)) K →ₐ[K] R) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro f hf
  set N := f.totalDegree
  let deg : (Fin (n + 1) →₀ ℕ) → ℕ := fun α => ∑ i, α i
  have hdeg : ∀ α ∈ f.support, deg α ≤ N := by
    intro α hα
    have := MvPolynomial.le_totalDegree hα
    refine le_trans (le_of_eq ?_) this
    simp only [deg]
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  let h : (Fin (n + 1) →₀ ℕ) → (Fin (n + 1) →₀ ℕ) := fun α =>
    Finsupp.equivFunOnFinite.symm (Fin.cons (N - deg α) (fun j => α j.succ))
  have hinj : ∀ α ∈ f.support, ∀ β ∈ f.support, h α = h β → α = β := by
    intro α hα β hβ hab
    have h0 := DFunLike.congr_fun hab 0
    have hs : ∀ j : Fin n, α j.succ = β j.succ := fun j => by
      simpa [h] using DFunLike.congr_fun hab j.succ
    simp only [h, deg, Fin.sum_univ_succ] at h0
    rw [Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_equivFunOnFinite_symm, Fin.cons_zero, Fin.cons_zero] at h0
    have ha := hdeg α hα; have hb := hdeg β hβ
    simp only [deg, Fin.sum_univ_succ] at ha hb
    have hsum : ∑ j : Fin n, α j.succ = ∑ j : Fin n, β j.succ := Finset.sum_congr rfl fun j _ => hs j
    ext i
    induction i using Fin.cases with
    | zero => omega
    | succ j => exact hs j
  let g : MvPolynomial (Fin (n + 1)) K := ∑ α ∈ f.support, MvPolynomial.monomial (h α) (f.coeff α)
  have hu : ∀ α : Fin (n + 1) →₀ ℕ, MvPolynomial.aeval (fun k => (u0 t k : R)) (MvPolynomial.monomial α (1 : K)) =
      ∏ i, (u0 t i : R) ^ α i := fun α => by
    rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have htm : ∀ α : Fin (n + 1) →₀ ℕ, MvPolynomial.aeval (fun k => (t k : R)) (MvPolynomial.monomial α (1 : K)) =
      ∏ i, (t i : R) ^ α i := fun α => by
    rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have hg : MvPolynomial.aeval (fun k => (t k : R)) g = (t 0 : R) ^ N * MvPolynomial.aeval (fun k => (u0 t k : R)) f := by
    conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff f]
    simp only [g, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [← mul_one (f.coeff α), ← smul_eq_mul, ← MvPolynomial.smul_monomial, ← MvPolynomial.smul_monomial,
      map_smul, map_smul, hu, htm, mul_smul_comm, infinityCoord_monomial_eq t N α (hdeg α hα)]
    rfl
  rw [hf, mul_zero] at hg
  have hg0 : g = 0 := ht (hg.trans (map_zero _).symm)
  ext β
  rw [MvPolynomial.coeff_zero]
  by_contra hβ
  have hβ' : β ∈ f.support := MvPolynomial.mem_support_iff.2 hβ
  have := congrArg (MvPolynomial.coeff (h β)) hg0
  rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_sum, Finset.sum_eq_single β] at this
  · rw [MvPolynomial.coeff_monomial, if_pos rfl] at this
    exact hβ this
  · intro α hα hne
    rw [MvPolynomial.coeff_monomial, if_neg (fun e => hne (hinj α hα β hβ' e))]
  · intro hn; exact absurd hβ' hn

theorem infinityCoord_localization (t : Fin (n + 1) → Rˣ) (ht : AlgebraicIndependent K fun k => (t k : R)) :
    Function.Injective (MvPolynomial.aeval (fun k => (⟨u0 t k, infinityCoord_mem_torus t k⟩ : torusS K t (Finset.univ.erase 0))) :
      MvPolynomial (Fin (n + 1)) K →ₐ[K] torusS K t (Finset.univ.erase 0)) ∧
    ∀ a : torusS K t (Finset.univ.erase 0), ∃ f g : MvPolynomial (Fin (n + 1)) K,
      IsUnit (MvPolynomial.aeval (fun k => (⟨u0 t k, infinityCoord_mem_torus t k⟩ : torusS K t (Finset.univ.erase 0))) g) ∧
      a * MvPolynomial.aeval (fun k => (⟨u0 t k, infinityCoord_mem_torus t k⟩ : torusS K t (Finset.univ.erase 0))) g =
        MvPolynomial.aeval (fun k => (⟨u0 t k, infinityCoord_mem_torus t k⟩ : torusS K t (Finset.univ.erase 0))) f := by
  classical
  have hval : ∀ p : MvPolynomial (Fin (n + 1)) K,
      ((MvPolynomial.aeval (fun k => (⟨u0 t k, infinityCoord_mem_torus t k⟩ : torusS K t (Finset.univ.erase 0))) p :
        torusS K t (Finset.univ.erase 0)) : R) = MvPolynomial.aeval (fun k => (u0 t k : R)) p := fun p =>
    DFunLike.congr_fun (MvPolynomial.comp_aeval (fun k => (⟨u0 t k, infinityCoord_mem_torus t k⟩ : torusS K t (Finset.univ.erase 0)))
      (torusS K t (Finset.univ.erase 0)).val) p
  refine ⟨fun p q hpq => infinityCoord_algebraicIndependent t ht (by rw [← hval, ← hval, hpq]), ?_⟩
  have key : ∀ x ∈ Submodule.span K (tpow t '' expS (Finset.univ.erase (0 : Fin (n + 2)))),
      ∃ (f : MvPolynomial (Fin (n + 1)) K) (e : Fin n → ℕ),
        x * ∏ j, (u0 t j.succ : R) ^ e j = MvPolynomial.aeval (fun k => (u0 t k : R)) f := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, rfl⟩ := hx
      have hm' := (mem_exponentSet_zero_iff m).1 hm
      refine ⟨MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm
          (Fin.cons (Int.toNat (-∑ k, m k)) fun j => Int.toNat (m j.succ) : Fin (n + 1) → ℕ)) 1,
        fun j => Int.toNat (-m j.succ), ?_⟩
      rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      have e1 : ∏ j : Fin n, (u0 t j.succ : R) ^ Int.toNat (-m j.succ) =
          (((∏ i, u0 t i ^ (Fin.cons 0 (fun j => Int.toNat (-m j.succ)) : Fin (n + 1) → ℕ) i : Rˣ)) : R) := by
        rw [Fin.prod_univ_succ]; simp
      have e2 : ∏ i, (u0 t i : R) ^ (Finsupp.equivFunOnFinite.symm
          (Fin.cons (Int.toNat (-∑ k, m k)) fun j => Int.toNat (m j.succ) : Fin (n + 1) → ℕ)) i =
          (((∏ i, u0 t i ^ (Fin.cons (Int.toNat (-∑ k, m k)) fun j => Int.toNat (m j.succ) : Fin (n + 1) → ℕ) i : Rˣ))
            : R) := by
        simp
      rw [e1, e2, infinityCoord_prod_pow, infinityCoord_prod_pow, ← tpow_add']
      congr 1
      have h1 : ∑ j : Fin n, ((Int.toNat (m j.succ) : ℕ) : ℤ) - ∑ j : Fin n, ((Int.toNat (-m j.succ) : ℕ) : ℤ) =
          ∑ j : Fin n, m j.succ := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => Int.toNat_sub_toNat_neg _
      have h2 : ∑ k, m k = m 0 + ∑ j : Fin n, m j.succ := Fin.sum_univ_succ _
      have h4 : ((Int.toNat (-∑ k, m k) : ℕ) : ℤ) = -∑ k, m k := Int.toNat_of_nonneg (by linarith)
      funext i
      induction i using Fin.cases with
      | zero =>
        rw [h2] at h4
        simp only [infinityExponent, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.add_apply]
        push_cast
        linarith
      | succ j =>
        simp only [infinityExponent, Fin.cons_succ, Pi.add_apply]
        omega
    | zero => exact ⟨0, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨f1, e1, h1⟩ := hx
      obtain ⟨f2, e2, h2⟩ := hy
      refine ⟨f1 * ∏ j : Fin n, MvPolynomial.X j.succ ^ e2 j + f2 * ∏ j : Fin n, MvPolynomial.X j.succ ^ e1 j,
        e1 + e2, ?_⟩
      simp only [map_add, map_mul, map_prod, map_pow, MvPolynomial.aeval_X, Pi.add_apply, pow_add,
        Finset.prod_mul_distrib]
      rw [← h1, ← h2]; ring
    | smul c x _ hx =>
      obtain ⟨f, e, h⟩ := hx
      exact ⟨c • f, e, by rw [map_smul, ← h, smul_mul_assoc]⟩
  intro a
  obtain ⟨f, e, h⟩ := key a.1 (torusS_le_span t _ a.2)
  refine ⟨f, ∏ j : Fin n, MvPolynomial.X j.succ ^ e j, ?_, ?_⟩
  · rw [map_prod]
    refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun j _ => ?_)
    rw [map_pow, MvPolynomial.aeval_X]
    refine IsUnit.pow _ (IsUnit.of_mul_eq_one ⟨_, infinityCoord_inv_mem t j⟩ (Subtype.ext ?_))
    simp
  · apply Subtype.ext
    rw [Subalgebra.coe_mul, hval, hval, ← h]
    simp [map_prod]

theorem infinityCoord_span_residue (t : Fin (n + 1) → Rˣ) :
    ∀ a ∈ torusS K t (Finset.univ.erase 0), (((t 0)⁻¹ : Rˣ) : R) ^ (n + 2) * a ∈
      Submodule.span K (tpow t '' {m | ∑ k, m k < -((n : ℤ) + 1)}) := by
  intro a ha
  have hc : (((t 0)⁻¹ : Rˣ) : R) ^ (n + 2) = tpow t (Pi.single 0 (-((n : ℤ) + 2))) := by
    rw [tpow_single, ← Units.val_pow_eq_pow_val]
    congr 1
  have key : Submodule.span K (tpow t '' expS (Finset.univ.erase (0 : Fin (n + 2)))) ≤
      (Submodule.span K (tpow t '' {m | ∑ k, m k < -((n : ℤ) + 1)})).comap
        (LinearMap.mulLeft K ((((t 0)⁻¹ : Rˣ) : R) ^ (n + 2))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨m, hm, rfl⟩
    have hm' := (mem_exponentSet_zero_iff m).1 hm
    refine Submodule.subset_span ⟨m + Pi.single 0 (-((n : ℤ) + 2)), ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib]
      simp
      linarith
    · rw [tpow_add', ← hc, LinearMap.mulLeft_apply, mul_comm]
  exact key (torusS_le_span t _ ha)

theorem infinityCoord_span_residue_ne (t : Fin (n + 1) → Rˣ) :
    ∀ a ∈ torusS K t (Finset.univ.erase 0), (((t 0)⁻¹ : Rˣ) : R) ^ (n + 2) * a ∈
      Submodule.span K (tpow t '' {m | m ≠ fun _ => -1}) := by
  intro a ha
  refine Submodule.span_mono (Set.image_mono ?_) (infinityCoord_span_residue t a ha)
  intro m hm heq
  subst heq
  simp at hm

end CrystallineSemistableComparison.Pb

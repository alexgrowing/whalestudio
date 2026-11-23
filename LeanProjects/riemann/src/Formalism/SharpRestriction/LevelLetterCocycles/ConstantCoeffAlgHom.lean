import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.NumberTheory.Padics.MahlerBasis

noncomputable section

open PowerSeries

namespace Formalism.MainNotions.N.WachTwistedLattices.PowerSeriesTruncation

variable {O : Type*} [CommRing O]

theorem coeff_X_pow_mul_lt {n d : ℕ} (h : d < n) (p : PowerSeries O) :
    coeff d (X ^ n * p) = 0 := by
  first
  | rw [PowerSeries.coeff_X_pow_mul', if_neg (not_le.mpr h)]
  | (rw [mul_comm, PowerSeries.coeff_mul_X_pow', if_neg (not_le.mpr h)])
  | simp [PowerSeries.coeff_X_pow_mul', not_le.mpr h]

theorem coeff_pow_mul_lt {Y : PowerSeries O} (hY : constantCoeff Y = 0) {n d : ℕ} (h : d < n)
    (p : PowerSeries O) : coeff d (Y ^ n * p) = 0 := by
  obtain ⟨Z, rfl⟩ := PowerSeries.X_dvd_iff.mpr hY
  rw [mul_pow, mul_assoc]
  exact coeff_X_pow_mul_lt h _

theorem trunc_decomp (a : PowerSeries O) (k : ℕ) :
    ∃ b, a = (trunc k a : PowerSeries O) + X ^ k * b := by
  have hd : (X : PowerSeries O) ^ k ∣ a - (trunc k a : PowerSeries O) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm, sub_self]
  obtain ⟨b, hb⟩ := hd
  exact ⟨b, by rw [← hb]; ring⟩

theorem algHom_coe (ψ : PowerSeries O →ₐ[O] PowerSeries O) (p : Polynomial O) :
    ψ (p : PowerSeries O) = Polynomial.aeval (ψ X) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.coe_add, map_add, hp, hq, map_add]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X, map_mul,
      map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    congr 1
    first
    | exact ψ.commutes c
    | (rw [← ψ.commutes c]; rfl)
    | simp [PowerSeries.algebraMap_eq]

private theorem natDegree_trunc_lt_of_pos (a : PowerSeries O) {N : ℕ} (hN : 0 < N) :
    (trunc N a).natDegree < N := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  first
  | exact PowerSeries.natDegree_trunc_lt a N'
  | exact Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun i hi => by
      rw [PowerSeries.coeff_trunc, if_neg (by omega)])

private theorem coeff_algHom_eq_sum_range_of_lt (σ : PowerSeries O →ₐ[O] PowerSeries O)
    (hσ : constantCoeff (σ X) = 0) (a : PowerSeries O) {m N : ℕ} (hN : m < N) :
    coeff m (σ a) = ∑ n ∈ Finset.range N, coeff n a * coeff m (σ X ^ n) := by
  obtain ⟨b, hb⟩ := trunc_decomp a N
  have hdeg := natDegree_trunc_lt_of_pos a (lt_of_le_of_lt (Nat.zero_le m) hN)
  rw [show σ a = σ ((trunc N a : PowerSeries O) + X ^ N * b) from congrArg σ hb, map_add, map_mul,
    map_pow, algHom_coe, map_add,
    coeff_pow_mul_lt hσ hN, add_zero,
    Polynomial.aeval_eq_sum_range' hdeg, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  first
  | rw [map_smul, smul_eq_mul, PowerSeries.coeff_trunc, if_pos hi]
  | rw [PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_trunc, if_pos hi]
  | simp [PowerSeries.coeff_trunc, hi]

private theorem hasSubst_of_constantCoeff_eq_zero_level_letter_cocycles {Y : PowerSeries O}
    (hY : constantCoeff Y = 0) : PowerSeries.HasSubst Y := by
  first
  | exact PowerSeries.HasSubst.of_constantCoeff_zero' hY
  | exact PowerSeries.HasSubst.of_constantCoeff_zero hY
  | exact ⟨1, by rw [pow_one]; exact hY⟩

private theorem coeff_subst_eq_sum_range_of_lt {Y : PowerSeries O} (hY : constantCoeff Y = 0)
    (a : PowerSeries O) {m N : ℕ} (hN : m < N) :
    coeff m (a.subst Y) = ∑ n ∈ Finset.range N, coeff n a * coeff m (Y ^ n) := by
  have hs := hasSubst_of_constantCoeff_eq_zero_level_letter_cocycles hY
  let σ : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom hs
  have h1 : ∀ f : PowerSeries O, σ f = f.subst Y := fun f => by
    first
    | rfl
    | simp [σ, PowerSeries.coe_substAlgHom]
  have h2 : σ X = Y := by
    rw [h1]
    first
    | exact PowerSeries.subst_X hs
    | simp [hs]
  have h3 := coeff_algHom_eq_sum_range_of_lt σ (by rw [h2]; exact hY) a hN
  rw [h2, h1] at h3
  exact h3

theorem algHom_eq_subst (ψ : PowerSeries O →ₐ[O] PowerSeries O)
    (hψ : constantCoeff (ψ X) = 0) (a : PowerSeries O) : ψ a = a.subst (ψ X) := by
  ext m
  rw [coeff_algHom_eq_sum_range_of_lt ψ hψ a (Nat.lt_succ_self m),
    coeff_subst_eq_sum_range_of_lt hψ a (Nat.lt_succ_self m)]

def qn (Y Z : PowerSeries O) (n : ℕ) : PowerSeries O :=
  ∑ i ∈ Finset.range n, Y ^ i * Z ^ (n - 1 - i)

theorem coeff_qn {Y Z : PowerSeries O} (hY : constantCoeff Y = 0) (hZ : constantCoeff Z = 0)
    {n j : ℕ} (h : j + 1 < n) : coeff j (qn Y Z n) = 0 := by
  obtain ⟨Y', rfl⟩ := PowerSeries.X_dvd_iff.mpr hY
  obtain ⟨Z', rfl⟩ := PowerSeries.X_dvd_iff.mpr hZ
  unfold qn
  rw [map_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mem_range] at hi
  have e : n - 1 = i + (n - 1 - i) := by omega
  have hprod : (X * Y') ^ i * (X * Z') ^ (n - 1 - i) = X ^ (n - 1) * (Y' ^ i * Z' ^ (n - 1 - i)) := by
    generalize n - 1 - i = k at e ⊢
    rw [e]
    ring
  rw [hprod]
  exact coeff_X_pow_mul_lt (by omega) _

theorem subst_sub_subst_dvd {Y Z : PowerSeries O} (hY : constantCoeff Y = 0)
    (hZ : constantCoeff Z = 0) (a : PowerSeries O) : (Y - Z) ∣ a.subst Y - a.subst Z := by
  classical
  have hYZ : ∀ n, (Y - Z) * qn Y Z n = Y ^ n - Z ^ n := fun n => by
    unfold qn
    rw [mul_comm]
    first
    | exact geom_sum₂_mul Y Z n
    | exact (Commute.all Y Z).geom_sum₂_mul n
  have stab : ∀ q M, q + 2 ≤ M →
      ∑ n ∈ Finset.range M, coeff n a * coeff q (qn Y Z n) =
        ∑ n ∈ Finset.range (q + 2), coeff n a * coeff q (qn Y Z n) := by
    intro q M hM
    symm
    refine Finset.sum_subset (fun x hx => by rw [Finset.mem_range] at hx ⊢; omega) fun n _ hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    rw [coeff_qn hY hZ (by omega), mul_zero]
  refine ⟨PowerSeries.mk fun q =>
    ∑ n ∈ Finset.range (q + 2), coeff n a * coeff q (qn Y Z n), ?_⟩
  ext m
  symm
  have hm : m < m + 2 := by omega
  rw [map_sub, PowerSeries.coeff_mul, coeff_subst_eq_sum_range_of_lt hY a hm,
    coeff_subst_eq_sum_range_of_lt hZ a hm, ← Finset.sum_sub_distrib]
  have h1 : ∀ n, coeff n a * coeff m (Y ^ n) - coeff n a * coeff m (Z ^ n) =
      ∑ p ∈ Finset.antidiagonal m, coeff p.1 (Y - Z) * (coeff n a * coeff p.2 (qn Y Z n)) := by
    intro n
    have e := congrArg (coeff m) (hYZ n)
    rw [map_sub, PowerSeries.coeff_mul] at e
    rw [← mul_sub, ← e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [Finset.sum_congr rfl fun n _ => h1 n]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [PowerSeries.coeff_mk, ← Finset.mul_sum,
    stab p.2 (m + 2) (by rw [Finset.mem_antidiagonal] at hp; omega)]

end Formalism.MainNotions.N.WachTwistedLattices.PowerSeriesTruncation

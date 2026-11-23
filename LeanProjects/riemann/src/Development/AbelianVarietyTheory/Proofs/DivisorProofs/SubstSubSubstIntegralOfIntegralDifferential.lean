import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem exists_sub_eq_p_mul_of_constantCoeff_eq {x y : WittVector p k}
    (h : WittVector.constantCoeff x = WittVector.constantCoeff y) : ∃ z, x - y = p * z := by
  by_cases hxy : x - y = 0
  · exact ⟨0, by rw [hxy, mul_zero]⟩
  obtain ⟨m, z, hz, hxyz⟩ := WittVector.exists_eq_pow_p_mul (x - y) hxy
  rcases m with _ | m
  · exfalso; apply hz
    have h1 := congrArg WittVector.constantCoeff hxyz
    rw [map_sub, h, sub_self, pow_zero, one_mul] at h1
    exact h1.symm
  · exact ⟨p ^ m * z, by rw [hxyz, pow_succ]; ring⟩

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem prod_sub_prod_divisible_lemma_2 {σ τ : Type} (c : _root_.GlobalTheory.Katz.Fr p k)
    (U V : σ → MvPowerSeries τ (WittVector p k)) (e : σ → ℕ) (S : Finset σ)
    (h : ∀ i ∈ S, ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (U i ^ e i - V i ^ e i) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y) :
    ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (∏ i ∈ S, U i ^ e i - ∏ i ∈ S, V i ^ e i) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert i S hi ih =>
    obtain ⟨Y1, hY1⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨Y2, hY2⟩ := h i (Finset.mem_insert_self i S)
    refine ⟨U i ^ e i * Y1 + Y2 * ∏ j ∈ S, V j ^ e j, ?_⟩
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    simp only [Algebra.smul_def, map_sub, map_mul, map_add, map_pow, map_prod] at hY1 hY2 ⊢
    linear_combination
      (MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (U i)) ^ e i * hY1 +
      (∏ j ∈ S, (MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (V j)) ^ e j) * hY2

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem exists_choose_mul_p_pow_mul_eq_p_mul (c : _root_.GlobalTheory.Katz.Fr p k) (m : WittVector p k)
    {n : ℕ} (hc : (n : _root_.GlobalTheory.Katz.Fr p k) * c = algebraMap (WittVector p k) _ m)
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    ∃ t : WittVector p k, c * ((n.choose j : _root_.GlobalTheory.Katz.Fr p k) * (p : _root_.GlobalTheory.Katz.Fr p k) ^ j) =
      algebraMap (WittVector p k) _ (p * t) := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨e, j', hj', hjeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : j ≠ 0) p hp.ne_one
  have hj'0 : j' ≠ 0 := by rintro rfl; simp at hj'
  have hej : e < j := by
    have h1 : p ^ e ≤ j := by rw [hjeq]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hj'0)
    exact lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt) h1
  obtain ⟨q, rfl⟩ : ∃ q, j = q + e + 1 := ⟨j - e - 1, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hunit : IsUnit (j' : WittVector p k) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    have h2 : (j' : WittVector p k).coeff 0 = (j' : k) :=
      map_natCast (WittVector.constantCoeff (p := p) (R := k)) j'
    rw [h2]
    exact (CharP.cast_eq_zero_iff k p j').not.2 hj'
  obtain ⟨s, hs⟩ := hunit.exists_right_inv
  refine ⟨m * (n'.choose (q + e) : WittVector p k) * (p : WittVector p k) ^ q * s, ?_⟩
  set ι := algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)
  have hs' : (j' : _root_.GlobalTheory.Katz.Fr p k) * ι s = 1 := by
    rw [← map_natCast ι, ← map_mul, hs, map_one]
  have hjK : ((q + e + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) = (p : _root_.GlobalTheory.Katz.Fr p k) ^ e * j' := by
    rw [hjeq]; push_cast; ring
  have hchoose : ((n' + 1).choose (q + e + 1) : _root_.GlobalTheory.Katz.Fr p k) * ((q + e + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) =
      ((n' + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k) := by
    have := Nat.add_one_mul_choose_eq n' (q + e)
    rw [← Nat.cast_mul, ← Nat.cast_mul, this]
  have hj0 : ((q + e + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) ≠ 0 := by
    rw [hjK]
    have hinj : Function.Injective ι := IsFractionRing.injective _ _
    refine mul_ne_zero (pow_ne_zero _ ?_) ?_
    · rw [← map_natCast ι]; exact (map_ne_zero_iff ι hinj).2 (WittVector.p_nonzero p k)
    · rw [← map_natCast ι]; exact (map_ne_zero_iff ι hinj).2 hunit.ne_zero
  apply mul_right_cancel₀ hj0
  simp only [map_mul, map_pow, map_natCast]
  linear_combination (c * (p : _root_.GlobalTheory.Katz.Fr p k) ^ (q + e + 1)) * hchoose +
    ((p : _root_.GlobalTheory.Katz.Fr p k) ^ (q + e + 1) * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k)) * hc -
    ((p : _root_.GlobalTheory.Katz.Fr p k) * ι m * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k) *
      (p : _root_.GlobalTheory.Katz.Fr p k) ^ q * ι s) * hjK -
    ((p : _root_.GlobalTheory.Katz.Fr p k) ^ (q + e + 1) * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k) * ι m) * hs'

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem map_algebraMap_smul' {τ : Type} (a : WittVector p k) (Y : MvPowerSeries τ (WittVector p k)) :
    MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (a • Y) =
      algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) a •
        MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
  ext β
  simp only [MvPowerSeries.coeff_map, map_smul, smul_eq_mul, map_mul]

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem map_add_p_mul_pow_sub_pow_eq_p_smul {τ : Type} (c : _root_.GlobalTheory.Katz.Fr p k) (m : WittVector p k)
    {n : ℕ} (hc : (n : _root_.GlobalTheory.Katz.Fr p k) * c = algebraMap (WittVector p k) _ m)
    (V H : MvPowerSeries τ (WittVector p k)) :
    ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      ((V + (p : MvPowerSeries τ (WittVector p k)) * H) ^ n - V ^ n) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
  rw [add_pow, Finset.sum_range_succ, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one,
    mul_one, add_sub_cancel_right, map_sum, Finset.smul_sum]
  have key : ∀ j ∈ Finset.range n, ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k))) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
    intro j hj
    rw [Finset.mem_range] at hj
    obtain ⟨t, ht⟩ := exists_choose_mul_p_pow_mul_eq_p_mul c m hc (n - j) (by omega) (by omega)
    rw [Nat.choose_symm (by omega)] at ht
    refine ⟨t • (V ^ j * H ^ (n - j)), ?_⟩
    have e1 : V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k)) =
        ((n.choose j * p ^ (n - j) : ℕ) : WittVector p k) • (V ^ j * H ^ (n - j)) := by
      rw [Algebra.smul_def, map_natCast]; push_cast; ring
    rw [e1, map_algebraMap_smul', map_algebraMap_smul', smul_smul, smul_smul, map_natCast]
    congr 1
    rw [← map_mul, ← ht]; push_cast; ring
  have hsum : ∀ S : Finset ℕ, (∀ j ∈ S, ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k))) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y) →
      ∃ Y, ∑ j ∈ S, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k))) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
    intro S hS
    classical
    induction S using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert j S hj ih =>
      obtain ⟨Y1, hY1⟩ := ih fun i hi => hS i (Finset.mem_insert_of_mem hi)
      obtain ⟨Y2, hY2⟩ := hS j (Finset.mem_insert_self j S)
      exact ⟨Y2 + Y1, by rw [Finset.sum_insert hj, hY1, hY2, map_add, smul_add]⟩
  exact hsum _ key

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in

theorem _root_.GlobalTheory.Katz.subst_sub_subst_mem_intBy : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u v : σ → MvPowerSeries (τ) (_root_.GlobalTheory.Katz.Fr p k)) (w : σ → MvPowerSeries τ k) (f : MvPowerSeries (σ) (_root_.GlobalTheory.Katz.Fr p k)), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, _root_.GlobalTheory.Katz.Red p (u i) (w i)) → (∀ i, _root_.GlobalTheory.Katz.Red p (v i) (w i)) → f ∈ _root_.GlobalTheory.Katz.quasiInt p k σ → subst u f - subst v f ∈ _root_.GlobalTheory.Katz.intBy p k τ p := by
  intro p _ k _ _ _ σ τ _ u v w f hu0 hv0 hu hv hf
  classical
  choose a ha using fun i β => hu i β
  choose b hb using fun i β => hv i β
  choose hh hhh using fun i β =>
    exists_sub_eq_p_mul_of_constantCoeff_eq ((ha i β).2.trans (hb i β).2.symm)
  let U : σ → MvPowerSeries τ (WittVector p k) := fun i β => a i β
  let V : σ → MvPowerSeries τ (WittVector p k) := fun i β => b i β
  let Hs : σ → MvPowerSeries τ (WittVector p k) := fun i β => hh i β
  have hUV : ∀ i, U i = V i + (p : MvPowerSeries τ (WittVector p k)) * Hs i := by
    intro i; refine MvPowerSeries.ext fun β => ?_
    have e : (p : MvPowerSeries τ (WittVector p k)) * Hs i = (p : WittVector p k) • Hs i := by
      rw [Algebra.smul_def, map_natCast]
    rw [e, map_add, map_smul, smul_eq_mul]
    show a i β = b i β + p * hh i β
    rw [← hhh]; ring
  have huM : u = fun i => MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (U i) := by
    funext i; ext β; rw [MvPowerSeries.coeff_map]; exact (ha i β).1
  have hvM : v = fun i => MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (V i) := by
    funext i; ext β; rw [MvPowerSeries.coeff_map]; exact (hb i β).1
  have hf' : ∀ (α : σ →₀ ℕ) (i : σ), ∃ m, ((α i : ℕ) : _root_.GlobalTheory.Katz.Fr p k) * MvPowerSeries.coeff α f =
      algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) m := hf
  have hsu := MvPowerSeries.hasSubst_of_constantCoeff_zero hu0
  have hsv := MvPowerSeries.hasSubst_of_constantCoeff_zero hv0
  unfold _root_.GlobalTheory.Katz.intBy
  refine fun β => ?_
  rw [map_sub, MvPowerSeries.coeff_subst hsu, MvPowerSeries.coeff_subst hsv,
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite hsu f β)
      (MvPowerSeries.coeff_subst_finite hsv f β)]
  refine finsum_induction (fun x => ∃ w, x = algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) (p * w))
    ⟨0, by simp⟩ (fun x y ⟨w1, h1⟩ ⟨w2, h2⟩ => ⟨w1 + w2, by rw [h1, h2, mul_add, map_add]⟩) fun α => ?_
  obtain ⟨Y, hY⟩ := prod_sub_prod_divisible_lemma_2 (MvPowerSeries.coeff α f) U V α α.support fun i _ => by
    obtain ⟨mi, hmi⟩ := hf' α i
    rw [hUV i]
    exact map_add_p_mul_pow_sub_pow_eq_p_smul _ mi hmi (V i) (Hs i)
  refine ⟨MvPowerSeries.coeff β Y, ?_⟩
  rw [huM, hvM]
  simp only [Finsupp.prod, ← map_pow, ← map_prod]
  rw [smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub, ← map_sub, ← smul_eq_mul, ← map_smul, hY,
    map_smul, MvPowerSeries.coeff_map, smul_eq_mul, map_mul]

end GlobalTheory.Katz

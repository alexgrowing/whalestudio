import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.TqPerm

theorem sl_det (g : SL(2, ℤ)) : mat g 0 0 * mat g 1 1 - mat g 0 1 * mat g 1 0 = 1 := by
  have h := g.det_coe
  rw [Matrix.det_fin_two] at h
  exact h

theorem mem_lev (N l : ℕ) (g : SL(2, ℤ)) :
    g ∈ Lev N l ↔ (N : ℤ) ∣ mat g 0 0 - 1 ∧ (N : ℤ) ∣ mat g 1 0 ∧ (l : ℤ) ∣ mat g 1 0 := by
  have hd := sl_det g
  simp only [Lev, Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [sub_eq_zero]
  constructor
  · rintro ⟨⟨h1, _, h3⟩, h4⟩
    exact ⟨h1, h3, h4⟩
  · rintro ⟨h1, h3, h4⟩
    refine ⟨⟨h1, ?_, h3⟩, h4⟩
    have h := congrArg (Int.cast : ℤ → ZMod N) hd
    push_cast at h
    rw [h1, h3] at h
    simpa using h

theorem diam_facts {N l q : ℕ} {σ : SL(2, ℤ)} (h : IsDiam N l (q : ZMod N) σ) :
    (N : ℤ) ∣ mat σ 1 0 ∧ (l : ℤ) ∣ mat σ 1 0 ∧ (N : ℤ) ∣ mat σ 1 1 - q := by
  obtain ⟨h1, h2⟩ := h
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  push_cast at h1
  refine ⟨(dvd_mul_right _ _).trans h1, (dvd_mul_left _ _).trans h1, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [h2, sub_self]

def InDelta (N l q : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0 = q ∧ (N : ℤ) ∣ M 0 0 - 1 ∧ (N : ℤ) ∣ M 1 0 ∧ (l : ℤ) ∣ M 1 0

theorem tqFam_inDelta {N l q : ℕ} {σ : SL(2, ℤ)} (h : IsDiam N l (q : ZMod N) σ) (i : Fin (q + 1)) :
    InDelta N l q (tqFam q σ i) := by
  obtain ⟨⟨c1, h1⟩, ⟨c2, h2⟩, ⟨c3, h3⟩⟩ := diam_facts h
  have hd := sl_det σ
  unfold tqFam InDelta
  split_ifs with hi
  · simp
  · simp only [dg, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    refine ⟨by linear_combination (q : ℤ) * hd, ⟨mat σ 0 1 * c1 - mat σ 0 0 * c3, ?_⟩, ⟨c1 * q, ?_⟩, ⟨c2 * q, ?_⟩⟩
    · linear_combination hd + mat σ 0 1 * h1 - mat σ 0 0 * h3
    · linear_combination (q : ℤ) * h1
    · linear_combination (q : ℤ) * h2

theorem InDelta.mul {N l q : ℕ} {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : InDelta N l q M) {g : SL(2, ℤ)}
    (hg : g ∈ Lev N l) : InDelta N l q (M * mat g) := by
  obtain ⟨h0, h1, h2, h3⟩ := hM
  obtain ⟨g1, g2, g3⟩ := (mem_lev N l g).1 hg
  have hd := sl_det g
  unfold InDelta
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨by linear_combination (mat g 0 0 * mat g 1 1 - mat g 0 1 * mat g 1 0) * h0 + (q : ℤ) * hd, ?_, ?_, ?_⟩
  · have : M 0 0 * mat g 0 0 + M 0 1 * mat g 1 0 - 1
        = (M 0 0 - 1) * mat g 0 0 + (mat g 0 0 - 1) + M 0 1 * mat g 1 0 := by ring
    rw [this]
    exact dvd_add (dvd_add (h1.mul_right _) g1) (g2.mul_left _)
  · exact dvd_add (h2.mul_right _) (g2.mul_left _)
  · exact dvd_add (h3.mul_right _) (g3.mul_left _)

theorem exists_res {q : ℕ} (hq : q.Prime) {x : ℤ} (hx : ¬ (q : ℤ) ∣ x) (y : ℤ) :
    ∃ j : ℕ, j < q ∧ (q : ℤ) ∣ y - j * x := by
  haveI := Fact.mk hq
  have hx' : (x : ZMod q) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨((y : ZMod q) / x).val, ZMod.val_lt _, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, div_mul_cancel₀ _ hx', sub_self]

theorem exists_upper {N l q : ℕ} (hq : q.Prime) (σ : SL(2, ℤ)) {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : InDelta N l q M) {j : ℕ} (hj : j < q) (ha : (q : ℤ) ∣ M 0 1 - j * M 0 0)
    (hb : (q : ℤ) ∣ M 1 1 - j * M 1 0) :
    ∃ (k : Fin (q + 1)) (g : Lev N l), M = mat g * tqFam q σ k := by
  obtain ⟨h0, h1, h2, h3⟩ := hM
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hdet : (!![M 0 0, u; M 1 0, v] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    apply mul_left_cancel₀ hq0
    linear_combination h0 - M 0 0 * hv + M 1 0 * hu
  refine ⟨⟨j, by omega⟩, ⟨⟨_, hdet⟩, (mem_lev N l _).2 ⟨h1, h2, h3⟩⟩, ?_⟩
  show M = !![M 0 0, u; M 1 0, v] * _
  ext a b
  fin_cases a <;> fin_cases b <;> simp [tqFam, hj, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hu
  · linear_combination hv

theorem exists_rep {N l q : ℕ} (hq : q.Prime) (hqN : ¬ q ∣ N * l) {σ : SL(2, ℤ)}
    (hσ : IsDiam N l (q : ZMod N) σ) {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : InDelta N l q M) :
    ∃ (k : Fin (q + 1)) (g : Lev N l), M = mat g * tqFam q σ k := by
  have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  have h0 := hM.1
  by_cases hα : (q : ℤ) ∣ M 0 0
  · by_cases hγ : (q : ℤ) ∣ M 1 0
    · obtain ⟨-, h1, h2, h3⟩ := hM
      obtain ⟨u, hu⟩ := hα
      obtain ⟨v, hv⟩ := hγ
      obtain ⟨s1, s2, s3⟩ := diam_facts hσ
      have hd := sl_det σ
      have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
      have hcN : IsCoprime (N : ℤ) q := Nat.isCoprime_iff_coprime.2
        ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqN (h.mul_right _)).symm
      have hcl : IsCoprime (l : ℤ) q := Nat.isCoprime_iff_coprime.2
        ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqN (h.mul_left _)).symm
      have hNv : (N : ℤ) ∣ v := hcN.dvd_of_dvd_mul_left (hv ▸ h2)
      have hlv : (l : ℤ) ∣ v := hcl.dvd_of_dvd_mul_left (hv ▸ h3)
      have hd' : u * M 1 1 - M 0 1 * v = 1 := by
        apply mul_left_cancel₀ hq0
        linear_combination h0 - M 1 1 * hu + M 0 1 * hv
      have hdet : (!![u * mat σ 1 1 - M 0 1 * mat σ 1 0, -u * mat σ 0 1 + M 0 1 * mat σ 0 0;
          v * mat σ 1 1 - M 1 1 * mat σ 1 0, -v * mat σ 0 1 + M 1 1 * mat σ 0 0] :
          Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination (u * M 1 1 - M 0 1 * v) * hd + hd'
      refine ⟨Fin.last q, ⟨⟨_, hdet⟩, (mem_lev N l _).2 ⟨?_, ?_, ?_⟩⟩, ?_⟩
      · show (N : ℤ) ∣ u * mat σ 1 1 - M 0 1 * mat σ 1 0 - 1
        have : u * mat σ 1 1 - M 0 1 * mat σ 1 0 - 1
            = u * (mat σ 1 1 - q) - M 0 1 * mat σ 1 0 + (M 0 0 - 1) := by rw [hu]; ring
        rw [this]
        exact dvd_add (dvd_sub (s3.mul_left _) (s1.mul_left _)) h1
      · exact dvd_sub (hNv.mul_right _) (s1.mul_left _)
      · exact dvd_sub (hlv.mul_right _) (s2.mul_left _)
      · show M = !![u * mat σ 1 1 - M 0 1 * mat σ 1 0, -u * mat σ 0 1 + M 0 1 * mat σ 0 0;
          v * mat σ 1 1 - M 1 1 * mat σ 1 0, -v * mat σ 0 1 + M 1 1 * mat σ 0 0] * _
        ext a b
        fin_cases a <;> fin_cases b <;> simp [tqFam, dg, Matrix.mul_apply, Fin.sum_univ_two]
        · linear_combination hu - q * u * hd
        · linear_combination (-M 0 1) * hd
        · linear_combination hv - q * v * hd
        · linear_combination (-M 1 1) * hd
    · obtain ⟨j, hj, hb⟩ := exists_res hq hγ (M 1 1)
      refine exists_upper hq σ hM hj ?_ hb
      have : (q : ℤ) ∣ M 1 0 * (M 0 1 - j * M 0 0) := by
        have e : M 1 0 * (M 0 1 - j * M 0 0) = M 0 0 * (M 1 1 - j * M 1 0) - q := by linear_combination -h0
        rw [e]
        exact dvd_sub (hb.mul_left _) dvd_rfl
      exact (hp.dvd_or_dvd this).resolve_left hγ
  · obtain ⟨j, hj, ha⟩ := exists_res hq hα (M 0 1)
    refine exists_upper hq σ hM hj ha ?_
    have : (q : ℤ) ∣ M 0 0 * (M 1 1 - j * M 1 0) := by
      have e : M 0 0 * (M 1 1 - j * M 1 0) = M 1 0 * (M 0 1 - j * M 0 0) + q := by linear_combination h0
      rw [e]
      exact dvd_add (ha.mul_left _) dvd_rfl
    exact (hp.dvd_or_dvd this).resolve_left hα

theorem tqFam_inj {q : ℕ} (hq : q.Prime) (σ h : SL(2, ℤ)) {i k : Fin (q + 1)}
    (e : tqFam q σ i = mat h * tqFam q σ k) : i = k := by
  have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  have hd := sl_det h
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e10 := congrFun (congrFun e 1) 0
  have hi := i.2
  have hk := k.2
  by_cases a : (i : ℕ) < q <;> by_cases b : (k : ℕ) < q
  · simp [tqFam, a, b, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
    have hdv : (q : ℤ) ∣ ((i : ℕ) : ℤ) - ((k : ℕ) : ℤ) := ⟨mat h 0 1, by linear_combination e01 - ((k : ℕ) : ℤ) * e00⟩
    have := Int.eq_zero_of_abs_lt_dvd hdv (by rw [abs_lt]; constructor <;> omega)
    exact Fin.ext (by omega)
  · exfalso
    simp [tqFam, a, b, dg, Matrix.mul_apply, Fin.sum_univ_two] at e00
    exact hp.not_dvd_one ⟨mat h 0 0 * mat σ 0 0 + mat h 0 1 * mat σ 1 0, by linear_combination e00⟩
  · exfalso
    simp [tqFam, a, b, dg, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
    exact hp.not_dvd_one ⟨mat σ 0 0 * mat h 1 1 - mat h 0 1 * mat σ 1 0,
      by linear_combination -hd - mat h 1 1 * e00 + mat h 0 1 * e10⟩
  · exact Fin.ext (by omega)

theorem tqFam_perm : ∀ (N l q : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → q.Prime → ¬ q ∣ N * l → ∀ σ : SL(2, ℤ),
    IsDiam N l (q : ZMod N) σ → ∀ γ : Lev N l, ∃ π : Equiv.Perm (Fin (q + 1)), ∀ i, ∃ γ' : Lev N l,
      tqFam q σ i * mat γ = mat γ' * tqFam q σ (π i) := by
  intro N l q _ _ _ hq hqN σ hσ γ
  choose f g hf using fun i => exists_rep hq hqN hσ ((tqFam_inDelta hσ i).mul γ.2)
  have hinj : Function.Injective f := by
    intro i k hik
    refine tqFam_inj hq σ ((g i : SL(2, ℤ)) * (g k : SL(2, ℤ))⁻¹) ?_
    have h1 : mat γ * mat (γ : SL(2, ℤ))⁻¹ = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h2 : mat (g k : SL(2, ℤ))⁻¹ * mat (g k) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc tqFam q σ i = tqFam q σ i * mat γ * mat (γ : SL(2, ℤ))⁻¹ := by rw [mul_assoc, h1, mul_one]
      _ = mat (g i) * (mat (g k : SL(2, ℤ))⁻¹ * mat (g k)) * tqFam q σ (f k) * mat (γ : SL(2, ℤ))⁻¹ := by
          rw [hf i, hik, h2, mul_one]
      _ = mat (g i) * mat (g k : SL(2, ℤ))⁻¹ * (mat (g k) * tqFam q σ (f k)) * mat (γ : SL(2, ℤ))⁻¹ := by
          simp only [mul_assoc]
      _ = mat (g i) * mat (g k : SL(2, ℤ))⁻¹ * tqFam q σ k := by
          rw [← hf k, mul_assoc, mul_assoc (tqFam q σ k), h1, mul_one]
      _ = _ := by rw [← Matrix.SpecialLinearGroup.coe_mul]
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), fun i => ⟨g i, hf i⟩⟩

end GlobalTheory.TqPerm

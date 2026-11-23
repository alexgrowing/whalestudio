import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.HeckeCosetLevel

lemma toGQ_val (m : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) :
    (((toGQ m : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = m.map (Int.castRingHom ℚ) := by
  simp [toGQ, h]

lemma ofSL_val (γ : SL(2, ℤ)) :
    (((ofSL γ : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := by
  rfl

lemma toGQ_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (hA : 0 < A.det) (hB : 0 < B.det) :
    toGQ (A * B) = toGQ A * toGQ B := by
  have hAB : 0 < (A * B).det := by rw [Matrix.det_mul]; exact mul_pos hA hB
  apply Subtype.ext; apply Units.ext
  rw [toGQ_val _ hAB]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [toGQ_val _ hA, toGQ_val _ hB, Matrix.map_mul]

lemma toGQ_SL (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  apply Subtype.ext; apply Units.ext
  rw [toGQ_val _ (by simp), ofSL_val]

lemma mem_Gamma_of_mul (M q : ℕ) (hqM : Nat.Coprime q M) (N : SL(2, ℤ)) (B m : Matrix (Fin 2) (Fin 2) ℤ)
    (hm : (N : Matrix (Fin 2) (Fin 2) ℤ) * B = m)
    (b00 : (B 0 0 : ZMod M) = 1) (b01 : (B 0 1 : ZMod M) = 0) (b10 : (B 1 0 : ZMod M) = 0) (b11 : (B 1 1 : ZMod M) = q)
    (h00 : (m 0 0 : ZMod M) = 1) (h01 : (m 0 1 : ZMod M) = 0) (h10 : (m 1 0 : ZMod M) = 0) (h11 : (m 1 1 : ZMod M) = q) :
    N ∈ CongruenceSubgroup.Gamma M := by
  have hu : IsUnit (q : ZMod M) := by
    have := (ZMod.unitOfCoprime q hqM).isUnit
    rwa [ZMod.coe_unitOfCoprime] at this
  have e : ∀ i j, ((m i j : ℤ) : ZMod M) = ((N : Matrix (Fin 2) (Fin 2) ℤ) i 0 : ZMod M) * (B 0 j : ZMod M) +
      ((N : Matrix (Fin 2) (Fin 2) ℤ) i 1 : ZMod M) * (B 1 j : ZMod M) := by
    intro i j; rw [← hm]; simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  rw [b00, b10, h00] at e00
  rw [b01, b11, h01] at e01
  rw [b00, b10, h10] at e10
  rw [b01, b11, h11] at e11
  simp only [mul_one, mul_zero, add_zero, zero_add] at e00 e01 e10 e11
  refine CongruenceSubgroup.Gamma_mem.mpr ⟨e00.symm, ?_, e10.symm, ?_⟩
  · exact (hu.mul_left_eq_zero).mp e01.symm
  · exact hu.mul_right_cancel (by rw [one_mul]; exact e11.symm)

lemma sigma_diag_mod (M q : ℕ) (σ : SL(2, ℤ))
    (hσ : (en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) :
    let B := (σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]
    (B 0 0 : ZMod M) = 1 ∧ (B 0 1 : ZMod M) = 0 ∧ (B 1 0 : ZMod M) = 0 ∧ (B 1 1 : ZMod M) = q := by
  intro B
  obtain ⟨s01, s10, s11⟩ := hσ
  have hd : (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := σ.2
  rw [Matrix.det_fin_two] at hd
  have hd' := congrArg (fun x : ℤ => (x : ZMod M)) hd
  simp only [en] at s01 s10 s11
  push_cast at hd'
  rw [s01, s10, s11] at hd'
  simp [B, Matrix.mul_apply, Fin.sum_univ_two, s01, s10, s11]
  linear_combination hd'

def reps (M q : ℕ) (σ : SL(2, ℤ)) (i : Fin (q + 1)) : Matrix (Fin 2) (Fin 2) ℤ :=
  if (i : ℕ) < q then !![1, ((i : ℕ) * M : ℤ); 0, (q : ℤ)] else (σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]

lemma reps_det (M q : ℕ) (σ : SL(2, ℤ)) (i : Fin (q + 1)) : (reps M q σ i).det = q := by
  unfold reps; split_ifs <;> simp [Matrix.det_fin_two]

theorem exists_coset (M q : ℕ) (hM : 0 < M) (hq : q.Prime) (hqM : Nat.Coprime q M) (σ : SL(2, ℤ))
    (hσ : (en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q)
    (m : Matrix (Fin 2) (Fin 2) ℤ) (hdet : m.det = q) (h00 : (m 0 0 : ZMod M) = 1) (h01 : (m 0 1 : ZMod M) = 0)
    (h10 : (m 1 0 : ZMod M) = 0) (h11 : (m 1 1 : ZMod M) = q) :
    (∃ j < q, ∃ γ ∈ CongruenceSubgroup.Gamma M, m = (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, (j * M : ℤ); 0, (q : ℤ)]) ∨
      ∃ γ ∈ CongruenceSubgroup.Gamma M, m = (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) := by
  haveI := Fact.mk hq
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  rw [Matrix.det_fin_two] at hdet
  by_cases hdiv : (q : ℤ) ∣ m 0 0 ∧ (q : ℤ) ∣ m 1 0
  · right
    obtain ⟨⟨a', ha⟩, ⟨c', hc⟩⟩ := hdiv
    have hd1 : a' * m 1 1 - m 0 1 * c' = 1 := by
      apply mul_left_cancel₀ hq0
      rw [ha, hc] at hdet; linear_combination hdet
    have hσd : (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := σ.2
    let N0 : Matrix (Fin 2) (Fin 2) ℤ := !![a', m 0 1; c', m 1 1] * (σ : Matrix (Fin 2) (Fin 2) ℤ).adjugate
    have hN : N0.det = 1 := by
      simp only [N0, Matrix.det_mul, Matrix.det_adjugate, hσd, Matrix.det_fin_two_of]
      simp [hd1]
    let N : SL(2, ℤ) := ⟨N0, hN⟩
    have hNm : (N : Matrix (Fin 2) (Fin 2) ℤ) * ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) = m := by
      show N0 * _ = m
      simp only [N0]
      rw [← Matrix.mul_assoc, Matrix.mul_assoc _ (σ : Matrix (Fin 2) (Fin 2) ℤ).adjugate, Matrix.adjugate_mul, hσd, one_smul,
        Matrix.mul_one]
      ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hc] <;> ring
    obtain ⟨b00, b01, b10, b11⟩ := sigma_diag_mod M q σ hσ
    exact ⟨N, mem_Gamma_of_mul M q hqM N _ m hNm b00 b01 b10 b11 h00 h01 h10 h11, hNm.symm⟩
  · left
    have hMq : ((M : ℕ) : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hq).mp hqM
    have hz : ∀ x : ℤ, (q : ℤ) ∣ x ↔ ((x : ℤ) : ZMod q) = 0 := fun x => (ZMod.intCast_zmod_eq_zero_iff_dvd x q).symm
    have hdz : ((m 0 0 : ℤ) : ZMod q) * (m 1 1 : ZMod q) - (m 0 1 : ZMod q) * (m 1 0 : ZMod q) = 0 := by
      have := congrArg (fun x : ℤ => (x : ZMod q)) hdet
      push_cast at this; rw [this]; exact ZMod.natCast_self q
    set a : ZMod q := ((m 0 0 : ℤ) : ZMod q) with ha
    set b : ZMod q := ((m 0 1 : ℤ) : ZMod q) with hb
    set c : ZMod q := ((m 1 0 : ℤ) : ZMod q) with hc
    set d : ZMod q := ((m 1 1 : ℤ) : ZMod q) with hd
    have hac : a ≠ 0 ∨ c ≠ 0 := by
      by_contra hcon; push_neg at hcon
      exact hdiv ⟨(hz _).mpr hcon.1, (hz _).mpr hcon.2⟩
    obtain ⟨t, ht1, ht2⟩ : ∃ t : ZMod q, b = a * t * (M : ZMod q) ∧ d = c * t * (M : ZMod q) := by
      rcases hac with ha0 | hc0
      · refine ⟨b / (a * (M : ZMod q)), ?_, ?_⟩
        · field_simp
        · field_simp; linear_combination hdz
      · by_cases ha0 : a = 0
        · refine ⟨d / (c * (M : ZMod q)), ?_, ?_⟩
          · rw [ha0] at hdz ⊢
            have : b * c = 0 := by linear_combination -hdz
            rcases mul_eq_zero.mp this with h | h
            · rw [h]; ring
            · exact absurd h hc0
          · field_simp
        · refine ⟨b / (a * (M : ZMod q)), ?_, ?_⟩
          · field_simp
          · field_simp; linear_combination hdz
    refine ⟨t.val, ZMod.val_lt t, ?_⟩
    have ht : ((t.val : ℤ) : ZMod q) = t := by simp
    obtain ⟨t1, e1⟩ : (q : ℤ) ∣ m 0 1 - m 0 0 * ((t.val : ℤ) * M) := by
      rw [hz]; push_cast; rw [ZMod.natCast_zmod_val, ← hb, ← ha, ht1]; ring
    obtain ⟨t2, e2⟩ : (q : ℤ) ∣ m 1 1 - m 1 0 * ((t.val : ℤ) * M) := by
      rw [hz]; push_cast; rw [ZMod.natCast_zmod_val, ← hd, ← hc, ht2]; ring
    have hd1 : m 0 0 * t2 - t1 * m 1 0 = 1 := by
      apply mul_left_cancel₀ hq0
      linear_combination hdet - m 0 0 * e2 + m 1 0 * e1
    let N : SL(2, ℤ) := ⟨!![m 0 0, t1; m 1 0, t2], by rw [Matrix.det_fin_two_of]; exact hd1⟩
    have hNm : (N : Matrix (Fin 2) (Fin 2) ℤ) * !![1, ((t.val : ℕ) * M : ℤ); 0, (q : ℤ)] = m := by
      show !![m 0 0, t1; m 1 0, t2] * _ = m
      ext i j; fin_cases i <;> fin_cases j <;> simp [-ZMod.natCast_val] <;> first | linear_combination -e1 | linear_combination -e2
    refine ⟨N, mem_Gamma_of_mul M q hqM N _ m hNm (by simp) (by simp) (by simp) (by simp) h00 h01 h10 h11, hNm.symm⟩

theorem reps_distinct (M q : ℕ) (hq : q.Prime) (hqM : Nat.Coprime q M) (σ : SL(2, ℤ)) (i k : Fin (q + 1))
    (g : SL(2, ℤ)) (h : reps M q σ i = (g : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ k) : i = k := by
  have hq1 : ¬ (q : ℤ) ∣ 1 := by
    intro h
    have := Int.natCast_dvd_natCast.mp (by exact_mod_cast h)
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  have E : ∀ a b, reps M q σ i a b = ((g : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ k) a b := fun a b => by rw [h]
  have e00 := E 0 0
  have e01 := E 0 1
  have e10 := E 1 0
  have e11 := E 1 1
  unfold reps at e00 e01 e10 e11
  by_cases hi : (i : ℕ) < q <;> by_cases hk : (k : ℕ) < q <;>
    simp only [hi, hk, if_true, if_false] at e00 e01 e10 e11 <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  ·
    have hdv : (q : ℤ) ∣ ((i : ℕ) - (k : ℕ) : ℤ) * M := ⟨(g : Matrix (Fin 2) (Fin 2) ℤ) 0 1, by
      rw [← e00] at e01; linear_combination e01⟩
    have hcop : IsCoprime (q : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.mpr hqM
    have hdv' := hcop.dvd_of_dvd_mul_right hdv
    have h0 := Int.eq_zero_of_abs_lt_dvd hdv' (by rw [abs_lt]; constructor <;> omega)
    exact Fin.ext (by omega)
  ·
    exact absurd ⟨(g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0, by linear_combination e00⟩ hq1
  ·
    have hσd : (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := σ.2
    rw [Matrix.det_fin_two] at hσd
    apply absurd _ hq1
    exact ⟨(σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0, by
      linear_combination -hσd + (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * e11 - (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * e01 -
        ((k : ℕ) : ℤ) * (M : ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * e10 + ((k : ℕ) : ℤ) * (M : ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * e00⟩
  · exact Fin.ext (by omega)

end GlobalTheory.HeckeCosetLevel

open GlobalTheory.HeckeCosetLevel in
theorem GlobalTheory.hecke_product_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (M q : ℕ) (f : X.K), 0 < M → q.Prime → Nat.Coprime q M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ∀ σ : SL(2, ℤ), ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) = (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f := by
  intro Ω _ _ ε X M q f hM hq hqM hf σ hσ γ hγ
  have hprod : (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) *
      X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f =
      ∏ i : Fin (q + 1), X.sl (toGQ (reps M q σ i)) f := by
    rw [Fin.prod_univ_castSucc, Finset.prod_range]
    simp [reps]
  rw [hprod, map_prod]
  obtain ⟨g00, g01, g10, g11⟩ := CongruenceSubgroup.Gamma_mem.mp hγ
  have hpos : ∀ i, 0 < (reps M q σ i).det := fun i => by rw [reps_det]; exact_mod_cast hq.pos
  have hrM : ∀ i, ((reps M q σ i) 0 0 : ZMod M) = 1 ∧ ((reps M q σ i) 0 1 : ZMod M) = 0 ∧
      ((reps M q σ i) 1 0 : ZMod M) = 0 ∧ ((reps M q σ i) 1 1 : ZMod M) = q := by
    intro i
    unfold reps
    split_ifs with hi
    · simp
    · obtain ⟨s01, s10, s11⟩ := hσ
      have hd : (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := σ.2
      rw [Matrix.det_fin_two] at hd
      have hd' := congrArg (fun x : ℤ => (x : ZMod M)) hd
      simp only [en] at s01 s10 s11
      push_cast at hd'
      rw [s01, s10, s11] at hd'
      simp [Matrix.mul_apply, Fin.sum_univ_two, s01, s10, s11]
      linear_combination hd'
  have key : ∀ i, ∃ k, ∃ g ∈ CongruenceSubgroup.Gamma M,
      reps M q σ i * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (g : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ k := by
    intro i
    obtain ⟨a00, a01, a10, a11⟩ := hrM i
    have hdet : (reps M q σ i * (γ : Matrix (Fin 2) (Fin 2) ℤ)).det = q := by
      rw [Matrix.det_mul, reps_det]; simp
    rcases exists_coset M q hM hq hqM σ hσ _ hdet
      (by simp [Matrix.mul_apply, Fin.sum_univ_two, a00, a01, g00, g10])
      (by simp [Matrix.mul_apply, Fin.sum_univ_two, a00, a01, g01, g11])
      (by simp [Matrix.mul_apply, Fin.sum_univ_two, a10, a11, g00, g10])
      (by simp [Matrix.mul_apply, Fin.sum_univ_two, a10, a11, g01, g11]) with ⟨j, hj, g, hg, h⟩ | ⟨g, hg, h⟩
    · refine ⟨⟨j, by omega⟩, g, hg, ?_⟩
      rw [h]; simp [reps, hj]
    · refine ⟨Fin.last q, g, hg, ?_⟩
      rw [h]; simp [reps]
  choose π g hg hπ using key
  have inj : Function.Injective π := by
    intro i j hij
    have h1 := hπ i
    have h2 := hπ j
    rw [hij] at h1
    apply reps_distinct M q hq hqM σ i j (g i * (g j)⁻¹)
    have hγi : (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hgj : ((g j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (((g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hgj' : (((g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * ((g j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc reps M q σ i = reps M q σ i * (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [Matrix.mul_assoc, hγi, Matrix.mul_one]
      _ = (g i : Matrix (Fin 2) (Fin 2) ℤ) * (((g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
            ((g j : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ (π j)) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [h1]; simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (((g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (g j : Matrix (Fin 2) (Fin 2) ℤ), hgj', Matrix.one_mul]
      _ = ((g i * (g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ j := by
          rw [← h2, Matrix.SpecialLinearGroup.coe_mul]
          simp only [Matrix.mul_assoc, hγi, Matrix.mul_one]
  let e := Equiv.ofBijective π (Finite.injective_iff_bijective.mp inj)
  calc ∏ i : Fin (q + 1), X.sl (ofSL γ) (X.sl (toGQ (reps M q σ i)) f)
      = ∏ i : Fin (q + 1), X.sl (toGQ (reps M q σ (e i))) f := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [← X.sl_mul, ← toGQ_SL γ, ← toGQ_mul _ _ (hpos i) (by simp), hπ i,
          toGQ_mul _ _ (by simp) (hpos _), toGQ_SL, X.sl_mul, hf _ (hg i)]
        rfl
    _ = ∏ i : Fin (q + 1), X.sl (toGQ (reps M q σ i)) f := Equiv.prod_comp e (fun i => X.sl (toGQ (reps M q σ i)) f)

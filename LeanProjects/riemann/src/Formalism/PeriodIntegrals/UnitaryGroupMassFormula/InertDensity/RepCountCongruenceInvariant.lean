import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.AnisoPeelAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.ExistsTraceNeZero

open Finset

noncomputable section

namespace DensInertW

def cgComb {L : Type} [Field L] {m n : ℕ} (Q : Matrix (Fin m) (Fin m) L) (X : Fin m → Fin n → L) :
    Fin m → Fin n → L :=
  fun i => ∑ k, Q i k • X k

theorem cg_comb_comb {L : Type} [Field L] {m n : ℕ} (P Q : Matrix (Fin m) (Fin m) L)
    (X : Fin m → Fin n → L) : cgComb P (cgComb Q X) = cgComb (P * Q) X := by
  funext i
  simp only [cgComb, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_comm

theorem cg_comb_one {L : Type} [Field L] {m n : ℕ} (X : Fin m → Fin n → L) :
    cgComb (1 : Matrix (Fin m) (Fin m) L) X = X := by
  funext i
  simp [cgComb, Matrix.one_apply, ite_smul]

theorem cg_mem {L : Type} [Field L] {m n : ℕ} (Q : Matrix (Fin m) (Fin m) L)
    (X : Fin m → Fin n → L) (W : Submodule L (Fin n → L)) (hX : ∀ i, X i ∈ W) :
    ∀ i, cgComb Q X i ∈ W := by
  intro i
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hX k)

theorem cg_lincomb {L : Type} [Field L] {m n : ℕ} (Q : Matrix (Fin m) (Fin m) L)
    (X : Fin m → Fin n → L) (g : Fin m → L) :
    ∑ i, g i • cgComb Q X i = ∑ k, (Matrix.vecMul g Q) k • X k := by
  simp only [cgComb, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
  exact Finset.sum_comm

theorem cg_indep {L : Type} [Field L] {m n : ℕ} (Q : Matrix (Fin m) (Fin m) L)
    (X : Fin m → Fin n → L) (hQ : Q.det ≠ 0) (hX : LinearIndependent L X) :
    LinearIndependent L (cgComb Q X) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro g hg i
  rw [cg_lincomb] at hg
  have h0 : Matrix.vecMul g Q = 0 := funext (hX _ hg)
  have hg' : g = Matrix.vecMul (Matrix.vecMul g Q) Q⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hQ.isUnit, Matrix.vecMul_one]
  rw [hg', h0, Matrix.zero_vecMul, Pi.zero_apply]

theorem cg_hf_left {L : Type} [Field L] {m n : ℕ} (q : ℕ) (M : Matrix (Fin n) (Fin n) L)
    (c : Fin m → L) (x : Fin m → Fin n → L) (y : Fin n → L) :
    hf q M (∑ k, c k • x k) y = ∑ k, c k * hf q M (x k) y := by
  have e1 : ∀ a b, (∑ k, c k * x k a) * M a b * y b ^ q =
      ∑ k, c k * (x k a * M a b * y b ^ q) := fun a b => by
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e1, Finset.mul_sum]
  calc _ = ∑ a, ∑ k, ∑ b, c k * (x k a * M a b * y b ^ q) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem cg_hf_right (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] {m n : ℕ}
    (M : Matrix (Fin n) (Fin n) L) (c : Fin m → L) (x : Fin n → L) (y : Fin m → Fin n → L) :
    hf (Fintype.card K) M x (∑ l, c l • y l) =
      ∑ l, c l ^ Fintype.card K * hf (Fintype.card K) M x (y l) := by
  obtain ⟨p, hch⟩ := CharP.exists K
  obtain ⟨n, hp, hq⟩ := FiniteField.card K p
  haveI := Fact.mk hp
  haveI : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hfr : ∀ (s : Finset (Fin m)) (f : Fin m → L),
      (∑ i ∈ s, f i) ^ Fintype.card K = ∑ i ∈ s, f i ^ Fintype.card K := by
    intro s f
    rw [hq]
    first
    | exact sum_pow_char_pow s f
    | (haveI : ExpChar L p := ExpChar.prime hp
       have h := map_sum (iterateFrobenius L p n) f s
       simp only [iterateFrobenius_def] at h
       exact h)
    | (haveI : ExpChar L p := ExpChar.prime hp
       simp)
  have hfrob : ∀ b, (∑ l, c l * y l b) ^ Fintype.card K =
      ∑ l, c l ^ Fintype.card K * y l b ^ Fintype.card K := by
    intro b
    rw [hfr]
    simp [mul_pow]
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hfrob, Finset.mul_sum]
  calc _ = ∑ a, ∑ l, ∑ b, x a * M a b * (c l ^ Fintype.card K * y l b ^ Fintype.card K) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ b, x a * M a b * (c l ^ Fintype.card K * y l b ^ Fintype.card K) :=
        Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => by ring

theorem cg_gram (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] {m n : ℕ}
    (M : Matrix (Fin n) (Fin n) L) (Q G : Matrix (Fin m) (Fin m) L) (X : Fin m → Fin n → L)
    (hX : ∀ k l, hf (Fintype.card K) M (X k) (X l) = G k l) (i j : Fin m) :
    hf (Fintype.card K) M (cgComb Q X i) (cgComb Q X j) =
      (Q * G * (Q.map (fun y => y ^ Fintype.card K)).transpose) i j := by
  show hf (Fintype.card K) M (∑ k, Q i k • X k) (∑ l, Q j l • X l) = _
  rw [cg_hf_left]
  simp only [cg_hf_right K L, hX, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ l, ∑ k, Q i k * (Q j l ^ Fintype.card K * G k l) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem cg_map_mul (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] {m : ℕ}
    (A C : Matrix (Fin m) (Fin m) L) :
    (A * C).map (fun y => y ^ Fintype.card K) =
      A.map (fun y => y ^ Fintype.card K) * C.map (fun y => y ^ Fintype.card K) := by
  obtain ⟨p, hch⟩ := CharP.exists K
  obtain ⟨n, hp, hq⟩ := FiniteField.card K p
  haveI := Fact.mk hp
  haveI : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hfr : ∀ (s : Finset (Fin m)) (f : Fin m → L),
      (∑ i ∈ s, f i) ^ Fintype.card K = ∑ i ∈ s, f i ^ Fintype.card K := by
    intro s f
    rw [hq]
    first
    | exact sum_pow_char_pow s f
    | (haveI : ExpChar L p := ExpChar.prime hp
       have h := map_sum (iterateFrobenius L p n) f s
       simp only [iterateFrobenius_def] at h
       exact h)
    | (haveI : ExpChar L p := ExpChar.prime hp
       simp)
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply]
  rw [hfr]
  simp [mul_pow]

theorem repCountCongruenceInvariant : Congr := by
  intro K L _ _ _ _ _ _ n M W m B P hP
  have hdet : P.det ≠ 0 := hP.ne_zero
  have hq1 : 0 < Fintype.card K := Fintype.card_pos
  have hmap1 : (1 : Matrix (Fin m) (Fin m) L).map (fun y => y ^ Fintype.card K) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, zero_pow hq1.ne']
  have hPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hPinv' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hinj : Function.Injective (fun X : Fin m → Fin n → L => cgComb P X) := fun X Y h => by
    have h2 := congrArg (cgComb P⁻¹) h
    simpa [cg_comb_comb, hPinv', cg_comb_one] using h2
  have e : (P.map (fun y => y ^ Fintype.card K)).transpose *
      (P⁻¹.map (fun y => y ^ Fintype.card K)).transpose = 1 := by
    rw [← Matrix.transpose_mul, ← cg_map_mul K L, hPinv', hmap1, Matrix.transpose_one]
  have e2 : P⁻¹ * (P * B * (P.map (fun y => y ^ Fintype.card K)).transpose) *
      (P⁻¹.map (fun y => y ^ Fintype.card K)).transpose = B := by
    simp only [Matrix.mul_assoc, e, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hPinv', Matrix.one_mul]
  unfold cntT
  convert Set.ncard_image_of_injective _ hinj using 2
  ext Y
  constructor
  · rintro ⟨hW, hI, hG⟩
    refine ⟨cgComb P⁻¹ Y, ⟨cg_mem _ _ _ hW,
      cg_indep _ _ (Matrix.isUnit_nonsing_inv_det P hP).ne_zero hI, fun i j => ?_⟩, ?_⟩
    · rw [cg_gram K L M P⁻¹ _ Y hG, e2]
    · show cgComb P (cgComb P⁻¹ Y) = Y
      rw [cg_comb_comb, hPinv, cg_comb_one]
  · rintro ⟨X, ⟨hW, hI, hG⟩, rfl⟩
    exact ⟨cg_mem _ _ _ hW, cg_indep _ _ hdet hI, fun i j => cg_gram K L M P B X hG i j⟩

end DensInertW

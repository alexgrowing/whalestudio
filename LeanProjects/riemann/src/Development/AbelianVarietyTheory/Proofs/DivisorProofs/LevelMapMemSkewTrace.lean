import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
open Matrix GlobalTheory.SUCong

namespace GlobalTheory.SUCong.LevMem

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem intM_mul (S : Subring A) {M N : Matrix n n A} (hM : ∀ i j, M i j ∈ S)
    (hN : ∀ i j, N i j ∈ S) : ∀ i j, (M * N) i j ∈ S := fun i j => by
  rw [mul_apply]; exact Subring.sum_mem _ fun l _ => mul_mem (hM i l) (hN l j)

theorem intM_cT (S : Subring A) (σ : A →+* A) (hσ : ∀ s ∈ S, σ s ∈ S) {M : Matrix n n A}
    (hM : ∀ i j, M i j ∈ S) : ∀ i j, Formalism.UG.cT σ M i j ∈ S := fun i j => by
  simp only [Formalism.UG.cT, transpose_apply, map_apply]; exact hσ _ (hM j i)

theorem cancel_pow {ϖ : A} (h : ∀ a : A, ϖ * a = 0 → a = 0) (k : ℕ) {a : A}
    (ha : ϖ ^ k * a = 0) : a = 0 := by
  induction k generalizing a with
  | zero => simpa using ha
  | succ k ih => exact h _ (ih (by rw [← mul_assoc, mul_comm _ ϖ, ← pow_succ']; exact ha))

theorem cT_one_add_smul (σ : A →+* A) {c : A} (hc : σ c = c) (X : Matrix n n A) :
    Formalism.UG.cT σ (1 + c • X) = 1 + c • Formalism.UG.cT σ X := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Formalism.UG.cT, hc]
  · simp [Formalism.UG.cT, hc, one_apply, h, Ne.symm h]

end GlobalTheory.SUCong.LevMem

open GlobalTheory.SUCong.LevMem in

theorem GlobalTheory.SUCong.levMap_mem_skewTr : ∀ {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (S : Subring A) (σ : A →+* A) (H : Matrix n n A) (ϖ : A) (q k : ℕ), GoodRing S σ ϖ q → GoodForm S σ H → 1 ≤ k → ∀ (g : GL n A), g ∈ congSU S σ H ϖ k → levMap S ϖ k (g : Matrix n n A) ∈ skewTr S σ H ϖ := by
  intro A _ n _ _ S σ H ϖ q k hR hF hk g hg
  obtain ⟨hU, hdet, -, -, hpow⟩ := hg
  obtain ⟨-, hσS, hϖS, hσϖ, hnz, -⟩ := hR
  obtain ⟨hHS, -, -⟩ := hF
  set X : Matrix n n A := fun i j => Classical.choose (hpow i j) with hX
  have hXS : ∀ i j, X i j ∈ S := fun i j => (Classical.choose_spec (hpow i j)).1
  have hXe : ∀ i j, ((g : Matrix n n A) - 1) i j = ϖ ^ k * X i j :=
    fun i j => (Classical.choose_spec (hpow i j)).2
  have hg1 : (g : Matrix n n A) = 1 + ϖ ^ k • X := by
    ext i j
    have := hXe i j
    rw [Matrix.sub_apply] at this
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ← this]; ring
  have hkm : ϖ ^ k = ϖ * ϖ ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  refine ⟨X, hXS, fun i j => ?_, fun i j => ?_, ?_⟩
  · simp only [levMap, dif_pos (hpow i j)]; rfl
  · have hU' : Formalism.UG.cT σ (g : Matrix n n A) * H * (g : Matrix n n A) = H := hU
    rw [hg1, cT_one_add_smul σ (by rw [map_pow, hσϖ]) X] at hU'
    have hexp : (1 + ϖ ^ k • Formalism.UG.cT σ X) * H * (1 + ϖ ^ k • X) =
        H + ϖ ^ k • (Formalism.UG.cT σ X * H + H * X + ϖ ^ k • (Formalism.UG.cT σ X * H * X)) := by
      simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_add,
        smul_smul, Matrix.mul_assoc]
      abel
    rw [hexp] at hU'
    have e := congrFun (congrFun hU' i) j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at e
    have e2 : ϖ ^ k * ((Formalism.UG.cT σ X * H) i j + (H * X) i j +
        ϖ ^ k * (Formalism.UG.cT σ X * H * X) i j) = 0 := by linear_combination e
    have e3 := cancel_pow hnz k e2
    have hZ := intM_mul S (intM_mul S (intM_cT S σ hσS hXS) hHS) hXS i j
    refine ⟨-(ϖ ^ (k - 1) * (Formalism.UG.cT σ X * H * X) i j), neg_mem (mul_mem (pow_mem hϖS _) hZ), ?_⟩
    rw [pow_one, Matrix.add_apply]
    linear_combination e3 - (Formalism.UG.cT σ X * H * X) i j * hkm
  · let XS : Matrix n n S := fun i j => ⟨X i j, hXS i j⟩
    let t : S := ⟨ϖ, hϖS⟩ ^ k
    have hd := Matrix.det_one_add_smul t XS
    set c := Polynomial.eval t (1 + (Polynomial.X : Polynomial S) • XS.map Polynomial.C).det.divX.divX
    have hm : S.subtype.mapMatrix (1 + t • XS) = (g : Matrix n n A) := by
      rw [hg1]; ext i j
      by_cases h : i = j
      · subst h; simp [XS, t] <;> rfl
      · simp [XS, t, one_apply, h] <;> rfl
    have h1 : ((1 + t • XS).det : A) = (g : Matrix n n A).det := by
      rw [← hm, ← RingHom.map_det]; rfl
    have h2 : ((1 + t • XS).det : A) = 1 + X.trace * ϖ ^ k + (c : A) * (ϖ ^ k) ^ 2 := by
      rw [hd]; simp [t, XS, Matrix.trace] <;> rfl
    rw [h1, hdet] at h2
    have e3 : ϖ ^ k * (X.trace + ϖ ^ k * c) = 0 := by linear_combination -h2
    have e4 := cancel_pow hnz k e3
    refine ⟨-(ϖ ^ (k - 1) * c), neg_mem (mul_mem (pow_mem hϖS _) c.2), ?_⟩
    rw [pow_one]
    linear_combination e4 - (c : A) * hkm

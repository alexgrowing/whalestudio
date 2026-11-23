import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZphiPowPr

open Matrix

namespace GlobalTheory.ZarhinFam

theorem zpow_finset_sum' {G ι : Type} [CommGroup G] (a : G) (s : Finset ι) (e : ι → ℤ) :
    a ^ (∑ k ∈ s, e k) = ∏ k ∈ s, a ^ e k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.prod_insert hb, _root_.zpow_add, ih]

theorem prod_prod_zpow_mul {G : Type} [CommGroup G] (P Q : Matrix (Fin 4) (Fin 4) ℤ) (w : Fin 4 → G)
    (a : Fin 4) : ∏ k, (∏ i, w i ^ Q k i) ^ P a k = ∏ i, w i ^ (P * Q) a i := by
  simp_rw [← Finset.prod_zpow, ← _root_.zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, zpow_finset_sum']
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem prod_zpow_smul_one {G : Type} [CommGroup G] (c : ℤ) (w : Fin 4 → G) (a : Fin 4) :
    ∏ i, w i ^ (c • (1 : Matrix (Fin 4) (Fin 4) ℤ)) a i = w a ^ c := by
  simp [Matrix.smul_apply, Matrix.one_apply]

theorem zarhin_kernel_trivial : ∀ (d : ℕ) (GA GB : Type) [CommGroup GA] [CommGroup GB] (f : GA →* GB) (g : GB →* GA), 0 < d → (∀ a, g (f a) = a ^ d) → ∀ (u : Fin 4 → GA) (v : Fin 4 → GB), (∀ i, f (u i) * ∏ j, v j ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ j, f (∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i) * v j ^ d = 1) → ((∀ j, v j = 1) → ∀ j, ∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ i, u i = 1) ∧ ∀ j, v j = 1 := by
  intro d GA GB _ _ f g hd hgf u v hA hB hC
  have hxx : quat d * (quat d)ᵀ = (((d - 1 : ℕ) : ℤ)) • (1 : Matrix (Fin 4) (Fin 4) ℤ) :=
    quat_mul_transpose d
  have hxtx : (quat d)ᵀ * quat d = (((d - 1 : ℕ) : ℤ)) • (1 : Matrix (Fin 4) (Fin 4) ℤ) :=
    quat_transpose_mul d
  have hd1 : d = (d - 1) + 1 := by omega
  have hv : ∀ k, v k = 1 := by
    intro k
    have E : ∏ i, (f (u i) * ∏ j, v j ^ quat d j i) ^ quat d k i = 1 := by
      simp [hA]
    rw [Finset.prod_congr rfl fun i _ => mul_zpow (f (u i)) (∏ j, v j ^ quat d j i) (quat d k i),
      Finset.prod_mul_distrib] at E
    have E2 : ∏ i, (∏ j, v j ^ (quat d)ᵀ i j) ^ quat d k i = v k ^ (((d - 1 : ℕ) : ℤ)) := by
      rw [prod_prod_zpow_mul, hxx, prod_zpow_smul_one]
    simp only [Matrix.transpose_apply] at E2
    have hF : f (∏ i, u i ^ quat d k i) = ∏ i, f (u i) ^ quat d k i := by
      simp [map_prod, map_zpow]
    rw [E2, ← hF, zpow_natCast] at E
    have hBk := hB k
    rw [show v k ^ d = v k ^ (d - 1) * v k by rw [← pow_succ, ← hd1], ← mul_assoc, E, one_mul] at hBk
    exact hBk
  refine ⟨?_, hv⟩
  have hxu := hC hv
  intro l
  have E : ∏ k, (∏ i, u i ^ quat d k i) ^ (quat d)ᵀ l k = 1 := by
    simp [hxu]
  rw [prod_prod_zpow_mul, hxtx, prod_zpow_smul_one, zpow_natCast] at E
  have hfu : f (u l) = 1 := by
    have h := hA l
    simpa [hv] using h
  have hdu : u l ^ d = 1 := by
    rw [← hgf, hfu, map_one]
  rw [show u l ^ d = u l ^ (d - 1) * u l by rw [← pow_succ, ← hd1], E, one_mul] at hdu
  exact hdu

end GlobalTheory.ZarhinFam

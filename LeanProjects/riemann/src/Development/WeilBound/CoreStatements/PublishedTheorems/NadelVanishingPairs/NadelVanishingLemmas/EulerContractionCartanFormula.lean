import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDifferentialMulLogCoordinateWedgeStatement

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

private theorem dDR_iota_dlog_eq_zero (K : Type) [Field K] (u : Kˣ) :
    CechDR.dDR ℤ K (ExteriorAlgebra.ι K (dlog u)) = 0 := by
  have h1 : (ExteriorAlgebra.ι K (dlog u) : CechDR.DR ℤ K) =
      ((u : K)⁻¹) • CechDR.ι1 (KaehlerDifferential.D ℤ K (u : K)) := by
    show ExteriorAlgebra.ι K (((u⁻¹ : Kˣ) : K) • KaehlerDifferential.D ℤ K (u : K)) = _
    rw [map_smul, Units.val_inv_eq_inv_val]
  rw [h1, CechDR.dDR_smul, CechDR.dDR_D, smul_zero, add_zero, Derivation.leibniz_inv, map_smul,
    smul_mul_assoc]
  have h2 : (CechDR.ι1 (KaehlerDifferential.D ℤ K (u : K)) : CechDR.DR ℤ K) *
      CechDR.ι1 (KaehlerDifferential.D ℤ K (u : K)) = 0 := ExteriorAlgebra.ι_sq_zero _
  rw [h2, smul_zero]

private theorem dDR_prod_dlog_eq_zero_and_euler_contraction (K : Type) [Field K] {n : ℕ} (x : Fin n → Kˣ) (i : Fin n)
    (θ : abelian₂ K →ₗ[K] abelian₂ K) (hθ : IsEulerContraction x i θ) (l : List (Fin n)) :
    CechDR.dDR ℤ K (l.map (fun j => ExteriorAlgebra.ι K (dlog (x j)))).prod = 0 ∧
    CechDR.dDR ℤ K (θ (l.map (fun j => ExteriorAlgebra.ι K (dlog (x j)))).prod) = 0 := by
  have d1 : CechDR.dDR ℤ K (1 : CechDR.DR ℤ K) = 0 := by
    have h := CechDR.dDR_algebraMap (R := ℤ) (B := K) 1
    rw [map_one, Derivation.map_one_eq_zero, map_zero] at h
    exact h
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    refine ⟨d1, ?_⟩
    rw [hθ.1, map_zero]
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    refine ⟨?_, ?_⟩
    · rw [CechDR.dDR_mul, ih.1, dDR_iota_dlog_eq_zero, mul_zero, zero_mul, add_zero]
    · rw [hθ.2.1, hθ.2.2 a]
      split_ifs
      · rw [one_mul, map_sub, CechDR.dDR_mul, ih.1, ih.2, dDR_iota_dlog_eq_zero, mul_zero, zero_mul,
          add_zero, sub_self]
      · rw [zero_mul, zero_sub, map_neg, CechDR.dDR_mul, ih.2, dDR_iota_dlog_eq_zero, mul_zero, zero_mul,
          add_zero, neg_zero]

theorem euler_cartan_logWedge : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ) (i : Fin n)
    (θ : abelian₂ K →ₗ[K] abelian₂ K), IsEulerContraction x i θ → ∀ (c : K) (e : Fin n → K) (I : Finset (Fin n)),
    dK c = ∑ j, e j • dlog (x j) →
    extD K (θ (c • logWedge x I)) + θ (extD K (c • logWedge x I)) = e i • logWedge x I := by
  intro K _ n x i θ hθ c e I hc
  obtain ⟨hd, hdθ⟩ := dDR_prod_dlog_eq_zero_and_euler_contraction K x i θ hθ (I.sort (· ≤ ·))
  have hω : logWedge x I =
      ((I.sort (· ≤ ·)).map (fun j => ExteriorAlgebra.ι K (dlog (x j)))).prod := rfl
  rw [hω]
  generalize ((I.sort (· ≤ ·)).map (fun j => ExteriorAlgebra.ι K (dlog (x j)))).prod = ω at hd hdθ ⊢
  have hθc : θ (ExteriorAlgebra.ι K (KaehlerDifferential.D ℤ K c)) = e i • 1 := by
    have h : KaehlerDifferential.D ℤ K c = ∑ j, e j • dlog (x j) := hc
    rw [h, map_sum, map_sum]
    simp only [map_smul, hθ.2.2, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [extD_apply]
  rw [map_smul θ, CechDR.dDR_smul, CechDR.dDR_smul, hd, hdθ]
  simp only [smul_zero, add_zero]
  show _ + θ (ExteriorAlgebra.ι K (KaehlerDifferential.D ℤ K c) * ω) = _
  rw [hθ.2.1, hθc, smul_one_mul]
  show ExteriorAlgebra.ι K (KaehlerDifferential.D ℤ K c) * θ ω + (e i • ω - _) = _
  abel

end GlobalTheory

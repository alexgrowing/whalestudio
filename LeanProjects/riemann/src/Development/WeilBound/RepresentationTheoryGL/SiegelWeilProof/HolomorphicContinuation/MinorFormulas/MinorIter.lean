import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.MinorCore

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP.Mi

variable {R : Type} [CommRing R] {ρ : ℕ}

theorem del_C_mul (p q : Fin ρ) (r : R) (g : Pm R ρ) : del p q (C r * g) = C r * del p q g := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, MvPolynomial.derivation_C, mul_zero, add_zero]

theorem opE_C_mul' (α : R) (p q : Fin ρ) (r : R) (g : Pm R ρ) : opE α p q (C r * g) = C r * opE α p q g := by
  simp only [opE, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, del_C_mul]
  ring

theorem del_det_pow (p q : Fin ρ) (k : ℕ) :
    del p q ((Xm R ρ).det ^ k) = (k : Pm R ρ) * X (q, p) * (Xm R ρ).det ^ k := by
  rw [Derivation.leibniz_pow, delDet, smul_eq_mul, nsmul_eq_mul]
  rcases k with _ | k
  · simp
  · rw [pow_succ]
    push_cast
    ring

theorem opE_det_pow_mul (α : R) (p q : Fin ρ) (k : ℕ) (g : Pm R ρ) :
    opE α p q ((Xm R ρ).det ^ k * g) = (Xm R ρ).det ^ k * opE (α + k) p q g := by
  simp only [opE, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, del_det_pow]
  simp only [map_add, map_natCast]
  ring

theorem foldr_det_pow (α : R) (k : ℕ) (σ : Equiv.Perm (Fin ρ)) (L : List (Fin ρ)) (g : Pm R ρ) :
    (L.foldr (fun j h => opE α j (σ j) ∘ₗ h) LinearMap.id) ((Xm R ρ).det ^ k * g) =
      (Xm R ρ).det ^ k * (L.foldr (fun j h => opE (α + k) j (σ j) ∘ₗ h) LinearMap.id) g := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.foldr_cons, LinearMap.comp_apply, ih, opE_det_pow_mul]

theorem detE_det_pow_mul (α : R) (k : ℕ) (g : Pm R ρ) :
    detE α ((Xm R ρ).det ^ k * g) = (Xm R ρ).det ^ k * detE (α + k) g := by
  simp only [detE, LinearMap.sum_apply, LinearMap.smul_apply, foldr_det_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_smul_comm]

theorem foldr_C_mul (α : R) (r : R) (σ : Equiv.Perm (Fin ρ)) (L : List (Fin ρ)) (g : Pm R ρ) :
    (L.foldr (fun j h => opE α j (σ j) ∘ₗ h) LinearMap.id) (C r * g) =
      C r * (L.foldr (fun j h => opE α j (σ j) ∘ₗ h) LinearMap.id) g := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.foldr_cons, LinearMap.comp_apply, ih, opE_C_mul']

theorem detE_C_mul (α : R) (r : R) (g : Pm R ρ) : detE α (C r * g) = C r * detE α g := by
  simp only [detE, LinearMap.sum_apply, LinearMap.smul_apply, foldr_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_smul_comm]

theorem iter : Iter := by
  intro R _ ρ α N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih]
    have hc : (∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (C α + (l : Pm R ρ) - (i : Pm R ρ))) =
        C (∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (α + (l : R) - (i : R))) := by
      simp [map_prod]
    set r := ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (α + (l : R) - (i : R))
    have h1 : (C r : Pm R ρ) = C r * 1 := (mul_one _).symm
    rw [hc, mul_comm, detE_det_pow_mul, h1, detE_C_mul, core]
    rw [Finset.prod_range_succ, hc]
    simp only [map_prod, map_sub, map_add, map_natCast]
    ring

end PositivityTheory.Rg.Sw.SP.Mi

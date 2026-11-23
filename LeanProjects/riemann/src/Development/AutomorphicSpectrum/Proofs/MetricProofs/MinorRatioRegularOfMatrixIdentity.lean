import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetMemSubring
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

private theorem det_mul_eq_sum_prod_det_submatrix {Ω : Type} [Field Ω] {n r : ℕ}
    (B : Matrix (Fin r) (Fin n) Ω) (C : Matrix (Fin n) (Fin r) Ω) :
    (B * C).det = ∑ p : Fin r → Fin n, (∏ i, B i (p i)) * (C.submatrix p id).det := by
  have hsub : ∀ p : Fin r → Fin n, (C.submatrix p id).det =
      ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : Ω) * ∏ i, C (p i) (σ i) := by
    intro p
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  rw [← Matrix.det_transpose, Matrix.transpose_mul, Matrix.det_apply']
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Finset.mul_sum, hsub]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

private theorem det_submatrix_mul_det_eq_pow_mul {Ω : Type} [Field Ω] {n r : ℕ}
    (A C : Matrix (Fin n) (Fin r) Ω) (T : Matrix (Fin r) (Fin r) Ω) (a : Ω) (hAT : A * T = a • C)
    (J : Fin r → Fin n) :
    (A.submatrix J id).det * T.det = a ^ r * (C.submatrix J id).det := by
  have h1 : A.submatrix J id * T = a • C.submatrix J id := by
    ext i j
    have h := congrFun (congrFun hAT (J i)) j
    simpa [Matrix.mul_apply] using h
  rw [← Matrix.det_mul, h1, Matrix.det_smul, Fintype.card_fin]

theorem minor_isUnit_of_leftInverse : ∀ {Ω : Type} [Field Ω] {n r : ℕ} (R : Subring Ω) (A C : Matrix (Fin n) (Fin r) Ω)
    (B : Matrix (Fin r) (Fin n) Ω) (T : Matrix (Fin r) (Fin r) Ω) (a : Ω) (hAT : A * T = a • C) (ha : a ≠ 0)
    (hT : T.det ≠ 0) (hBC : B * C = 1) (hC : ∀ j l, C j l ∈ R) (hB : ∀ l j, B l j ∈ R) (J₀ : Fin r → Fin n)
    (hz : (A.submatrix J₀ id).det ≠ 0)
    (hr : ∀ J : Fin r → Fin n, (A.submatrix J id).det / (A.submatrix J₀ id).det ∈ R),
    (C.submatrix J₀ id).det ≠ 0 ∧ (C.submatrix J₀ id).det ∈ R ∧ (C.submatrix J₀ id).det⁻¹ ∈ R ∧
      (A.submatrix J₀ id).det * T.det = a ^ r * (C.submatrix J₀ id).det := by
  intro Ω _ n r R A C B T a hAT ha hT hBC hC hB J₀ hz hr
  have hrel : ∀ J : Fin r → Fin n,
      (A.submatrix J id).det * T.det = a ^ r * (C.submatrix J id).det :=
    det_submatrix_mul_det_eq_pow_mul A C T a hAT
  have har : a ^ r ≠ 0 := pow_ne_zero r ha
  have hC0 : (C.submatrix J₀ id).det ≠ 0 := by
    intro h0
    have h := hrel J₀
    rw [h0, mul_zero] at h
    exact mul_ne_zero hz hT h
  have hCR : (C.submatrix J₀ id).det ∈ R := by
    let M : Matrix (Fin r) (Fin r) R := Matrix.of fun i j => ⟨C (J₀ i) j, hC _ _⟩
    have hM : R.subtype.mapMatrix M = C.submatrix J₀ id := by
      ext i j
      rfl
    rw [← hM, ← RingHom.map_det]
    exact SetLike.coe_mem M.det
  have hratio : ∀ J : Fin r → Fin n, (C.submatrix J id).det =
      (C.submatrix J₀ id).det * ((A.submatrix J id).det / (A.submatrix J₀ id).det) := by
    intro J
    apply mul_left_cancel₀ har
    rw [← hrel J, show a ^ r * ((C.submatrix J₀ id).det *
        ((A.submatrix J id).det / (A.submatrix J₀ id).det)) =
        (a ^ r * (C.submatrix J₀ id).det) * ((A.submatrix J id).det / (A.submatrix J₀ id).det) by ring,
      ← hrel J₀]
    field_simp
  have hs := det_mul_eq_sum_prod_det_submatrix B C
  rw [hBC, Matrix.det_one] at hs
  have hs2 : (C.submatrix J₀ id).det * ∑ p : Fin r → Fin n,
      (∏ i, B i (p i)) * ((A.submatrix p id).det / (A.submatrix J₀ id).det) = 1 := by
    refine Eq.trans ?_ hs.symm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hratio p]
    ring
  refine ⟨hC0, hCR, ?_, hrel J₀⟩
  rw [inv_eq_of_mul_eq_one_right hs2]
  exact sum_mem fun p _ => mul_mem (prod_mem fun i _ => hB _ _) (hr p)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityHermitianMetrics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobiDensityWeightedThetaIntegralZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqFormDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeWeightedRootProductSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentTriangularFactor
import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero
open Filter Topology MeasureTheory Matrix
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (emb jacDens)
open GlobalTheory.FlagFibre (Low uni)
open GlobalTheory.FlagFormDeg (apolar)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell

theorem det_leading_mul_upper {R : Type} [CommRing R] {m : ℕ} (A B : Matrix (Fin m) (Fin m) R)
    (hB : B.BlockTriangular id) (l : Fin (m + 1)) :
    ((A * B).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det =
      (A.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det *
        (B.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det := by
  have hsplit : (A * B).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le) =
      A.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le) *
        B.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective _ (Fin.strictMono_castLE l.is_le).injective _ _ ?_ (fun _ => rfl)
    intro k hk
    have hkl : l.1 ≤ k.1 := by
      by_contra hc
      exact hk ⟨⟨k.1, lt_of_not_ge hc⟩, Fin.ext rfl⟩
    have hlt : Fin.castLE l.is_le j < k := by
      rw [Fin.lt_def]; exact lt_of_lt_of_le j.2 hkl
    have h0 : B k (Fin.castLE l.is_le j) = 0 := hB hlt
    rw [h0, mul_zero]
  rw [hsplit, Matrix.det_mul]

theorem exists_minors_ne_zero {m : ℕ} (h : Matrix (Fin m) (Fin m) ℂ) (hh : IsUnit h.det) :
    ∃ A : Matrix (Fin m) (Fin m) ℂ, ∀ l : Fin (m + 1),
      (A.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0 ∧
      ((h * A).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0 := by
  let Xm : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) ℂ) :=
    Matrix.of fun i j => MvPolynomial.X (i, j)
  let toM : (Fin m × Fin m → ℂ) → Matrix (Fin m) (Fin m) ℂ := fun a => Matrix.of fun i j => a (i, j)
  have hX : ∀ a, Xm.map (MvPolynomial.eval a) = toM a := by
    intro a; ext i j; simp [Xm, toM]
  have hhX : ∀ a, (h.map MvPolynomial.C * Xm).map (MvPolynomial.eval a) = h * toM a := by
    intro a
    rw [Matrix.map_mul, hX, Matrix.map_map]
    congr 1
    ext i j; simp
  have hsurj : ∀ B : Matrix (Fin m) (Fin m) ℂ, ∃ a, toM a = B :=
    fun B => ⟨fun p => B p.1 p.2, by ext i j; rfl⟩
  have key : ∀ (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) ℂ))
      (F : Matrix (Fin m) (Fin m) ℂ → Matrix (Fin m) (Fin m) ℂ),
      (∀ a, P.map (MvPolynomial.eval a) = F (toM a)) → ∀ l : Fin (m + 1),
      (∃ B, ((F B).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0) →
      ∀ᵐ a : Fin m × Fin m → ℂ, ((F (toM a)).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0 := by
    intro P F hP l ⟨B, hB⟩
    have hev : ∀ a, MvPolynomial.eval a (P.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det =
        ((F (toM a)).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det := by
      intro a
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, hP]
    obtain ⟨a0, ha0⟩ := hsurj B
    have hne : (P.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0 := by
      intro h0
      apply hB
      rw [← ha0, ← hev, h0, map_zero]
    filter_upwards [ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_linear (volume : Measure (Fin m × Fin m → ℂ))
      (LinearEquiv.refl ℂ _) _ hne] with a ha
    rw [← hev]; simpa using ha
  have hone : ∀ l : Fin (m + 1),
      ((1 : Matrix (Fin m) (Fin m) ℂ).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0 := by
    intro l
    rw [Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one]
    exact one_ne_zero
  have h1 : ∀ l : Fin (m + 1), ∀ᵐ a : Fin m × Fin m → ℂ,
      ((toM a).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0 := by
    intro l
    exact key Xm id hX l ⟨1, hone l⟩
  have h2 : ∀ l : Fin (m + 1), ∀ᵐ a : Fin m × Fin m → ℂ,
      ((h * toM a).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0 := by
    intro l
    refine key _ (fun B => h * B) hhX l ⟨h⁻¹, ?_⟩
    rw [Matrix.mul_nonsing_inv _ hh]
    exact hone l
  have hall : ∀ᵐ a : Fin m × Fin m → ℂ, ∀ l : Fin (m + 1),
      ((toM a).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0 ∧
      ((h * toM a).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0 := by
    rw [ae_all_iff]
    intro l
    filter_upwards [h1 l, h2 l] with a ha hb using ⟨ha, hb⟩
  obtain ⟨a, ha⟩ := hall.exists
  exact ⟨toM a, ha⟩

theorem ae_leading_minors_mul_uni_ne_zero : ∀ (m : ℕ) (g : Matrix (Fin m) (Fin m) ℂ), IsUnit g.det →
    ∀ᵐ x : Low m → ℂ, ∀ l : Fin (m + 1),
      ((g * uni x).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0 := by
  intro m g hg
  rw [ae_all_iff]
  intro l

  have hex : ∃ x : Low m → ℂ,
      ((g * uni x).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0 := by
    have hgi : IsUnit g⁻¹.det := by
      rw [Matrix.det_nonsing_inv]; exact (Ring.inverse_eq_inv g.det).symm ▸ hg.ringInverse
    obtain ⟨A, hA⟩ := exists_minors_ne_zero g⁻¹ hgi
    obtain ⟨n, b, hb, -, heq⟩ := exists_lu ℂ m (g⁻¹ * A) fun k => isUnit_iff_ne_zero.mpr (hA k).2
    have hA' : g * uniR n * b = A := by
      rw [Matrix.mul_assoc, ← heq, Matrix.mul_nonsing_inv_cancel_left _ _ hg]
    refine ⟨n, ?_⟩
    have h := (hA l).1
    rw [← hA', det_leading_mul_upper _ _ hb] at h
    rw [← uniR_eq_uni]
    exact left_ne_zero_of_mul h
  obtain ⟨x0, hx0⟩ := hex
  let P : Matrix (Fin m) (Fin m) (MvPolynomial (Low m) ℂ) :=
    g.map MvPolynomial.C * uniR (fun s => MvPolynomial.X s)
  have hev : ∀ x : Low m → ℂ,
      MvPolynomial.eval x (P.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det =
        ((g * uni x).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det := by
    intro x
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map]
    congr 2
    rw [Matrix.map_mul, map_uniR, Matrix.map_map, ← uniR_eq_uni]
    congr 1
    · ext i j; simp
    · congr 1; funext s; simp
  have hne : (P.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0 := by
    intro h0
    apply hx0
    rw [← hev, h0, map_zero]
  filter_upwards [ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_linear (volume : Measure (Low m → ℂ))
    (LinearEquiv.refl ℂ _) _ hne] with x hx
  rw [← hev]; simpa using hx

end GlobalTheory.FlagCell

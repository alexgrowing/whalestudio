import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MatrixAdditiveHaarNormalizedStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MatrixHaarRightTranslateStatement

open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.Vol

noncomputable def scalarInvGL {F : Type} [Field F] (m : ℕ) (x : F) (hx : x ≠ 0) : GL (Fin m) F :=
  Units.map (Matrix.scalar (Fin m) : F →+* Matrix (Fin m) (Fin m) F).toMonoidHom (Units.mk0 x⁻¹ (inv_ne_zero hx))

theorem coe_scalarInvGL {F : Type} [Field F] (m : ℕ) (x : F) (hx : x ≠ 0) :
    ((scalarInvGL m x hx : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = Matrix.diagonal (fun _ => x⁻¹) := by
  simp [scalarInvGL, Matrix.scalar_apply]

theorem preimage_intMat_eq {F : Type} [Field F] (O : Subring F) {ϖ : F} (hϖ : ϖ ≠ 0) (n m : ℕ) :
    (fun x : Matrix (Fin n) (Fin m) F => x * ((scalarInvGL m ϖ hϖ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) ⁻¹'
      intMat O n m = (IIset O ϖ : Set (Matrix (Fin n) (Fin m) F)) := by
  ext x
  simp only [Set.mem_preimage, intMat, Set.mem_setOf_eq, IIset, coe_scalarInvGL, Matrix.mul_diagonal]
  constructor
  · intro h i j
    exact ⟨x i j * ϖ⁻¹, h i j, by field_simp⟩
  · intro h i j
    obtain ⟨o, ho, e⟩ := h i j
    have : x i j * ϖ⁻¹ = o := by rw [e]; field_simp
    rw [this]; exact ho

theorem vol_IIset : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n m : ℕ, ∀ (dx : Measure (Matrix (Fin n) (Fin m) F)), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → dx (IIset O ϖ : Set (Matrix (Fin n) (Fin m) F)) = ENNReal.ofReal ((q : ℝ) ^ (-((n * m : ℕ) : ℤ))) := by
  intro F _ _ _ _ _ _ O ϖ nrm q hL n m dx hinv hone
  obtain ⟨hB, hOpen, -, -, -, -⟩ := GlobalTheory.T.matrix_additive_haar_normalized hL n m
  have hscale := (GlobalTheory.T.matrix_haar_right_translate hL n m dx hinv hone).1 (scalarInvGL m ϖ hL.ne)
  have hcont : Continuous (fun x : Matrix (Fin n) (Fin m) F =>
      x * ((scalarInvGL m ϖ hL.ne : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) :=
    continuous_id.matrix_mul continuous_const
  have hmap := congrArg (fun μ : Measure (Matrix (Fin n) (Fin m) F) => μ (intMat O n m)) hscale
  rw [Measure.map_apply hcont.measurable hOpen.measurableSet, preimage_intMat_eq O hL.ne n m] at hmap
  rw [hmap, Measure.smul_apply, hone, smul_eq_mul, mul_one]
  congr 1
  rw [coe_scalarInvGL, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    map_pow, map_inv₀, hL.nrm_pi, inv_inv, ← inv_pow, ← pow_mul, _root_.zpow_neg, zpow_natCast, inv_pow, mul_comm m n]

end GlobalTheory.CompanionTheory.QL.Vol

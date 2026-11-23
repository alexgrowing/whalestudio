import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitarySiegelParabolicBlockRelationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapTwoSidedMulHaarMatrixQuadraticExtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixColumnPairingAlgebraicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopologyStatement

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem blocks_of_weyl_mul_eq {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
    {ν : Type} [Fintype ν] [DecidableEq ν] {p q : UG c (stdJ ν E)} (hp : p ∈ sieg c ν) (hq : q ∈ sieg c ν)
    (h : weyl c ν * p = q * weyl c ν) :
    (mat c p).toBlocks₁₂ = 0 ∧ (mat c q).toBlocks₁₂ = 0 ∧ (mat c q).toBlocks₁₁ = (mat c p).toBlocks₂₂ := by
  have h1 : stdJ ν E * mat c p = mat c q * stdJ ν E := congrArg (mat c) h
  rw [← fromBlocks_toBlocks (mat c p), ← fromBlocks_toBlocks (mat c q), (mem_sieg c).mp hp, (mem_sieg c).mp hq,
    stdJ, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h1
  obtain ⟨h11, h12, -, h22⟩ := h1
  refine ⟨?_, ?_, ?_⟩
  · simpa using h22
  · simpa using h11
  · simpa using h12.symm

theorem fou_parFun_levi : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∀ p ∈ sieg c ν, ∀ q ∈ sieg c ν, weyl c ν * p = q * weyl c ν → ∀ φ : Matrix α ν E → ℂ, fou c ψ Q μ (parFun c ψ χ Q (mat c p) φ) = parFun c ψ χ Q (mat c q) (fou c ψ Q μ φ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ _ _ χ _ hχ _ _ μ _ p hp q hq hpq φ
  obtain ⟨hb, hb', ha'⟩ := blocks_of_weyl_mul_eq c hp hq hpq
  obtain ⟨had, -, -⟩ := GlobalTheory.T.splitUnitarySiegelParabolic_block_relations F E c δ hE ν p hp
  obtain ⟨β, hβ, -, -, hadj, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  obtain ⟨-, -, -, -, hsc, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hχ
  obtain ⟨-, hring, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  set a := (mat c p).toBlocks₁₁ with ha
  set d := (mat c p).toBlocks₂₂ with hd
  have hda : (d.map c)ᵀ * a = 1 := mul_eq_one_comm.mp had
  let A : GL ν E := ⟨a, (d.map c)ᵀ, had, hda⟩
  have hmap := GlobalTheory.T.map_twoSided_mul_haar_matrix_quadraticExt F E c δ hE α ν μ 1 A
  simp only [Units.val_one, Matrix.one_mul, map_one, one_pow, one_mul] at hmap
  let e : Matrix α ν E ≃ₜ Matrix α ν E :=
    { toFun := fun y => y * a
      invFun := fun y => y * (d.map c)ᵀ
      left_inv := fun y => by simp only [Matrix.mul_assoc, had, Matrix.mul_one]
      right_inv := fun y => by simp only [Matrix.mul_assoc, hda, Matrix.mul_one]
      continuous_toFun := continuous_id.matrix_mul continuous_const
      continuous_invFun := continuous_id.matrix_mul continuous_const }
  have hdet : d.det = (c a.det)⁻¹ := by
    have h1 : a.det * c d.det = 1 := by
      have := congrArg Matrix.det had
      rw [det_mul, det_transpose, det_one] at this
      rw [← this]
      congr 1
      exact RingHom.map_det (c : E →+* E) d
    have h2 := congrArg c h1
    rw [map_mul, hE.invol, map_one] at h2
    exact eq_inv_of_mul_eq_one_right h2
  have hsc' := hsc (Matrix.GeneralLinearGroup.det A)
  have hAdet : ((Matrix.GeneralLinearGroup.det A : Eˣ) : E) = a.det := rfl
  rw [hAdet, ← hdet] at hsc'
  have hN : nabs F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det A)) ≠ 0 :=
    (NNReal.coe_pos.mpr distribHaarChar_pos).ne'
  funext x
  have h0 : ∀ y : Matrix α ν E, pr c Q y 0 = 0 := fun y => by rw [← hβ, map_zero]
  have hint : ∫ y, ψ (pr c Q (x * d) (y * a)) * φ (y * a) ∂μ
      = (((nabs F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det A)) ^ Fintype.card α : ℝ) : ℂ))⁻¹
        * ∫ y, ψ (pr c Q (x * d) y) * φ y ∂μ := by
    have h1 := integral_map_equiv (μ := μ) e.toMeasurableEquiv (fun y => ψ (pr c Q (x * d) y) * φ y)
    have h2 : μ.map e.toMeasurableEquiv = _ := hmap
    rw [h2, integral_smul_nnreal_measure] at h1
    refine Eq.trans h1.symm ?_
    rw [NNReal.smul_def, Complex.real_smul]
    simp [nabs]
  have hpr : ∀ y : Matrix α ν E, pr c Q (x * d) (y * a) = pr c Q x y := fun y => by
    rw [← hβ, hadj, Matrix.mul_assoc, had, Matrix.mul_one, hβ]
  simp only [hpr] at hint
  simp only [fou, four, parFun, hb, hb', ha', ← ha, ← hd, Matrix.mul_zero, h0, mul_zero, AddChar.map_zero_eq_one, one_mul]
  simp only [mul_left_comm _ (sc F χ (Fintype.card α) a.det)]
  rw [integral_const_mul, hint, ← hsc', ← mul_assoc, mul_assoc (sc F χ _ d.det), mul_inv_cancel₀, mul_one]
  exact_mod_cast pow_ne_zero _ hN

end GlobalTheory.KSp

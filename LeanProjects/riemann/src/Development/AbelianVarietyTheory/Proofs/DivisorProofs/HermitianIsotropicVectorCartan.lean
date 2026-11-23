import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceComponentAdeleConjugationEqComplexConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxAdaptedPlaneEvaluation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicColumnsRingIsoComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueArchimedeanMatrixAdeleExtensionOfCom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAtOfPiInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAtEvIPiInfEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantFrameCommutesCartan
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.IwArchLocal

theorem iwasawa_arch_isotropic_line : ∀ {n : ℕ} (M θ g g' : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ), Mᴴ = M → IsCartan M θ → g * g' = 1 → gᵀ * M * g.map star = M → x ≠ 0 → x ⬝ᵥ M *ᵥ star x = 0 → ∃ k k' : Matrix (Fin n) (Fin n) ℂ, k * k' = 1 ∧ kᵀ * M * k.map star = M ∧ Commute k θ ∧ ∃ β : ℂ, β ≠ 0 ∧ (g * k') *ᵥ x = β • x := by
  intro n M θ g g' x hM hC hgg' hgM hx0 hxiso
  have hC' : Formalism.IndefR.Datum.IsCartanInv Mᵀ θ := GlobalTheory.MajFrameCartan.isCartanInv_transpose hM hC
  obtain ⟨b, ε, hb1, hb2⟩ := GlobalTheory.Doubling.exists_frame_of_isCartanInv hC'
  have hcT : ∀ {p q : Type} (N : Matrix p q ℂ), Formalism.UG.cT (starRingEnd ℂ) N = Nᴴ := fun N => by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  let gG : GL (Fin n) ℂ := ⟨g, g', hgg', mul_eq_one_comm.1 hgg'⟩
  have hgG : gG ∈ Formalism.UG.UJ (starRingEnd ℂ) Mᵀ := by
    show Formalism.UG.cT (starRingEnd ℂ) g * Mᵀ * g = Mᵀ
    rw [hcT]
    have := congrArg Matrix.transpose hgM
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.transpose_map] at this
    rw [Matrix.mul_assoc]; exact this
  let X : Matrix (Fin n) (Fin 1) ℂ := Matrix.of fun i _ => x i
  have hX : Formalism.UG.cT (starRingEnd ℂ) X * Mᵀ * X = 0 := by
    rw [hcT]
    ext i j
    fin_cases i; fin_cases j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, X, Matrix.of_apply,
      Matrix.zero_apply]
    rw [← hxiso]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  obtain ⟨k, hk, hku, β, hβ⟩ := GlobalTheory.Core.Rk.IwArch.iw_iso_cols (starRingEnd ℂ) (RingHom.id ℂ)
    Function.bijective_id (fun _ => rfl) b ε (by rw [hcT]; exact hb1) X hX gG hgG
  have hkG : k.1ᴴ * Mᵀ * k.1 = Mᵀ := by
    have h : Formalism.UG.cT (starRingEnd ℂ) k.1 * Mᵀ * k.1 = Mᵀ := hk
    rwa [hcT] at h
  have e : (g * (k⁻¹).1) *ᵥ x = β 0 0 • x := by
    funext i
    have h := congrFun (congrFun hβ i) 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_one] at h
    simp only [X, Matrix.of_apply] at h
    rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_comm]
    exact h
  refine ⟨k.1, (k⁻¹).1, Units.mul_inv k, ?_, ?_, β 0 0, ?_, e⟩
  · have := congrArg Matrix.transpose hkG
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at this
    rw [Matrix.conjTranspose, Matrix.transpose_map, Matrix.transpose_transpose] at this
    rw [← Matrix.mul_assoc] at this
    exact this
  · have hu : (b⁻¹ * k * b).1ᴴ * (b⁻¹ * k * b).1 = 1 := by
      have h : Formalism.UG.cT (starRingEnd ℂ) (b⁻¹ * k * b).1 * 1 * (b⁻¹ * k * b).1 = 1 := hku
      rwa [hcT, Matrix.mul_one] at h
    rw [Units.val_mul, Units.val_mul] at hu
    have := (GlobalTheory.Doubling.unitary_iff_commute (Units.mul_inv b) hb1
      (GlobalTheory.Doubling.diagonal_sign_mul_self ε) hkG).1 hu
    rwa [hb2] at this
  · intro h0
    rw [h0, zero_smul] at e
    apply hx0
    have hg'g : g' * g = 1 := mul_eq_one_comm.1 hgg'
    have hinv : (k.1 * g') * (g * (k⁻¹).1) = 1 := by
      calc (k.1 * g') * (g * (k⁻¹).1) = k.1 * (g' * g) * (k⁻¹).1 := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hg'g, Matrix.mul_one, Units.mul_inv]
    calc x = ((k.1 * g') * (g * (k⁻¹).1)) *ᵥ x := by rw [hinv, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, e, Matrix.mulVec_zero]

end GlobalTheory.IwArchLocal

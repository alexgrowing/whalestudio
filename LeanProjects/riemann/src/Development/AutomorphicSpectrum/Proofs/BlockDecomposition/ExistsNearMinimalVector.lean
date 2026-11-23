import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
import GroundTheory.AutomorphicForms.AnisotropicUnitaryHeight
import GroundTheory.AutomorphicForms.ReductionMahler

noncomputable section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov

open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic GroundTheory.Automorphic.Reduction

section NearMin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ}

def ratCoords [Algebra.IsQuadraticExtension F E] (u : Fin n → E) :
    Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F :=
  resVec (Module.finBasis F E) F (fun i => inclR (F := F) F (u i))

theorem hv_eq_adelicNorm_resVec [Algebra.IsQuadraticExtension F E] (ξ : Fin n → AF F ⊗[F] E) :
    hv (F := F) (E := E) ξ = adelicNorm (resVec (Module.finBasis F E) (AF F) ξ) := rfl

theorem ratCoords_ne_zero [Algebra.IsQuadraticExtension F E] {u : Fin n → E} (hu : u ≠ 0) :
    ratCoords (F := F) u ≠ 0 := by
  intro h0
  apply hu
  have h1 : (fun i => inclR (F := F) F (u i)) = fun _ : Fin n => (0 : F ⊗[F] E) := by
    apply resVec_injective (Module.finBasis F E) F
    rw [show resVec (Module.finBasis F E) F (fun i => inclR (F := F) F (u i)) = 0 from h0]
    funext p
    simp [resVec, coordsVec]
  funext i
  have h2 := congrFun h1 i
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F F).injective
    (h2.trans (map_zero _).symm)

theorem resVec_ratV [Algebra.IsQuadraticExtension F E] (u : Fin n → E) :
    resVec (Module.finBasis F E) (AF F) (ratV F u) = ratVec (ratCoords (F := F) u) := by
  have h := resVec_baseMap (Module.finBasis F E) (Algebra.ofId F (AF F))
    (fun i => inclR (F := F) F (u i))
  have e : (fun i => baseMap (Algebra.ofId F (AF F)) (inclR (F := F) F (u i))) = ratV F u := by
    funext i
    simp [ratV, inclR, baseMap]
  rw [e] at h
  rw [h]
  rfl

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

theorem exists_pos_le_hgt [Algebra.IsQuadraticExtension F E] (g : GAd σ J) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : Fin n → E, u ≠ 0 → c ≤ hgt σ J g u := by
  set T := trHom (Module.finBasis F E) (AF F) (matHom _ σ J g) with hT
  obtain ⟨P, hP, h⟩ := exists_adelicNorm_vecMul_le_mul (K := F) (C := {T⁻¹}) isCompact_singleton
  refine ⟨1 / P, one_div_pos.2 hP, fun u hu => ?_⟩
  have hx := ratCoords_ne_zero (F := F) hu
  have e2 : hgt σ J g u = adelicNorm (ratVec (ratCoords (F := F) u) ᵥ* (T : Matrix (Fin (Fintype.card (Fin n × Fin (Module.finrank F E))))
      (Fin (Fintype.card (Fin n × Fin (Module.finrank F E)))) (AF F))) := by
    rw [hT, ← resVec_ratV, resVec_vecMul_trHom, ← hv_eq_adelicNorm_resVec, hgt, map_inv]
  have h3 := h T⁻¹ rfl _ ((hasFiniteContent_ratVec hx).vecMul T)
  rw [← e2, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.vecMul_one] at h3
  rw [div_le_iff₀ hP, mul_comm]
  exact (one_le_adelicNorm_ratVec hx).trans h3

end NearMin

theorem exists_isotropic_of_isWittFrame {F E : Type} [Field F] [Field E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
    {X Y : Matrix (Fin n) (Fin (r + 1)) E} (h : IsWittFrame σ J X Y) :
    ∃ v : Fin n → E, v ≠ 0 ∧ hE σ J v v = 0 := by
  refine ⟨Xᵀ 0, fun h0 => ?_, ?_⟩
  · have h1 := congrFun (congrFun h.xy 0) 0
    have hc : ∀ i, X i 0 = 0 := fun i => congrFun h0 i
    simp [cT, Matrix.mul_apply, hc] at h1
  · have h1 := congrFun (congrFun h.xx 0) 0
    simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul, Matrix.zero_apply] at h1
    rw [Finset.sum_comm] at h1
    simpa [hE, Formalism.UG.hform] using h1

theorem exists_nearMin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ g : GAd σ J, ∃ v, NearMin σ J g v := by
  intro F E _ _ _ _ _ σ hCM n J _ r X Y hW g
  haveI : Algebra.IsQuadraticExtension F E := ⟨hCM.2.2.1⟩
  obtain ⟨c, hc, hlow⟩ := exists_pos_le_hgt σ J g
  obtain ⟨v₀, hv₀, hi₀⟩ := exists_isotropic_of_isWittFrame hW
  let S : Set ℝ := {t | ∃ u : Fin n → E, u ≠ 0 ∧ hE σ J u u = 0 ∧ t = hgt σ J g u}
  have hne : S.Nonempty := ⟨_, v₀, hv₀, hi₀, rfl⟩
  have hbdd : BddBelow S := ⟨c, by rintro _ ⟨u, hu, -, rfl⟩; exact hlow u hu⟩
  have hm : c ≤ sInf S := le_csInf hne (by rintro _ ⟨u, hu, -, rfl⟩; exact hlow u hu)
  have hm0 : 0 < sInf S := hc.trans_le hm
  obtain ⟨_, ⟨v, hv, hi, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne (show sInf S < 2 * sInf S by linarith)
  refine ⟨v, hv, hi, fun u hu hiu => ?_⟩
  have : sInf S ≤ hgt σ J g u := csInf_le hbdd ⟨u, hu, hiu, rfl⟩
  linarith

end GlobalTheory.CompanionTheory.RedCov

end

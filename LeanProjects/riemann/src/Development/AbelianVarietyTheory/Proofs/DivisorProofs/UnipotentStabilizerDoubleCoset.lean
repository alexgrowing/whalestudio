import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)

namespace GlobalTheory.EisCT

theorem form_mul_of_mem_unipRad {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (C : Matrix (Fin n) (Fin r) E)
    {ν : GAd σ J} (hν : ν ∈ unipRad σ J C) :
    adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J ν).1 = adMat F (cT (σ : E →+* E) C * J) := by
  unfold unipRad at hν
  induction hν using Subgroup.closure_induction with
  | mem g hg =>
    have h := hg.2.1
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    exact h
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul, Units.val_mul, ← Matrix.mul_assoc, ha, hb]
  | inv a _ ha =>
    conv_lhs => rw [← ha]
    rw [Matrix.mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.mul_one]

theorem not_orthL_of_stabL_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ w ∈ ratPts σ J, (matHom _ σ J w).1 * adMat F (col0 Y) = adMat F (col0 X) →
    ∀ ν ∈ unipRad σ J (col0 X), ∀ t : GAd σ J, GlobalTheory.EisCT.StabL σ J (col0 X) (w * ν * t⁻¹) →
    ¬ GlobalTheory.EisCT.OrthL σ J (col0 X) t := by
  intro F E _ _ _ _ _ σ n J r X Y _ _ hW w _ hw ν hν t hp horth
  obtain ⟨l, hl⟩ := hp
  have hxy : cT (σ : E →+* E) (col0 X) * J * col0 Y = 1 := by
    ext i j
    have h := congrFun (congrFun hW.xy 0) 0
    rw [Subsingleton.elim i j]
    simp only [Matrix.one_apply_eq] at h ⊢
    rw [← h]
    simp [Matrix.mul_apply, cT, col0]
  have hwi : (matHom _ σ J w⁻¹).1 * adMat F (col0 X) = adMat F (col0 Y) := by
    rw [← hw, ← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mul]
  have ht : t⁻¹ = ν⁻¹ * w⁻¹ * (w * ν * t⁻¹) := by group
  have hνi := form_mul_of_mem_unipRad σ J (col0 X) (inv_mem hν)
  unfold OrthL at horth
  rw [ht, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, hl,
    Matrix.mul_smul, Matrix.mul_assoc, hwi, Matrix.mul_smul, ← Matrix.mul_assoc, hνi] at horth
  unfold adMat at horth
  rw [← Matrix.map_mul, hxy] at horth
  have h0 := congrFun (congrFun horth 0) 0
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_eq, map_one, smul_eq_mul, mul_one,
    Matrix.zero_apply] at h0
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  haveI : Nontrivial (AF F ⊗[F] E) := inferInstance
  exact l.ne_zero h0

end GlobalTheory.EisCT

end

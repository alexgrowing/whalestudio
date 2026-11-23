import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EisCT

theorem exists_col0_ne_zero_of_witt {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y) :
    ∃ i, X i 0 ≠ 0 := by
  by_contra hc
  push_neg at hc
  have h1 := congrArg (fun M => M 0 0) hW.xy
  simp only [Matrix.one_apply_eq] at h1
  rw [Matrix.mul_apply] at h1
  simp [Matrix.mul_apply, Formalism.UG.cT, hc] at h1

theorem iwaHt_mul_rat_stabL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
    ∀ p ∈ ratPts σ J, GlobalTheory.EisCT.StabL σ J (col0 X) p → ∀ v, h (p * v) = h v := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS p hp hst v
  obtain ⟨-, -, -, -, hW, -, hI1, hI2⟩ := hS
  obtain ⟨lp, hlp⟩ := hst
  have key : absE F E lp = 1 := by
    rw [← range_ratEmb] at hp
    obtain ⟨γ, rfl⟩ := hp
    obtain ⟨i, hi⟩ := exists_col0_ne_zero_of_witt hW
    have hmat : (matHom _ σ J (ratEmb σ J γ)).1 = (γ.1.1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
      ext s t; rfl
    rw [hmat] at hlp
    have hent := congrArg (fun M => M i 0) hlp
    simp only [adMat] at hent
    rw [← RingHom.map_matrix_mul] at hent
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hent
    have hx : col0 X i 0 = X i 0 := rfl
    rw [hx] at hent
    set e : E := ((γ.1.1 : Matrix (Fin n) (Fin n) E) * col0 X) i 0 / X i 0 with he_def
    have he : inclR (F := F) (AF F) e * inclR (F := F) (AF F) (X i 0) =
        inclR (F := F) (AF F) (((γ.1.1 : Matrix (Fin n) (Fin n) E) * col0 X) i 0) := by
      rw [← map_mul, he_def, div_mul_cancel₀ _ hi]
    have hu : IsUnit (inclR (F := F) (AF F) (X i 0)) := (isUnit_iff_ne_zero.2 hi).map _
    have hl : lp.1 = inclR (F := F) (AF F) e := by
      rw [← he] at hent
      exact (hu.mul_left_inj.1 hent).symm
    by_cases he0 : e = 0
    · rw [he0, map_zero] at hl
      have : Subsingleton (AF F ⊗[F] E) := by
        have h01 := lp.mul_inv
        rw [hl, zero_mul] at h01
        exact subsingleton_of_zero_eq_one h01
      rw [Subsingleton.elim lp 1, map_one]
    · have := GlobalTheory.Doubling.absE_inclR (F := F) (E := E) (Units.mk0 e he0)
      rwa [show (Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 e he0)) = lp from
        Units.ext (by simp [hl])] at this
  obtain ⟨q, lq, hq, k, hk, rfl⟩ := hI1 v
  have e1 : h (q * k) = absE F E lq := hI2 q lq hq k hk
  have hpq : (matHom _ σ J (p * q)).1 * adMat F (col0 X) = (lp * lq).1 • adMat F (col0 X) := by
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hq, Matrix.mul_smul, hlp, smul_smul, Units.val_mul, mul_comm]
  have e2 : h (p * q * k) = absE F E (lp * lq) := hI2 (p * q) (lp * lq) hpq k hk
  rw [← mul_assoc, e2, e1, map_mul, key, one_mul]

end GlobalTheory.EisCT

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EisCT

section Swap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in
theorem cT_col0_mul_col0 (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (X Y : Matrix (Fin n) (Fin (r + 1)) E) :
    Formalism.UG.cT (σ : E →+* E) (col0 X) * J * col0 Y =
      Matrix.of fun _ _ => (Formalism.UG.cT (σ : E →+* E) X * J * Y) 0 0 := by
  ext i j
  simp [Matrix.mul_apply, Formalism.UG.cT, col0]

omit [NumberField F] [NumberField E] in
theorem cT_add' (σ : E →ₐ[F] E) {a b : Type} (M N : Matrix a b E) :
    Formalism.UG.cT (σ : E →+* E) (M + N) = Formalism.UG.cT (σ : E →+* E) M + Formalism.UG.cT (σ : E →+* E) N := by
  ext i j; simp [Formalism.UG.cT]

omit [NumberField F] [NumberField E] in
theorem cT_sub' (σ : E →ₐ[F] E) {a b : Type} (M N : Matrix a b E) :
    Formalism.UG.cT (σ : E →+* E) (M - N) = Formalism.UG.cT (σ : E →+* E) M - Formalism.UG.cT (σ : E →+* E) N := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_cT_of_isCMExt {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {a b : Type} (M : Matrix a b E) :
    Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) M) = M := by
  ext i j; simp [Formalism.UG.cT, GlobalTheory.SiegelSet.sigma_sigma hσ]

omit [NumberField F] [NumberField E] in
theorem cT_eq_of_isHermND {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) :
    Formalism.UG.cT (σ : E →+* E) J = J := by
  ext i j; simpa [Formalism.UG.cT] using hJ.1 i j

end Swap

theorem exists_ratPts_swap_col0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∃ w ∈ ratPts σ J, (matHom _ σ J w).1 * adMat F (col0 Y) = adMat F (col0 X) := by
  intro F E _ _ _ _ _ σ n J r X Y hσ hJ hW
  classical
  set x := col0 X with hxdef
  set y := col0 Y with hydef
  have hxx : Formalism.UG.cT (σ : E →+* E) x * J * x = 0 := by
    rw [hxdef, cT_col0_mul_col0, hW.xx]; ext i j; simp
  have hyy : Formalism.UG.cT (σ : E →+* E) y * J * y = 0 := by
    rw [hydef, cT_col0_mul_col0, hW.yy]; ext i j; simp
  have hxy : Formalism.UG.cT (σ : E →+* E) x * J * y = 1 := by
    rw [hxdef, hydef, cT_col0_mul_col0, hW.xy]; ext i j; simp [Matrix.one_apply, Subsingleton.elim i j]
  have hJ' := cT_eq_of_isHermND hJ
  have hyx : Formalism.UG.cT (σ : E →+* E) y * J * x = 1 := by
    have h := congrArg (Formalism.UG.cT (σ : E →+* E)) hxy
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT_of_isCMExt hσ, hJ', Formalism.UG.cT_one] at h
    simpa [Matrix.mul_assoc] using h
  set u := x - y with hu
  set v := Formalism.UG.cT (σ : E →+* E) u * J with hv
  have hvy : v * y = 1 := by
    rw [hv, hu, cT_sub', Matrix.sub_mul, Matrix.sub_mul, hxy, hyy, sub_zero]
  have hvx : v * x = -1 := by
    rw [hv, hu, cT_sub', Matrix.sub_mul, Matrix.sub_mul, hxx, hyx, zero_sub]
  set w0 : Matrix (Fin n) (Fin n) E := 1 + u * v with hw0
  have hw0y : w0 * y = x := by
    rw [hw0, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hvy, Matrix.mul_one, hu]; abel
  have hw0x : w0 * x = y := by
    rw [hw0, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hvx, Matrix.mul_neg, Matrix.mul_one, hu]; abel
  have hw0u : w0 * u = -u := by
    rw [hu, Matrix.mul_sub, hw0y, hw0x]; abel
  have hsq : w0 * w0 = 1 := by
    conv_lhs => rw [show w0 * w0 = w0 * (1 + u * v) from rfl]
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hw0u, hw0, Matrix.neg_mul]; abel
  have hcw : Formalism.UG.cT (σ : E →+* E) w0 * J = J * w0 := by
    rw [hw0, cT_add', Formalism.UG.cT_one, Formalism.UG.cT_mul, hv, Formalism.UG.cT_mul, cT_cT_of_isCMExt hσ, hJ',
      Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  have hunit : Formalism.UG.cT (σ : E →+* E) w0 * J * w0 = J := by
    rw [hcw, Matrix.mul_assoc, hsq, Matrix.mul_one]
  let U : GL (Fin n) E := ⟨w0, w0, hsq, hsq⟩
  have hU : U ∈ Formalism.UG.UJ (σ : E →+* E) J := hunit
  refine ⟨GlobalTheory.AdelicU.ratEmb σ J ⟨U, hU⟩, ?_, ?_⟩
  · rw [← GlobalTheory.AdelicU.range_ratEmb]; exact ⟨_, rfl⟩
  · change w0.map (inclR (F := F) (AF F)) * adMat F y = adMat F x
    simp only [adMat]
    rw [← Matrix.map_mul, hw0y]

end GlobalTheory.EisCT

end

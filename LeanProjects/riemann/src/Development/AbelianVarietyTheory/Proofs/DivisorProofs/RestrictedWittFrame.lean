import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeZeroTorus
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.EisRestrict
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EisRestrict

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem cT_mul_mulVec_apply {a : ℕ} (A : Matrix (Fin n) (Fin a) E) (K : Matrix (Fin n) (Fin n) E) (z : Fin n → E)
    (i : Fin a) : ((Formalism.UG.cT (σ : E →+* E) A * K) *ᵥ z) i = hE σ K (fun k => A k i) z := by
  rw [hE_eq_dot, ← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct, Formalism.UG.cT]

theorem cT_mul_mul_apply {a b : ℕ} (A : Matrix (Fin n) (Fin a) E) (K : Matrix (Fin n) (Fin n) E)
    (B : Matrix (Fin n) (Fin b) E) (i : Fin a) (j : Fin b) :
    (Formalism.UG.cT (σ : E →+* E) A * K * B) i j = hE σ K (fun k => A k i) (fun k => B k j) := by
  rw [← cT_mul_mulVec_apply]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

end GlobalTheory.EisRestrict

open GlobalTheory.EisRestrict in
theorem GlobalTheory.EisRestrict.isWittFrame_restrict : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    IsWittFrame σ (J0 σ J X Y) (X0 σ J X Y) (Y0 σ J X Y) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW
  have hyx := GlobalTheory.StdPar.yx (σ := σ) (J := J) (X := X) (Y := Y) h hJ hW
  have ent : ∀ (A B : Matrix (Fin n) (Fin (r + 1)) E) (i j : Fin (r + 1)),
      hE σ J (fun k => A k i) (fun k => B k j) = (Formalism.UG.cT (σ : E →+* E) A * J * B) i j :=
    fun A B i j => (cT_mul_mul_apply σ A J B i j).symm
  have c0X : GlobalTheory.EisMidHt.firstColumn X = fun k => X k 0 := rfl
  have c0Y : GlobalTheory.EisMidHt.firstColumn Y = fun k => Y k 0 := rfl
  have memX : ∀ j : Fin r, (fun k => X k j.succ) ∈ V0 σ J X Y := fun j => by
    rw [mem_invariant_forms, c0X, c0Y, ent, ent, hW.xx, hyx]
    simp [Matrix.one_apply, (Fin.succ_ne_zero j).symm]
  have memY : ∀ j : Fin r, (fun k => Y k j.succ) ∈ V0 σ J X Y := fun j => by
    rw [mem_invariant_forms, c0X, c0Y, ent, ent, hW.xy, hW.yy]
    simp [Matrix.one_apply, (Fin.succ_ne_zero j).symm]
  have iX := fun j => ι_coordTail σ J X Y X j (memX j)
  have iY := fun j => ι_coordTail σ J X Y Y j (memY j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    rw [cT_mul_mul_apply, hE_J0, iX, iX, ent, hW.xx]; rfl
  · ext i j
    rw [cT_mul_mul_apply, hE_J0, iY, iY, ent, hW.yy]; rfl
  · ext i j
    rw [cT_mul_mul_apply, hE_J0, iX, iY, ent, hW.xy]
    simp [Matrix.one_apply]
  · intro u h1 h2 h3
    apply ι_injective σ J X Y
    rw [map_zero]
    have hm := (mem_invariant_forms σ J X Y).1 (ι_mem σ J X Y u)
    apply hW.aniso
    · funext i
      rw [cT_mul_mulVec_apply]
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hm.1
      · have := congrFun h1 j
        rw [cT_mul_mulVec_apply, hE_J0, iX] at this
        simpa using this
    · funext i
      rw [cT_mul_mulVec_apply]
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hm.2
      · have := congrFun h2 j
        rw [cT_mul_mulVec_apply, hE_J0, iY] at this
        simpa using this
    · rw [← hE_J0]; exact h3

import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal

theorem phiW_inclL_E_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ) (Y : Matrix ι ι (OA l O)), (∀ i j, ∃ f : ZMod a → A O K, (∀ τ, (f τ : K⟦X⟧) = E K l e ^ α * P.mx τ i j) ∧ Y i j = ϖ.iTot t K f) → ∀ c : ι → OA l O, inclO l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) ^ α • phiW t ϖ P (inclL t ϖ P c) = inclL t ϖ P (Y.map (frobOA l O) *ᵥ fun i => frobOA l O (c i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P α Y hY c
  set s0 : OW l O := inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) with hs0

  have key : Y.map (inclO l O) = s0 ^ α • frobMat t ϖ P := by
    ext i j
    obtain ⟨f, hf, hYij⟩ := hY i j
    rw [Matrix.map_apply, hYij, ← ϖ.iW_of_mem t K, Matrix.smul_apply, smul_eq_mul, hs0, ← ϖ.iTot_E t K,
      ← ϖ.iW_of_mem t K, ← map_pow, frobMat, Matrix.map_apply, Matrix.of_apply, ← map_mul]
    congr 1
    funext τ
    apply Subtype.ext
    simp only [Pi.mul_apply, Pi.pow_apply, Subalgebra.coe_mul, Subalgebra.coe_pow, hf τ]
    rfl
  have key2 : (Y.map (frobOA l O)).map (inclO l O) =
      inclO l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) ^ α • (frobMat t ϖ P).map (frobOW l O) := by
    have h1 : (Y.map (frobOA l O)).map (inclO l O) = (Y.map (inclO l O)).map (frobOW l O) := by
      ext i j; simp only [Matrix.map_apply, frobOW_inclO]
    rw [h1, key]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, hs0, frobOW_inclO]
  rw [inclL_apply, phiW_apply, inclL_apply]
  have h2 : (fun i => frobOW l O ((frobMat t ϖ P *ᵥ fun i => inclO l O (c i)) i)) =
      (frobMat t ϖ P).map (frobOW l O) *ᵥ fun i => inclO l O (frobOA l O (c i)) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, frobOW_inclO]
  have h3 : (fun i => inclO l O ((Y.map (frobOA l O) *ᵥ fun i => frobOA l O (c i)) i)) =
      (Y.map (frobOA l O)).map (inclO l O) *ᵥ fun i => inclO l O (frobOA l O (c i)) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [h2, h3, key2, Matrix.smul_mulVec, Matrix.mulVec_smul]

end GlobalTheory.BKReal

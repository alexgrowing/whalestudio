import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

private lemma isIntegral_crd_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}
    {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (hs : IsSympl X bas) {v : Fin r → E}
    (hv : v ∈ X.Λ) (j : Fin g ⊕ Fin g) : IsIntegral ℤ (crd X bas v j) := by

  obtain ⟨m, rfl⟩ : ∃ m, (bas m : Fin r → E) = v := ⟨bas.symm ⟨v, hv⟩, by simp⟩
  rw [← vecQ_intCast X bas m, crd_vecQ hs]
  simpa using isIntegral_algebraMap (R := ℤ) (A := ℚ) (x := m j)

theorem heisG_fix_of_mem_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ φ : TF n g, IsSB φ → ∃ N : ℕ, 0 < N ∧ ∀ y : Matrix (Fin n) (Fin r) E, (∀ k, y k ∈ X.Λ) → ∀ j : ℕ, heisG X bas (((j * N : ℕ) : E) • y) φ = φ := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn φ hφ
  obtain ⟨R, hR, hlev⟩ := hφ
  refine ⟨2 * R, by omega, fun y hy j => ?_⟩

  have hmem : ∀ k, (j • y) k ∈ X.Λ := fun k => nsmul_mem (hy k) j
  have hsc : (((j * (2 * R) : ℕ) : E) • y) = (2 * R) • (j • y) := by
    rw [Nat.cast_smul_eq_nsmul, smul_smul]
    congr 1
    ring
  rw [hsc, GlobalTheory.SW.TensVac.heisG_eq hs, map_nsmul, Prod.smul_fst, Prod.smul_snd,
    ← Nat.cast_smul_eq_nsmul ℚ (2 * R) (GlobalTheory.SW.TensVac.crdHom hs (j • y)).1,
    ← Nat.cast_smul_eq_nsmul ℚ (2 * R) (GlobalTheory.SW.TensVac.crdHom hs (j • y)).2]
  exact GlobalTheory.SW.TensVac.heisS_fix hlev (fun k i => isIntegral_crd_of_mem hs (hmem k) (Sum.inl i))
    (fun k i => isIntegral_crd_of_mem hs (hmem k) (Sum.inr i))

end GlobalTheory.Ker

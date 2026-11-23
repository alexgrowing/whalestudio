import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfulRepMulVecInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceLsmulEqFinrankMulTraceStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem traceOnLattice_eq_rank_mul_trace : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (ρ : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]) (a : Λ), (ρ a).trace = (N : ℤ_[p]) * Algebra.trace ℤ_[p] Λ a := by
  intro p _ Λ _ _ _ _ _ _ N h hh ρ a
  let f : Λ →+* Module.End ℤ_[p] (Fin h → ℤ_[p]) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin h) (Fin h) ℤ_[p] ≃ₐ[ℤ_[p]] _).toAlgHom.comp ρ).toRingHom
  letI : Module Λ (Fin h → ℤ_[p]) := Module.compHom _ f
  have hsmul : ∀ (b : Λ) (x : Fin h → ℤ_[p]), b • x = (ρ b).mulVec x := fun b x => rfl
  haveI : IsScalarTower ℤ_[p] Λ (Fin h → ℤ_[p]) := ⟨fun r b x => by
    rw [hsmul, hsmul, map_smul]
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]⟩
  haveI : Module.Finite Λ (Fin h → ℤ_[p]) := Module.Finite.of_restrictScalars_finite ℤ_[p] Λ _
  haveI : NoZeroSMulDivisors Λ (Fin h → ℤ_[p]) := ⟨fun {b x} hbx => by
    by_cases hb : b = 0
    · exact Or.inl hb
    · exact Or.inr (GlobalTheory.T.faithful_rep_mulVec_injective ℤ_[p] Λ h ρ b x hb (by rw [← hsmul]; exact hbx))⟩
  haveI : Module.Free Λ (Fin h → ℤ_[p]) := Module.free_of_finite_type_torsion_free'
  haveI : Module.IsTorsionFree ℤ_[p] Λ :=
    NoZeroSMulDivisors.iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)
  haveI : Module.Free ℤ_[p] Λ := Module.free_of_finite_type_torsion_free'
  have hrank : Module.finrank Λ (Fin h → ℤ_[p]) = N := by
    have h1 := Module.finrank_mul_finrank ℤ_[p] Λ (Fin h → ℤ_[p])
    rw [Module.finrank_fin_fun] at h1
    have h2 := h1.trans hh
    have hpos : 0 < Module.finrank ℤ_[p] Λ := Module.finrank_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have key := GlobalTheory.T.trace_lsmul_eq_finrank_mul_trace ℤ_[p] Λ (Fin h → ℤ_[p]) a
  rw [hrank] at key
  rw [← key]
  have hlin : Algebra.lsmul ℤ_[p] ℤ_[p] (Fin h → ℤ_[p]) a = Matrix.toLin' (ρ a) := by
    exact LinearMap.ext fun x => hsmul a x
  rw [hlin, Matrix.trace_toLin'_eq]

end GlobalTheory

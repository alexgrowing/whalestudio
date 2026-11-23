import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissibleSupersetFinitePlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_admissiblePlaces_superset_and_mono : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F], 0 < p →
    (∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∃ S, S₀ ⊆ S ∧ AdmP p F S) ∧
      ∀ S T : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ T → AdmP p F S → AdmP p F T := by
  intro p F _ _ hp
  refine ⟨fun S₀ => ?_, fun S T hST h => ⟨h.1.mono hST, fun v hv => h.2 v fun a => hv (hST a)⟩⟩
  have hp0 : (p : F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  obtain ⟨S₁, h01, h1⟩ := exists_superset_mem_sUnits F {Units.mk0 (p : F) hp0} S₀
  obtain ⟨S, h1S, hS⟩ := exists_admissible_superset_finite_places F S₁
  refine ⟨S, h01.trans h1S, hS, ?_⟩
  exact (mem_sUnits F S _).1 (h1 S h1S _ (Finset.mem_singleton_self _))

end GlobalTheory.CNorm

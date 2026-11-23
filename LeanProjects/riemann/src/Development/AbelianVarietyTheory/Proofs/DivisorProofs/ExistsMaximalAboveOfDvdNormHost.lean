import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalComponentUnitaryMatrix
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq

open NumberField

namespace GlobalTheory.MaximalIdealDividingNorm

theorem exists_maximal_above_of_dvd_norm {K : Type*} [Field K] [NumberField K]
    (𝔪 : Ideal (𝓞 K)) {p : ℕ} (hp : p.Prime) (hd : p ∣ Ideal.absNorm 𝔪) :
    ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ 𝔪 ≤ P ∧ (p : 𝓞 K) ∈ P := by
  obtain ⟨P, hmax, hunder, hdiv⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp 𝔪 hd
  refine ⟨P, hmax, Ideal.le_of_dvd hdiv, ?_⟩
  have h1 : (p : ℤ) ∈ Ideal.under ℤ P := by
    rw [hunder]
    exact Ideal.mem_span_singleton_self _
  have h2 : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P := Ideal.mem_comap.mp h1
  rwa [map_natCast] at h2

theorem exists_maximal_above_of_dvd_norm_host (D : Formalism.BasicNotions.D7)
    (𝔪 : Ideal (𝓞 (Formalism.BasicNotions.D7.host D).E)) (_h𝔪 : 𝔪 ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Ideal.absNorm 𝔪) :
    ∃ P : Ideal (𝓞 (Formalism.BasicNotions.D7.host D).E),
      P.IsMaximal ∧ 𝔪 ≤ P ∧ (p : 𝓞 (Formalism.BasicNotions.D7.host D).E) ∈ P :=
  exists_maximal_above_of_dvd_norm 𝔪 hp hd

end GlobalTheory.MaximalIdealDividingNorm

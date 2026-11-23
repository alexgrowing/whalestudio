import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

theorem isLattice_comap_mulVecLin_of_leftInverse (E : Type) [Field E] [NumberField E] (n n₁ : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (ι : Matrix (Fin n) (Fin n₁) E)
    (P : Matrix (Fin n₁) (Fin n) E) (hPι : P * ι = 1) (hL : L.IsLattice E) :
    (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))).IsLattice E := by
  set f : (Fin n₁ → E) →ₗ[𝓞 E] (Fin n → E) := (Matrix.mulVecLin ι).restrictScalars (𝓞 E) with hf
  set g : (Fin n → E) →ₗ[𝓞 E] (Fin n₁ → E) := (Matrix.mulVecLin P).restrictScalars (𝓞 E) with hg
  have hgf : ∀ u, g (f u) = u := by
    intro u
    simp [hf, hg, Matrix.mulVec_mulVec, hPι]
  constructor
  · have hN : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian L hL.fg
    have h1 : ((L.comap f).map f).FG :=
      isNoetherian_submodule.1 hN _ (Submodule.map_comap_le f L)
    have h2 : ((L.comap f).map f).map g = L.comap f := by
      rw [← Submodule.map_comp]
      ext u
      simp only [Submodule.mem_map, LinearMap.coe_comp, Function.comp_apply, hgf]
      exact ⟨fun ⟨v, hv, he⟩ => he ▸ hv, fun hu => ⟨u, hu, rfl⟩⟩
    rw [← h2]
    exact h1.map g
  · rw [eq_top_iff]
    intro u _
    have hu : f u ∈ Submodule.span E (L : Set (Fin n → E)) := by
      rw [hL.span_eq_top]; trivial
    obtain ⟨y, hy, z, hz⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 E))).1 hu
    rw [Submodule.span_eq] at hy
    have hz0 : (algebraMap (𝓞 E) E (z : 𝓞 E)) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors z.2
    have hmem : (z : 𝓞 E) • u ∈ L.comap f := by
      have hc : (z : 𝓞 E) • IsLocalization.mk' E (1 : 𝓞 E) z = 1 := by
        rw [Algebra.smul_def, mul_comm, IsLocalization.mk'_spec, map_one]
      rw [Submodule.mem_comap, LinearMap.map_smul, hz, ← smul_assoc, hc, one_smul]
      exact hy
    have hsp : (z : 𝓞 E) • u ∈ Submodule.span E ((L.comap f : Submodule (𝓞 E) (Fin n₁ → E)) : Set (Fin n₁ → E)) :=
      Submodule.subset_span hmem
    have hu' : u = (algebraMap (𝓞 E) E (z : 𝓞 E))⁻¹ • ((z : 𝓞 E) • u) := by
      rw [← algebraMap_smul E (z : 𝓞 E) u, smul_smul, inv_mul_cancel₀ hz0, one_smul]
    rw [hu']
    exact Submodule.smul_mem _ _ hsp

end GlobalTheory

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinHeightSmulInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsEvEqProdNormZpow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisTail
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory

theorem fracIdeal_smul_mem_exists {E : Type} [Field E] [NumberField E] {n : ℕ}
    (B : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (B : Set (Fin n → E))) :
    ∃ s : 𝓞 E, s ≠ 0 ∧ s • x ∈ B := by
  first
  | exact @_root_.GlobalTheory.UnitaryNormalization.main
  | exact _root_.GlobalTheory.UnitaryNormalization.main
  | (apply _root_.GlobalTheory.UnitaryNormalization.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitaryNormalization.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitaryNormalization.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitaryNormalization.main ..)

theorem fracIdeal_of_lattice_smul_mem : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsLattice E L → ∀ u : Fin n → E, u ≠ 0 →
      ∃ I : FractionalIdeal (𝓞 E)⁰ E, I ≠ 0 ∧ ∀ c : E, c ∈ I ↔ c • u ∈ L := by
  intro E _ _ n L hL u hu
  let f : E →ₗ[𝓞 E] (Fin n → E) := (LinearMap.toSpanSingleton E (Fin n → E) u).restrictScalars (𝓞 E)
  have hf : Function.Injective f := smul_left_injective E hu
  let M : Submodule (𝓞 E) E := L.comap f
  have hLn : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian L hL.fg
  have hMfg : M.FG := by
    apply Submodule.fg_of_fg_map_injective f hf
    exact isNoetherian_submodule.mp hLn _ (Submodule.map_comap_le f L)
  have hfr : IsFractional (𝓞 E)⁰ M := FractionalIdeal.isFractional_of_fg hMfg
  let I : FractionalIdeal (𝓞 E)⁰ E := ⟨M, hfr⟩
  refine ⟨I, ?_, fun c => Iff.rfl⟩
  have hu' : u ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; exact Submodule.mem_top
  obtain ⟨d, hd, hdu⟩ := fracIdeal_smul_mem_exists L u hu'
  intro h0
  have hmem : algebraMap (𝓞 E) E d ∈ I := by
    show algebraMap (𝓞 E) E d • u ∈ L
    rw [algebraMap_smul]; exact hdu
  rw [h0, FractionalIdeal.mem_zero_iff] at hmem
  exact hd ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mp hmem)

end GlobalTheory

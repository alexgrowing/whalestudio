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

theorem restricted_exists_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (v : Fin n → E) : ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := hΛ ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨d', hd', h'⟩ := hy
    refine ⟨d * d', mul_ne_zero hd hd', ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem _ h
    · rw [mul_smul]; exact Λ.smul_mem _ h'
  | smul a x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) a
    refine ⟨q.1 * d, mul_ne_zero (nonZeroDivisors.ne_zero q.2) hd, ?_⟩
    have : (q.1 * d) • a • x = p • d • x := by
      simp only [← algebraMap_smul E (q.1 * d), ← algebraMap_smul E p, ← algebraMap_smul E d x, smul_smul, map_mul]
      rw [← hpq]
      congr 1
      ring
    rw [this]
    exact Λ.smul_mem _ h

theorem restrictedLattice_isLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), GlobalTheory.EisLine.IsAdapted σ J X Y L a →
    Submodule.IsLattice E (L0 σ J X Y L) := by
  intro F E _ _ _ _ _ σ n J r X Y _ _ _ L a hA
  have hL := hA.lat
  let f := (ι σ J X Y).restrictScalars (𝓞 E)
  have hf : Function.Injective f := ι_injective σ J X Y
  refine ⟨?_, ?_⟩
  · apply Submodule.fg_of_fg_map_injective f hf
    haveI : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian L hL.fg
    have hle : (L0 σ J X Y L).map f ≤ L := Submodule.map_comap_le f L
    haveI : IsNoetherian (𝓞 E) ((L0 σ J X Y L).map f) := isNoetherian_of_le hle
    exact Module.Finite.iff_fg.mp inferInstance
  · rw [eq_top_iff]
    intro u _
    obtain ⟨d, hd, hdu⟩ := restricted_exists_smul_mem L hL.span_eq_top (ι σ J X Y u)
    have hmem : d • u ∈ L0 σ J X Y L := by
      change f (d • u) ∈ L
      rw [map_smul]; exact hdu
    have hd' : (algebraMap (𝓞 E) E d) ≠ 0 := by
      simpa using hd
    have : u = (algebraMap (𝓞 E) E d)⁻¹ • (d • u) := by
      rw [← algebraMap_smul E d u, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.EisRestrict

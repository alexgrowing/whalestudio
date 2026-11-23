import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaleInto
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

namespace GlobalTheory.LatRankAdd

open Module

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_smul_mem_of_mem_span (W : Submodule (𝓞 K) V) {x : V}
    (hx : x ∈ Submodule.span K (W : Set V)) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ W := by
  first
  | exact @_root_.GlobalTheory.ScaleIntoUnitBall.scale_into
  | exact _root_.GlobalTheory.ScaleIntoUnitBall.scale_into
  | (apply _root_.GlobalTheory.ScaleIntoUnitBall.scale_into <;> assumption)
  | (intros; apply _root_.GlobalTheory.ScaleIntoUnitBall.scale_into <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ScaleIntoUnitBall.scale_into <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ScaleIntoUnitBall.scale_into ..)

theorem span_inf_ker {V' : Type} [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
    [IsScalarTower (𝓞 K) K V'] (q : V →ₗ[K] V') (W : Submodule (𝓞 K) V) :
    Submodule.span K ((W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V)
      = Submodule.span K (W : Set V) ⊓ LinearMap.ker q := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨hW, hk⟩
    exact ⟨Submodule.subset_span hW, hk⟩
  · rintro x ⟨hx, hk⟩
    obtain ⟨d, hd, h⟩ := exists_smul_mem_of_mem_span W hx
    have hdK : (algebraMap (𝓞 K) K d) ≠ 0 := by
      simpa using (IsFractionRing.injective (𝓞 K) K).ne hd
    have hmem : d • x ∈ (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) := by
      refine ⟨h, ?_⟩
      show q (d • x) = 0
      rw [← algebraMap_smul K d x, map_smul]
      have hk' : q x = 0 := hk
      rw [hk', smul_zero]
    have : x = (algebraMap (𝓞 K) K d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hdK, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem span_map {V' : Type} [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
    [IsScalarTower (𝓞 K) K V'] (q : V →ₗ[K] V') (W : Submodule (𝓞 K) V) :
    Submodule.span K ((W.map (q.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V') : Set V')
      = (Submodule.span K (W : Set V)).map q := by
  rw [Submodule.map_coe, Submodule.map_span]
  rfl

end GlobalTheory.LatRankAdd

open GlobalTheory.LatRankAdd in

theorem GlobalTheory.latRank_eq_latRank_inf_ker_add_latRank_map :
    ∀ (K : Type) [Field K] [NumberField K] (m m' : ℕ) (q : (Fin m → K) →ₗ[K] (Fin m' → K))
      (W : Submodule (𝓞 K) (Fin m → K)),
      latRank K W = latRank K (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K))
        + latRank K (W.map (q.restrictScalars (𝓞 K))) := by
  intro K _ _ m m' q W
  unfold latRank
  rw [span_inf_ker q W, span_map q W]
  set S := Submodule.span K (W : Set (Fin m → K))
  rw [add_comm, ← (q.domRestrict S).finrank_range_add_finrank_ker, LinearMap.range_domRestrict,
    LinearMap.ker_domRestrict, ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]

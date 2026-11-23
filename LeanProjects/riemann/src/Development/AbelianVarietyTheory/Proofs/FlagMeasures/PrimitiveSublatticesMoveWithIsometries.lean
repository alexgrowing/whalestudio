import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimMove

section

variable {R K : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]

theorem discN_congr {V W : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (k : W →ₗ⋆[K] W →ₗ[K] K) (e : V ≃ₗ[K] W)
    (he : ∀ x y, k (e x) (e y) = h x y) (A : Submodule R V) (B : Submodule R W)
    (hAB : ∀ x, e x ∈ B ↔ x ∈ A) : discN k B = discN h A := by
  have hd : ∀ x, e x ∈ dual k B ↔ x ∈ dual h A := by
    intro x
    unfold dual Formalism.E.hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    constructor
    · intro H y hy
      rw [← he]
      exact H _ ((hAB y).2 hy)
    · intro H y hy
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [he]
      exact H _ ((hAB z).1 hy)
  have hm : ∀ (A : Submodule R V) (B : Submodule R W), (∀ x, e x ∈ B ↔ x ∈ A) →
      B.toAddSubgroup = A.toAddSubgroup.map (e : V →+ W) := by
    intro A B H
    ext y
    obtain ⟨z, rfl⟩ := e.surjective y
    constructor
    · intro hy
      exact ⟨z, (H z).1 hy, rfl⟩
    · rintro ⟨w, hw, hwz⟩
      have : e w = e z := hwz
      rw [← this]
      exact (H w).2 hw
  unfold discN idxN
  rw [hm A B hAB, hm _ _ hd]
  exact AddSubgroup.relIndex_map_map_of_injective (f := (e : V →+ W)) _ _ e.injective

variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem smul_mem_smul_iff (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule R V) (x : V) :
    (g : V ≃ₗ[K] V) x ∈ g • L ↔ x ∈ L := by
  constructor
  · rintro ⟨w, hw, hwx⟩
    have : w = x := (g : V ≃ₗ[K] V).injective hwx
    exact this ▸ hw
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem smul_mem_primSp (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule R V)
    (U : Submodule K V) (j n : ℕ) : g • U ∈ primSp h (g • L) j n ↔ U ∈ primSp h L j n := by
  let e : U ≃ₗ[K] (g • U : Submodule K V) := (g : V ≃ₗ[K] V).submoduleMap U
  have he : ∀ x : U, (e x : V) = (g : V ≃ₗ[K] V) x := fun _ => rfl
  have h1 : Module.finrank K (g • U : Submodule K V) = Module.finrank K U := e.finrank_eq.symm
  have h2 : discN (hRes h (g • U)) (latIn (g • U) (g • L)) = discN (hRes h U) (latIn U L) := by
    refine discN_congr _ _ e (fun x y => ?_) _ _ (fun x => ?_)
    · exact g.2 (x : V) (y : V)
    · exact smul_mem_smul_iff h g L (x : V)
  change _ ∧ _ ↔ _ ∧ _
  rw [h1, h2]

end

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (g : isom h) (L : Submodule (𝓞 K) V) (U : Submodule K V) (j n : ℕ), (g • U ∈ primSp h (g • L) j n ↔ U ∈ primSp h L j n) ∧ (primSp h (g • L) j n).encard = (primSp h L j n).encard := by
  intro K V _ _ _ _ _ _ _ _ h _ _ _ g L U j n
  refine ⟨smul_mem_primSp h g L U j n, ?_⟩
  have hi : primSp h (g • L) j n = (fun W : Submodule K V => g • W) '' primSp h L j n := by
    ext W
    constructor
    · intro hW
      refine ⟨g⁻¹ • W, ?_, smul_inv_smul g W⟩
      rw [← smul_mem_primSp h g, smul_inv_smul]
      exact hW
    · rintro ⟨W', hW', rfl⟩
      exact (smul_mem_primSp h g L W' j n).2 hW'
  rw [hi]
  exact (MulAction.injective g).encard_image _

end GlobalTheory.Mass.PrimMove

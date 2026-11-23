import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsOrbitSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAffineCoverOfQuotient
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem isProjOver_of_isProper_of_affine_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsProper s]
    {L : LB X} (hL : L.IsLB) {n : ℕ} (σ : Fin n → LB.Sec L) (ha : ∀ i, IsAffineOpen (Out.nonzeroLocus (σ i)))
    (hc : ⨆ i, Out.nonzeroLocus (σ i) = ⊤) : IsProjOver s := by
  have hA : IsAmpleLB L := by
    refine ⟨hL, ⟨?_⟩, ?_⟩
    · have hu : (Set.univ : Set X) = ⋃ i, (Out.nonzeroLocus (σ i) : Set X) := by
        rw [← TopologicalSpace.Opens.coe_iSup, hc]
        rfl
      rw [hu]
      exact isCompact_iUnion fun i => (ha i).isCompact
    · intro x
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← hc] at hx
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      refine ⟨1, le_rfl, secToPow (σ i) 1, ?_, ?_⟩
      · rw [nonzeroLocus_secToPow (σ i) le_rfl]
        exact hi
      · rw [nonzeroLocus_secToPow (σ i) le_rfl]
        exact ha i
  exact hA.isProjOver s

theorem isProjOver_quotient : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (s' : X' ⟶ Sp R), IsProjOver (π ≫ s') → IsProjOver s' := by
  intro Γ _ _ X X' ρ π hq R _ _ s' hX
  have hQ : IsAffineQuotient ρ π :=
    ⟨hq.2.1, hq.1, fun W => (hq.2.2 W).1, fun W f hf => (hq.2.2 W).2 f (by
      unfold IsInvariantSection at hf
      exact fun g _ => (hf g).2)⟩
  have hP : IsProper (π ≫ s') := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hX).1
  have hs' : IsProper s' := hQ.isProper s'
  have hXs : X.IsSeparated := by
    constructor
    rw [show terminal.from X = (π ≫ s') ≫ terminal.from (Sp R) from terminal.hom_ext _ _]
    infer_instance
  obtain ⟨L, n, σ, hL, ha, ho⟩ := exists_sections_orbit_subset_nonzeroLocus Γ R X (π ≫ s') ρ hX
  obtain ⟨L', n', σ', hL', ha', hc'⟩ :=
    QuotientNorm.exists_affine_cover_of_quotient Γ X X' ρ π hq hXs L n σ hL ha ho
  exact isProjOver_of_isProper_of_affine_cover s' hL' σ' ha' hc'

end GlobalTheory

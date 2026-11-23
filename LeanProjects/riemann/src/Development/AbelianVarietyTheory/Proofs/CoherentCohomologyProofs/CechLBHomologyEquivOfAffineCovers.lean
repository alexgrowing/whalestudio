import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AcyclicSliceSecCubeOfIsAffineOpen

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.AbLaw

variable {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) {M : LB Y}
  {ν κ : Type} [LinearOrder ν] [LinearOrder κ]

def sliceEmptySecCubeIso (M : LB Y) (E : ν → Y.Opens) (e : κ ↪o ν) {s₀ : Finset ν} (h₀ : s₀ = ∅) :
    Cube.slice e s₀ (secCube f M E) ≅ secCube f M fun k => E (e k) :=
  have h (t : Finset κ) : ⨅ i ∈ s₀ ∪ t.map e.toEmbedding, E i = ⨅ k ∈ t, E (e k) := by
    subst h₀
    rw [Finset.empty_union]
    refine le_antisymm (le_iInf₂ fun k hk => biInf_le _ (Finset.mem_map_of_mem _ hk))
      (le_iInf₂ fun i hi => ?_)
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 hi
    exact biInf_le (fun k => E (e k)) hk
  Cube.isoMk (fun t => LinearEquiv.ofBijective (SecOnR.restrict f M (h t).ge)
      (SecOnR.restrict_bijective f (h t).ge (h t).le))
    fun {s t} _ x => (SecOnR.restrict_restrict f _ (h t).ge x).trans
      (SecOnR.restrict_restrict f (h s).ge _ x).symm

theorem acyclic_slice_secCube_of_isSeparated [Fintype κ] (hM : M.IsLB) [IsSeparated f]
    (E : ν → Y.Opens) (hE : ∀ i, IsAffineOpen (E i)) (e : κ ↪o ν) (hc : ⨆ k, E (e k) = ⊤)
    {s₀ : Finset ν} (h₀ : s₀.Nonempty) :
    (cubeComplex (Cube.slice e s₀ (secCube f M E))).Acyclic := by
  have : IsSeparated (terminal.from Y) := by
    rw [← terminal.comp_from f]
    infer_instance
  refine acyclic_slice_secCube_of_isAffineOpen R Y f M ν κ E e s₀ hM (hc ▸ le_top) fun t => ?_
  exact IsAffineOpen.biInf _ (Finset.finite_toSet _)
    (h₀.mono Finset.subset_union_left) fun i _ => hE i

theorem cechLB_homology_equiv_of_affine_covers :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (κ' : Type) [LinearOrder κ'] [Fintype κ'] (D' : κ' → Y.Opens), M.IsLB → IsSeparated f → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ i, IsAffineOpen (D' i)) → ⨆ i, D' i = ⊤ → ∀ n, Nonempty ((cechLB f M D).homology n ≃ₗ[R] (cechLB f M D').homology n) := by
  intro R _ Y f M κ _ _ D κ' _ _ D' hM hf hD hc hD' hc' n
  let E : κ ⊕ₗ κ' → Y.Opens := fun u => Sum.elim D D' (ofLex u)
  have hE (u : κ ⊕ₗ κ') : IsAffineOpen (E u) := by
    rcases u with i | i
    exacts [hD i, hD' i]
  let e₁ := trunc₂HomologyIsoFst (secCube f M E) (fun s hs =>
    acyclic_slice_secCube_of_isSeparated f hM E hE (Cube.inrEmb κ κ') hc' hs.map) n
  let e₂ := trunc₂HomologyIsoSnd (secCube f M E) (fun t ht => by
    rw [Cube.sliceFst_eq_slice]
    exact acyclic_slice_secCube_of_isSeparated f hM E hE (Cube.inlEmb κ κ') hc ht.map) n
  let i₁ : Cube.sliceFst (secCube f M E) ∅ ≅ secCube f M D :=
    eqToIso (Cube.sliceFst_eq_slice _ _) ≪≫
      sliceEmptySecCubeIso f M E (Cube.inlEmb κ κ') (Finset.map_empty _)
  let i₂ : Cube.sliceSnd (secCube f M E) ∅ ≅ secCube f M D' :=
    sliceEmptySecCubeIso f M E (Cube.inrEmb κ κ') (Finset.map_empty _)
  exact ⟨((HomologicalComplex.homologyMapIso ((cechFunctor κ R).mapIso i₁) n).symm ≪≫ e₁.symm ≪≫
    e₂ ≪≫ HomologicalComplex.homologyMapIso ((cechFunctor κ' R).mapIso i₂) n).toLinearEquiv⟩

end GlobalTheory.AbLaw

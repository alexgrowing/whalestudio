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

section

variable {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) {M : LB Y}
  {ν κ : Type}

theorem isAffineOpen_biInf_of_le (E : ν → Y.Opens)
    (hE : ∀ i V, IsAffineOpen V → IsAffineOpen (E i ⊓ V)) (u : Finset ν) {V : Y.Opens}
    (hV : IsAffineOpen V) (h : ⨅ i ∈ u, E i ≤ V) : IsAffineOpen (⨅ i ∈ u, E i) := by
  classical
  rw [← inf_eq_left.2 h]
  clear h
  induction u using Finset.induction_on with
  | empty => simpa using hV
  | insert a s _ ih =>
    rw [Finset.iInf_insert, inf_assoc]
    exact hE a _ ih

theorem acyclic_comap_secCube [LinearOrder ν] [LinearOrder κ] [Fintype κ] (hM : M.IsLB)
    (E : ν → Y.Opens) (hE : ∀ i V, IsAffineOpen V → IsAffineOpen (E i ⊓ V)) (e : κ ↪o ν)
    (hc : ⨆ k, E (e k) = ⊤) (s₀ : Finset ν) {V : Y.Opens} (hV : IsAffineOpen V)
    (h : ⨅ i ∈ s₀, E i ≤ V) (g : Finset κ → Finset ν) (hg : Monotone g)
    (hgs : ∀ t, g t = s₀ ∪ t.map e.toEmbedding) :
    (cubeComplex (Cube.comap g hg (secCube f M E))).Acyclic := by
  rw [Cube.comap_congr hg (Cube.monotone_union_map e s₀) hgs]
  exact acyclic_slice_secCube_of_isAffineOpen R Y f M ν κ E e s₀ hM (hc ▸ le_top) fun t =>
    isAffineOpen_biInf_of_le E hE _ hV
      ((iInf_le_iInf_of_subset E Finset.subset_union_left).trans h)

variable (M) in

def comapSecCubeIso (E : ν → Y.Opens) (D : κ → Y.Opens) (g : Finset κ → Finset ν) (hg : Monotone g)
    (h : ∀ t, ⨅ i ∈ g t, E i = ⨅ k ∈ t, D k) :
    Cube.comap g hg (secCube f M E) ≅ secCube f M D :=
  Cube.isoMk (fun t => LinearEquiv.ofBijective (SecOnR.restrict f M (h t).ge)
      (SecOnR.restrict_bijective f (h t).ge (h t).le))
    fun hst x => (SecOnR.restrict_restrict f (iInf_le_iInf_of_subset E (hg hst)) (h _).ge x).trans
      (SecOnR.restrict_restrict f (h _).ge (iInf_le_iInf_of_subset D hst) x).symm

theorem biInf_sumVertex [LinearOrder ν] [LinearOrder κ] (E : ν ⊕ₗ κ → Y.Opens) (s : Finset ν)
    (t : Finset κ) : ⨅ i ∈ Cube.sumVertex s t, E i =
      (⨅ i ∈ s, E (toLex (Sum.inl i))) ⊓ ⨅ k ∈ t, E (toLex (Sum.inr k)) := by
  apply le_antisymm
  · exact le_inf (le_iInf₂ fun i hi => iInf₂_le _ (Cube.inl_mem_sumVertex.2 hi))
      (le_iInf₂ fun i hi => iInf₂_le _ (Cube.inr_mem_sumVertex.2 hi))
  · refine le_iInf₂ fun i hi => ?_
    obtain ⟨i | i, rfl⟩ := toLex.surjective i
    · exact inf_le_left.trans (iInf₂_le _ (Cube.inl_mem_sumVertex.1 hi))
    · exact inf_le_right.trans (iInf₂_le _ (Cube.inr_mem_sumVertex.1 hi))

end

theorem cechLB_homology_equiv_trunc₂ :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (κ₁ : Type) [LinearOrder κ₁] [Fintype κ₁] (U : κ₁ → Y.Opens) (κ₂ : Type) [LinearOrder κ₂] [Fintype κ₂] (W : κ₂ → Y.Opens), M.IsLB → IsSeparated f → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ⨆ i, U i = ⊤ → ⨆ j, W j = ⊤ → (∀ i V, IsAffineOpen V → IsAffineOpen (U i ⊓ V)) → (∀ j V, IsAffineOpen V → IsAffineOpen (W j ⊓ V)) → (∀ i j, IsAffineOpen (U i ⊓ W j)) → ∀ n, Nonempty ((cechLB f M D).homology n ≃ₗ[R] (cubeComplex (Cube.trunc₂ (secCube f M fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u)))).homology (n + 2)) := by
  intro R _ Y f M κ _ _ D κ₁ _ _ U κ₂ _ _ W hM hf hD cD cU cW hU hW hUW n
  have hY : Y.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let E : (κ₁ ⊕ₗ κ₂) ⊕ₗ κ → Y.Opens := fun u =>
    Sum.elim (fun v : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex v)) D (ofLex u)
  have hE : ∀ i V, IsAffineOpen V → IsAffineOpen (E i ⊓ V) := by
    rintro ((i | j) | k) V hV
    · exact hU i V hV
    · exact hW j V hV
    · exact (hD k).inf hV
  let A := secCube f M E
  let e₁ := trunc₃HomologyIsoDropLast A (fun s t ⟨i, hi⟩ ⟨j, hj⟩ =>
    acyclic_comap_secCube f hM E hE (Cube.inrEmb _ _) cD
      ((Cube.sumVertex s t).map (Cube.inlEmb _ _).toEmbedding) (hUW i j)
      (le_inf
        (iInf₂_le (toLex (Sum.inl (toLex (Sum.inl i))))
          (Finset.mem_map_of_mem _ (Cube.inl_mem_sumVertex.2 hi)))
        (iInf₂_le (toLex (Sum.inl (toLex (Sum.inr j))))
          (Finset.mem_map_of_mem _ (Cube.inr_mem_sumVertex.2 hj))))
      _ (fun _ _ h => Cube.sumVertex_mono (subset_refl _) h) fun _ => rfl) (n + 2)
  let e₂ := trunc₃HomologyIsoDropFirst A (fun t w _ ⟨k, hk⟩ =>
    acyclic_comap_secCube f hM E hE (Cube.firstEmb _ _ _) cU
      ((Cube.sumVertex t w).map (Cube.lastTwoEmb _ _ _).toEmbedding) (hD k)
      (iInf₂_le (toLex (Sum.inr k)) (Finset.mem_map_of_mem _ (Cube.inr_mem_sumVertex.2 hk)))
      (fun s => Cube.sumVertex (Cube.sumVertex s t) w)
      (fun _ _ h => Cube.sumVertex_mono (Cube.sumVertex_mono h (subset_refl _)) (subset_refl _))
      fun s => (Cube.map_lastTwoEmb_union s t w).symm) (n + 2)
  let e₃ := trunc₂HomologyIsoSnd (Cube.lowerFace (Cube.lastTwoEmb κ₁ κ₂ κ) A) (fun w ⟨k, hk⟩ =>
    acyclic_comap_secCube f hM E hE ((Cube.inlEmb κ₂ κ).trans (Cube.lastTwoEmb κ₁ κ₂ κ)) cW
      (w.map (Cube.inrEmb _ _).toEmbedding) (hD k)
      (iInf₂_le (toLex (Sum.inr k)) (Finset.mem_map_of_mem _ hk))
      (fun t => (Cube.sumVertex t w).map (Cube.lastTwoEmb κ₁ κ₂ κ).toEmbedding)
      (fun _ _ h => Finset.map_subset_map.2 (Cube.sumVertex_mono h (subset_refl _)))
      fun t => by
        rw [Cube.sumVertex, Finset.map_union, Finset.map_map, Finset.map_map, Finset.union_comm]
        rfl) n
  let e₄ : Cube.sliceFst A ∅ ≅ secCube f M fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u) :=
    comapSecCubeIso f M E _ _ (fun _ _ h => Cube.sumVertex_mono h (subset_refl _)) fun t => by
      rw [biInf_sumVertex]
      simp [E]
  let e₅ : Cube.sliceSnd A (Cube.sumVertex ∅ ∅) ≅ secCube f M D :=
    comapSecCubeIso f M E _ _ (fun _ _ h => Cube.sumVertex_mono (subset_refl _) h) fun t => by
      rw [biInf_sumVertex]
      simp [E, Cube.sumVertex]
  exact ⟨((cechHomologyMapIso
    (eqToIso (Cube.sliceSnd_lowerFace_lastTwoEmb A ∅) ≪≫ e₅) n).symm ≪≫ e₃.symm ≪≫ e₂.symm ≪≫ e₁ ≪≫
      cubeHomologyMapIso (Cube.trunc₂Iso e₄.hom fun _ _ _ _ =>
        ConcreteCategory.bijective_of_isIso (e₄.hom.app _)) (n + 2)).toLinearEquiv⟩

end GlobalTheory.AbLaw

import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RangeRestrictCompSubtypeOfOrthogonalOfNe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineOpenBiInfOfLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSecOnRTensorEquiv

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem isAffineOpen_preimage_inf_of_isSeparated {Y Z : Scheme.{0}} [Y.IsSeparated] (p : Z ⟶ Y)
    {U : Y.Opens} (hU : IsAffineOpen U) {V : Z.Opens} (hV : IsAffineOpen V) :
    IsAffineOpen (p ⁻¹ᵁ U ⊓ V) := by
  have : IsAffine V := hV
  have : IsAffineHom ((V.ι ≫ p) ≫ terminal.from Y) := inferInstance
  have : IsAffineHom (V.ι ≫ p) := IsAffineHom.of_comp _ (terminal.from Y)
  have h := (hU.preimage (V.ι ≫ p)).image_of_isOpenImmersion V.ι
  rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_comm] at h

theorem rs_coord_pullLE_restrict {Y Z : Scheme.{0}} {M : LB Y} (p : Z ⟶ Y) {V V' : Y.Opens}
    {O O' B B' : Z.Opens} (h : V' ≤ V) (hO : O' ≤ O) (e : O ≤ p ⁻¹ᵁ V) (e' : O' ≤ p ⁻¹ᵁ V')
    (a : SecOn M V) (j : (M.pull p).ι) (h₁ : B' ≤ O' ⊓ (M.pull p).U j)
    (h₂ : B ≤ O ⊓ (M.pull p).U j) (h₃ : B' ≤ B) :
    rs Z h₁ (GlobalTheory.LB.coord (SecOn.pullLE M p V' O' e' (SecOn.restrict M h a)) j) =
      rs Z h₃ (rs Z h₂ (GlobalTheory.LB.coord (SecOn.pullLE M p V O e a) j)) := by
  rw [SecOn.pullLE_restrict, ← SecOn.restrict_pullLE p e hO, SecOn.coord_restrict, rs_rs, rs_rs]

theorem finrank_cechLB_homology_extProd : ∀ (K : Type) [Field K] (Y Y' Z : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of K)) (f' : Y' ⟶ Spec (CommRingCat.of K)) (p₁ : Z ⟶ Y) (p₂ : Z ⟶ Y') (M : LB Y) (M' : LB Y'), IsPullback p₁ p₂ f f' → M.IsLB → M'.IsLB → IsSeparated f → IsSeparated f' → ∀ (κ₁ : Type) [LinearOrder κ₁] [Fintype κ₁] (U : κ₁ → Y.Opens) (κ₂ : Type) [LinearOrder κ₂] [Fintype κ₂] (W : κ₂ → Y'.Opens) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Z.Opens), (∀ i, IsAffineOpen (U i)) → ⨆ i, U i = ⊤ → (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = ⊤ → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ n, Module.Finite K ((cechLB f M U).homology n)) → (∀ n, Module.Finite K ((cechLB f' M' W).homology n)) → ∀ n, Module.finrank K ((cechLB (p₁ ≫ f) (tw (M.pull p₁) (M'.pull p₂) 1) D).homology n) = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, Module.finrank K ((cechLB f M U).homology x.1) * Module.finrank K ((cechLB f' M' W).homology x.2) := by
  intro K _ Y Y' Z f f' p₁ p₂ M M' H hM hM' hf hf' κ₁ _ _ U κ₂ _ _ W κ _ _ D hU cU hW cW hD cD hA hB n
  have hY : Y.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have hY' : Y'.IsSeparated := ⟨by rw [← terminal.comp_from f']; infer_instance⟩
  have hp₁ : IsSeparated p₁ := MorphismProperty.of_isPullback H.flip hf'
  obtain ⟨e⟩ := cechLB_homology_equiv_trunc₂ K Z (p₁ ≫ f) (tw (M.pull p₁) (M'.pull p₂) 1) κ D
    κ₁ (fun i => p₁ ⁻¹ᵁ U i) κ₂ (fun j => p₂ ⁻¹ᵁ W j)
    (isLB_tw (LB.isLB_pull hM p₁) (LB.isLB_pull hM' p₂) 1) inferInstance hD cD
    (by rw [← Scheme.Hom.preimage_iSup, cU]; rfl) (by rw [← Scheme.Hom.preimage_iSup, cW]; rfl)
    (fun i V hV => isAffineOpen_preimage_inf_of_isSeparated p₁ (hU i) hV)
    (fun j V hV => isAffineOpen_preimage_inf_of_isSeparated p₂ (hW j) hV)
    (fun i j => ExtProd.isAffineOpen_inf H (hU i) (hW j)) n
  rw [e.finrank_eq]
  let E : κ₁ ⊕ₗ κ₂ → Z.Opens := fun u =>
    Sum.elim (fun i => p₁ ⁻¹ᵁ U i) (fun j => p₂ ⁻¹ᵁ W j) (ofLex u)
  have hO (s : Finset κ₁) (t : Finset κ₂) : ⨅ i ∈ Cube.sumVertex s t, E i =
      p₁ ⁻¹ᵁ (⨅ i ∈ s, U i) ⊓ p₂ ⁻¹ᵁ (⨅ j ∈ t, W j) := by
    rw [biInf_sumVertex, preimage_biInf, preimage_biInf]
    rfl
  have hs (s : Finset κ₁) (h : s.Nonempty) : IsAffineOpen (⨅ i ∈ s, U i) :=
    IsAffineOpen.biInf (s : Set κ₁) s.finite_toSet h fun i _ => hU i
  have ht (t : Finset κ₂) (h : t.Nonempty) : IsAffineOpen (⨅ j ∈ t, W j) :=
    IsAffineOpen.biInf (t : Set κ₂) t.finite_toSet h fun j _ => hW j
  choose m hm using fun (s : Finset κ₁) (t : Finset κ₂) (h : s.Nonempty) (h' : t.Nonempty) =>
    exists_secOnR_tensor_equiv K Y Y' Z f f' p₁ p₂ M M' H hM hM' _ _ _
      ((hO s t).le.trans inf_le_left) ((hO s t).le.trans inf_le_right) (hs s h) (ht t h') (hO s t)
  refine (cech_kuenneth_of_bijective (secCube f M U) (secCube f' M' W)
    (secCube (p₁ ≫ f) (tw (M.pull p₁) (M'.pull p₂) 1) E)
    (fun s t h h' => (m s t h h').toLinearMap) (fun s t h h' => (m s t h h').bijective)
    (fun {s s' t t'} h₁ h₂ h h' a b => SecOn.tw_ext fun p l => ?_) hA hB n).2
  have hE := iInf_le_iInf_of_subset E (Cube.sumVertex_mono h h')
  refine (hm s' t' (h₁.mono h) (h₂.mono h') (SecOn.restrict M (iInf_le_iInf_of_subset U h) a)
    (SecOn.restrict M' (iInf_le_iInf_of_subset W h') b) p l).trans
    (Eq.trans ?_ (congrArg (rs Z (inf_le_inf_right _ hE)) (hm s t h₁ h₂ a b p l)).symm)
  rw [map_mul]
  exact congrArg₂ (· * ·) (rs_coord_pullLE_restrict p₁ _ hE _ _ a p _ _ _)
    (rs_coord_pullLE_restrict p₂ _ hE _ _ b l _ _ _)

end GlobalTheory.AbLaw

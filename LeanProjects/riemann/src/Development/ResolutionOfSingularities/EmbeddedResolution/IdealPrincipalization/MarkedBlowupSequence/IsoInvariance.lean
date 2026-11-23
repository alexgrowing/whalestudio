import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem exists_isIso_subschemeι_eq_comp_of_eq_ker {A X : Scheme.{u}} (g : A ⟶ X)
    [IsClosedImmersion g] (I : X.IdealSheafData) (hI : I = g.ker) :
    ∃ φ : I.subscheme ⟶ A, IsIso φ ∧ I.subschemeι = φ ≫ g := by
  subst hI
  have : Mono g := inferInstance
  have : Mono (Scheme.Hom.ker g).subschemeι := inferInstance
  have h1 : Scheme.Hom.ker g ≤ Scheme.Hom.ker (Scheme.Hom.ker g).subschemeι :=
    le_of_eq (Scheme.IdealSheafData.ker_subschemeι _).symm
  have h2 : Scheme.Hom.ker (Scheme.Hom.ker g).subschemeι ≤ Scheme.Hom.ker g :=
    le_of_eq (Scheme.IdealSheafData.ker_subschemeι _)
  have hφ : IsClosedImmersion.lift g (Scheme.Hom.ker g).subschemeι h1 ≫ g
      = (Scheme.Hom.ker g).subschemeι := by simp
  have hψ : IsClosedImmersion.lift (Scheme.Hom.ker g).subschemeι g h2
      ≫ (Scheme.Hom.ker g).subschemeι = g := by simp
  refine ⟨IsClosedImmersion.lift g (Scheme.Hom.ker g).subschemeι h1,
    ⟨⟨IsClosedImmersion.lift (Scheme.Hom.ker g).subschemeι g h2, ?_, ?_⟩⟩, hφ.symm⟩
  · rw [← cancel_mono (Scheme.Hom.ker g).subschemeι, Category.assoc, hψ, hφ, Category.id_comp]
  · rw [← cancel_mono g, Category.assoc, hφ, hψ, Category.id_comp]

private theorem iso_inv_base_hom_base_apply {X Y : Scheme.{u}} (e : X ≅ Y) (x : X) :
    e.inv.base (e.hom.base x) = x := by
  simp

private theorem iso_hom_base_inv_base_apply {X Y : Scheme.{u}} (e : X ≅ Y) (y : Y) :
    e.hom.base (e.inv.base y) = y := by
  simp

private theorem isIso_resLE_iso_hom {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens) :
    IsIso (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl) := by
  have h1 : U ≤ (Opens.map e.inv.base).obj ((Opens.map e.hom.base).obj U) := by
    intro y hy
    show e.hom.base (e.inv.base y) ∈ U
    rw [iso_hom_base_inv_base_apply e y]
    exact hy
  refine ⟨e.inv.resLE ((Opens.map e.hom.base).obj U) U h1, ?_, ?_⟩
  · rw [← cancel_mono (Scheme.Opens.ι ((Opens.map e.hom.base).obj U)), Category.assoc,
      Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
      e.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [← cancel_mono (Scheme.Opens.ι U), Category.assoc,
      Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
      e.inv_hom_id, Category.comp_id, Category.id_comp]

theorem orderAtLeastLocus_comap_iso_hom_eq_preimage {X Y : Scheme.{u}} (e : X ≅ Y) (J : Y.IdealSheafData) (n : ℕ) :
    orderAtLeastLocus (J.comap e.hom) n = ⇑e.hom.base ⁻¹' orderAtLeastLocus J n := by
  have hJ : (J.comap e.hom).comap e.inv = J := by
    rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id]
  ext x
  have h1 := orderAt_le_orderAt_comap e.hom J x
  have h2 := orderAt_le_orderAt_comap e.inv (J.comap e.hom) (e.hom.base x)
  rw [iso_inv_base_hom_base_apply e x, hJ] at h2
  simp only [Set.mem_preimage, mem_orderAtLeastLocus_iff]
  exact ⟨fun hm => le_trans hm h2, fun hm => le_trans hm h1⟩

theorem strictTransform_comp_iso_hom {X X₁ Y : Scheme.{u}} (π : X₁ ⟶ X) (e : X ≅ Y)
    (Z D : Y.IdealSheafData) :
    Blowup.strictTransform (π ≫ e.hom) Z D = Blowup.strictTransform π (Z.comap e.hom) (D.comap e.hom) := by
  have hZ : Z.comap (π ≫ e.hom) = (Z.comap e.hom).comap π := by
    rw [Scheme.IdealSheafData.comap_comp]
  have hD : D.comap (π ≫ e.hom) = (D.comap e.hom).comap π := by
    rw [Scheme.IdealSheafData.comap_comp]
  rw [Blowup.strictTransform_eq_ker, Blowup.strictTransform_eq_ker, Blowup.strictTransformImmersion_eq,
    Blowup.strictTransformImmersion_eq, Blowup.strictTransformOpens_eq, Blowup.strictTransformOpens_eq, hZ, hD]

theorem smooth_comap_iso {k : Type u} [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) (Z : Y.IdealSheafData)
    (h : AlgebraicGeometry.Smooth (Z.subschemeι ≫ q)) :
    AlgebraicGeometry.Smooth ((Z.comap e.hom).subschemeι ≫ e.hom ≫ q) := by
  have hsq : Limits.pullback.fst e.hom Z.subschemeι =
      Limits.pullback.snd e.hom Z.subschemeι ≫ Z.subschemeι ≫ e.inv := by
    rw [← Category.assoc, ← Limits.pullback.condition, Category.assoc, e.hom_inv_id,
      Category.comp_id]
  have hsnd : IsIso (Limits.pullback.snd e.hom Z.subschemeι) := inferInstance
  have hci : IsClosedImmersion (Limits.pullback.fst e.hom Z.subschemeι) := by
    rw [hsq]; infer_instance
  obtain ⟨φ, hφ, hcomm⟩ :=
    exists_isIso_subschemeι_eq_comp_of_eq_ker (Limits.pullback.fst e.hom Z.subschemeι)
      (Z.comap e.hom) rfl
  have := hφ
  have hc2 : (Z.comap e.hom).subschemeι ≫ e.hom =
      (φ ≫ Limits.pullback.snd e.hom Z.subschemeι) ≫ Z.subschemeι := by
    rw [hcomm, Category.assoc, Category.assoc, Limits.pullback.condition]
  rw [← Category.assoc, hc2, Category.assoc]
  have : IsIso (φ ≫ Limits.pullback.snd e.hom Z.subschemeι) := inferInstance
  have : AlgebraicGeometry.Smooth (Z.subschemeι ≫ q) := h
  infer_instance

theorem restrictIdeal_comap {X Y : Scheme.{u}} (f : X ⟶ Y) (J : Y.IdealSheafData) (U : Y.Opens) :
    restrictIdeal (J.comap f) ((Opens.map f.base).obj U) =
      (restrictIdeal J U).comap (f.resLE U ((Opens.map f.base).obj U) le_rfl) := by
  rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, Scheme.Hom.resLE_comp_ι]

private theorem ofIso_map_comp_affineSpaceFinToSpec {k : Type u} [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) {U : Y.Opens} {m : ℕ}
    (c : EtaleChart q U m) :
    (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl ≫ c.map) ≫ affineSpaceFinToSpec k m =
      Scheme.Opens.ι ((Opens.map e.hom.base).obj U) ≫ (e.hom ≫ q) := by
  rw [Category.assoc, c.comp_struct, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]

private theorem etale_resLE_comp_map_of_iso {k : Type u} [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) {U : Y.Opens} {m : ℕ}
    (c : EtaleChart q U m) :
    AlgebraicGeometry.Etale
      (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl ≫ c.map) := by
  have : IsIso (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl) := isIso_resLE_iso_hom e U
  have : AlgebraicGeometry.Etale (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl) :=
    inferInstance
  have : AlgebraicGeometry.Etale c.map := c.isEtale
  infer_instance

def EtaleChart.ofIso {k : Type u} [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) {U : Y.Opens} {m : ℕ}
    (c : EtaleChart q U m) : EtaleChart (e.hom ≫ q) ((Opens.map e.hom.base).obj U) m where
  map := e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl ≫ c.map
  comp_struct := ofIso_map_comp_affineSpaceFinToSpec q e c
  isEtale := etale_resLE_comp_map_of_iso q e c

theorem EtaleChart.ofIso_coordIdeal {k : Type u} [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) {U : Y.Opens} {m : ℕ}
    (c : EtaleChart q U m) (S : Finset (Fin m)) :
    (EtaleChart.ofIso q e c).coordIdeal S =
      (c.coordIdeal S).comap (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl) := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  show (coordSubspaceIdeal k m S).comap
      (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl ≫ c.map) = _
  rw [Scheme.IdealSheafData.comap_comp]

theorem hasStrictNormalCrossingsWith_comap_iso {k : Type u} [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) (Z : Y.IdealSheafData)
    (F : List Y.IdealSheafData) (h : HasStrictNormalCrossingsWith q Z F) :
    HasStrictNormalCrossingsWith (e.hom ≫ q) (Z.comap e.hom) (F.map (fun D => D.comap e.hom)) := by
  unfold HasStrictNormalCrossingsWith at h ⊢
  intro x hx
  have hx1 : x ∈ orderAtLeastLocus (Z.comap e.hom) 1 := (mem_orderAtLeastLocus_one_iff _ _).2 hx
  rw [orderAtLeastLocus_comap_iso_hom_eq_preimage e Z 1] at hx1
  have hx' : e.hom.base x ∈ Z.support := (mem_orderAtLeastLocus_one_iff _ _).1 hx1
  obtain ⟨U, hU, m, c, a, S, h1, h2, h3, h4⟩ := h (e.hom.base x) hx'
  refine ⟨(Opens.map e.hom.base).obj U, hU, m, EtaleChart.ofIso q e c, a, S, ?_, ?_, ?_, ?_⟩
  · simpa using h1
  · intro i hi hai
    have hi' : i < F.length := by simpa using hi
    have hmap : (List.map (fun D => D.comap e.hom) F)[i] = (F[i]'hi').comap e.hom := by
      simp
    rw [hmap, restrictIdeal_comap, h2 i hi' hai]
    exact Scheme.IdealSheafData.comap_top _
  · intro i hi t hai
    have hi' : i < F.length := by simpa using hi
    have hmap : (List.map (fun D => D.comap e.hom) F)[i] = (F[i]'hi').comap e.hom := by
      simp
    rw [hmap, restrictIdeal_comap, h3 i hi' t hai, EtaleChart.ofIso_coordIdeal]
  · rw [restrictIdeal_comap, h4, EtaleChart.ofIso_coordIdeal]

theorem comapIsoInvariance : ComapIsoInvariance.{u} where
  coSupport_comap := fun e J n => orderAtLeastLocus_comap_iso_hom_eq_preimage e J n
  hasSNCWith_comap := fun q e Z F h => hasStrictNormalCrossingsWith_comap_iso q e Z F h
  smooth_comap := fun q e Z h => smooth_comap_iso q e Z h
  strictTransform_comap := fun π e Z D => strictTransform_comp_iso_hom π e Z D

end FunctorialResolution.EmbeddedResolution

end

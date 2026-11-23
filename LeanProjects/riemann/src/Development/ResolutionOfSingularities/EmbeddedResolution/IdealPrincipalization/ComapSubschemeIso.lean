import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.InvarianceUnderIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace PrincipalizationIsoTransport

abbrev preimageOpens {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens) : X.Opens :=
  (Opens.map e.hom.base).obj U

private theorem ker_subschemeι_le_ker_comap_subschemeι_comp_hom {X Y : Scheme.{u}} (f : X ≅ Y) (I : Y.IdealSheafData) :
    Scheme.Hom.ker I.subschemeι
      ≤ Scheme.Hom.ker ((I.comap f.hom).subschemeι ≫ f.hom) := by
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.ker_subschemeι]
  exact Scheme.IdealSheafData.le_map_comap I f.hom

private theorem ker_comap_subschemeι_le_ker_subschemeι_comp_inv {X Y : Scheme.{u}} (f : X ≅ Y) (I : Y.IdealSheafData) :
    Scheme.Hom.ker (I.comap f.hom).subschemeι
      ≤ Scheme.Hom.ker (I.subschemeι ≫ f.inv) := by
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.ker_subschemeι]
  have h : (I.comap f.hom).comap f.inv = I := by
    rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  have h2 := Scheme.IdealSheafData.le_map_comap (I.comap f.hom) f.inv
  rw [h] at h2
  exact h2

private theorem exists_iso_subscheme_comap_comm {X Y : Scheme.{u}} (f : X ≅ Y) (I : Y.IdealSheafData) :
    ∃ g : (I.comap f.hom).subscheme ≅ I.subscheme,
      g.hom ≫ I.subschemeι = (I.comap f.hom).subschemeι ≫ f.hom := by
  have hc := IsClosedImmersion.lift_fac I.subschemeι
    ((I.comap f.hom).subschemeι ≫ f.hom) (ker_subschemeι_le_ker_comap_subschemeι_comp_hom f I)
  have hd := IsClosedImmersion.lift_fac (I.comap f.hom).subschemeι
    (I.subschemeι ≫ f.inv) (ker_comap_subschemeι_le_ker_subschemeι_comp_inv f I)
  set c := IsClosedImmersion.lift I.subschemeι ((I.comap f.hom).subschemeι ≫ f.hom)
    (ker_subschemeι_le_ker_comap_subschemeι_comp_hom f I)
  set d := IsClosedImmersion.lift (I.comap f.hom).subschemeι (I.subschemeι ≫ f.inv)
    (ker_comap_subschemeι_le_ker_subschemeι_comp_inv f I)
  refine ⟨⟨c, d, ?_, ?_⟩, hc⟩
  · rw [← cancel_mono (I.comap f.hom).subschemeι, Category.assoc, hd, ← Category.assoc, hc,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [← cancel_mono I.subschemeι, Category.assoc, hc, ← Category.assoc, hd,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

def comapSubschemeIso {X Y : Scheme.{u}} (f : X ≅ Y) (I : Y.IdealSheafData) :
    (I.comap f.hom).subscheme ≅ I.subscheme :=
  (exists_iso_subscheme_comap_comm f I).choose

@[reassoc]
theorem comapSubschemeIso_hom_comp {X Y : Scheme.{u}} (f : X ≅ Y) (I : Y.IdealSheafData) :
    (comapSubschemeIso f I).hom ≫ I.subschemeι = (I.comap f.hom).subschemeι ≫ f.hom :=
  (exists_iso_subscheme_comap_comm f I).choose_spec

@[reassoc]
theorem preimageOpens_ι_comp_hom {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens) :
    (preimageOpens e U).ι ≫ e.hom = (preimageOpensIso e U).hom ≫ U.ι := by
  rw [preimageOpensIso_hom, Scheme.Hom.resLE_comp_ι]

@[reassoc]
theorem subschemeι_comp_preimageOpens_ι_comp_hom {W W' : Scheme.{u}} (e : W' ≅ W) (U : W.Opens)
    (H : U.toScheme.IdealSheafData) :
    (H.comap (preimageOpensIso e U).hom).subschemeι ≫ (preimageOpens e U).ι ≫ e.hom
      = (comapSubschemeIso (preimageOpensIso e U) H).hom ≫ H.subschemeι ≫ U.ι := by
  rw [preimageOpens_ι_comp_hom, ← Category.assoc, ← comapSubschemeIso_hom_comp, Category.assoc]

private theorem coe_support_comap_iso {X Y : Scheme.{u}} (g : X ≅ Y) (J : Y.IdealSheafData) :
    ((J.comap g.hom).support : Set ↥X) = ⇑g.hom.base ⁻¹' (J.support : Set ↥Y) := by
  have h := orderAtLeastLocus_comap_iso_hom_eq_preimage g J 1
  rw [orderAtLeastLocus_one, orderAtLeastLocus_one] at h
  exact h

private theorem support_comap_iso_subset_of_subset {X Y : Scheme.{u}} (g : X ≅ Y)
    {A B : Y.IdealSheafData} (h : (A.support : Set ↥Y) ⊆ (B.support : Set ↥Y)) :
    ((A.comap g.hom).support : Set ↥X) ⊆ ((B.comap g.hom).support : Set ↥X) := by
  rw [coe_support_comap_iso, coe_support_comap_iso]
  exact Set.preimage_mono h

private theorem preimage_base_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (S : Set ↥Z) :
    ⇑(f ≫ g).base ⁻¹' S = ⇑f.base ⁻¹' (⇑g.base ⁻¹' S) := by
  ext x
  simp

private theorem image_mem_irreducibleComponents_of_homeomorph {α β : Type u} [TopologicalSpace α]
    [TopologicalSpace β] (h : α ≃ₜ β) {T : Set α} (hT : T ∈ irreducibleComponents α) :
    ⇑h '' T ∈ irreducibleComponents β := by
  have himg : IsIrreducible (⇑h '' T) := hT.1.image _ h.continuous.continuousOn
  refine ⟨himg, ?_⟩
  intro S hS hsub
  have h2 : ⇑h.symm '' S = ⇑h ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hy
      exact ⟨h y, hy, by simp⟩
  have hpre : IsIrreducible (⇑h ⁻¹' S) := by
    rw [← h2]
    exact hS.image _ h.symm.continuous.continuousOn
  have hTsub : T ⊆ ⇑h ⁻¹' S := fun y hy => hsub ⟨y, hy, rfl⟩
  have h3 : ⇑h ⁻¹' S ⊆ T := hT.2 hpre hTsub
  intro y hy
  refine ⟨h.symm y, h3 ?_, by simp⟩
  simpa using hy

private theorem comap_preimageOpens_ι_comap_iso {X Y : Scheme.{u}} (e : X ≅ Y) (V : Y.Opens)
    (A : Y.IdealSheafData) :
    (A.comap e.hom).comap (preimageOpens e V).ι = (A.comap V.ι).comap (preimageOpensIso e V).hom := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, preimageOpens_ι_comp_hom]

private theorem comap_subschemeι_comap_iso {X Y : Scheme.{u}} (r : X ≅ Y) (B : Y.IdealSheafData)
    (A : Y.IdealSheafData) :
    (A.comap r.hom).comap (B.comap r.hom).subschemeι
      = (A.comap B.subschemeι).comap (comapSubschemeIso r B).hom := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    comapSubschemeIso_hom_comp]

private theorem support_comap_preimageOpens_subset {X Y : Scheme.{u}} (e : X ≅ Y) (V : Y.Opens)
    (A : Y.IdealSheafData) (B : V.toScheme.IdealSheafData)
    (h : ((A.comap V.ι).support : Set ↥V.toScheme) ⊆ (B.support : Set ↥V.toScheme)) :
    (((A.comap e.hom).comap (preimageOpens e V).ι).support :
        Set ↥(preimageOpens e V).toScheme)
      ⊆ ((B.comap (preimageOpensIso e V).hom).support : Set ↥(preimageOpens e V).toScheme) := by
  rw [comap_preimageOpens_ι_comap_iso]
  exact support_comap_iso_subset_of_subset (preimageOpensIso e V) h

private theorem isOpen_preimage_support_comap_preimageOpensIso {X Y : Scheme.{u}} (e : X ≅ Y) (V : Y.Opens)
    (A : Y.IdealSheafData) (B : V.toScheme.IdealSheafData)
    (h : IsOpen (⇑B.subschemeι.base ⁻¹' ((A.comap V.ι).support : Set ↥V.toScheme))) :
    IsOpen (⇑(B.comap (preimageOpensIso e V).hom).subschemeι.base ⁻¹'
      (((A.comap e.hom).comap (preimageOpens e V).ι).support :
        Set ↥(preimageOpens e V).toScheme)) := by
  rw [comap_preimageOpens_ι_comap_iso, coe_support_comap_iso (preimageOpensIso e V) (A.comap V.ι), ← _root_.FunctorialResolution.EmbeddedResolution.PrincipalizationIsoTransport.preimage_base_comp,
    ← comapSubschemeIso_hom_comp, _root_.FunctorialResolution.EmbeddedResolution.PrincipalizationIsoTransport.preimage_base_comp]
  exact h.preimage (comapSubschemeIso (preimageOpensIso e V) B).hom.continuous

private theorem preimage_comap_subschemeι_preimageOpens_comp {X Y : Scheme.{u}} (e : X ≅ Y) (V : Y.Opens)
    (B : V.toScheme.IdealSheafData) (Mem : Set ↥Y) :
    ⇑((B.comap (preimageOpensIso e V).hom).subschemeι ≫ (preimageOpens e V).ι).base ⁻¹'
        (⇑e.hom.base ⁻¹' Mem)
      = ⇑(comapSubschemeIso (preimageOpensIso e V) B).hom.base ⁻¹'
        (⇑(B.subschemeι ≫ V.ι).base ⁻¹' Mem) := by
  rw [← _root_.FunctorialResolution.EmbeddedResolution.PrincipalizationIsoTransport.preimage_base_comp, ← _root_.FunctorialResolution.EmbeddedResolution.PrincipalizationIsoTransport.preimage_base_comp, Category.assoc, subschemeι_comp_preimageOpens_ι_comp_hom]

private theorem eq_none_of_map_comap_eq_none {X Y : Scheme.{u}} (g : X ≅ Y)
    {o : Option Y.IdealSheafData} (h : o.map (fun J => J.comap g.hom) = Option.none) :
    o = Option.none := by
  cases o with
  | none => rfl
  | some a => simp at h

private theorem exists_eq_some_of_map_comap_eq_some {X Y : Scheme.{u}} (g : X ≅ Y)
    {o : Option Y.IdealSheafData} {b : X.IdealSheafData}
    (h : o.map (fun J => J.comap g.hom) = Option.some b) :
    ∃ a, o = Option.some a ∧ a.comap g.hom = b := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, rfl, by simpa using h⟩

private theorem exists_isOpen_comap_eq_comap_preimageOpensIso {W W' : Scheme.{u}} (e : W' ≅ W) (N : W.IdealSheafData)
    (Mem : Set ↥W) (V : W.Opens) (B : V.toScheme.IdealSheafData)
    (Jz : B.subscheme.IdealSheafData)
    (h : ∀ x : ↥B.subscheme, (B.subschemeι ≫ V.ι).base x ∉ Mem →
      ∃ O : B.subscheme.Opens, x ∈ O ∧
        Jz.comap O.ι = ((N.comap V.ι).comap B.subschemeι).comap O.ι)
    (x : ↥(B.comap (preimageOpensIso e V).hom).subscheme)
    (hx : ((B.comap (preimageOpensIso e V).hom).subschemeι ≫ (preimageOpens e V).ι).base x
      ∉ ⇑e.hom.base ⁻¹' Mem) :
    ∃ O : (B.comap (preimageOpensIso e V).hom).subscheme.Opens, x ∈ O ∧
      (Jz.comap (comapSubschemeIso (preimageOpensIso e V) B).hom).comap O.ι =
        (((N.comap e.hom).comap (preimageOpens e V).ι).comap
          (B.comap (preimageOpensIso e V).hom).subschemeι).comap O.ι := by
  have hx' : (B.subschemeι ≫ V.ι).base
      ((comapSubschemeIso (preimageOpensIso e V) B).hom.base x) ∉ Mem := by
    intro hmem
    apply hx
    have hmem2 : x ∈ ⇑(comapSubschemeIso (preimageOpensIso e V) B).hom.base ⁻¹'
        (⇑(B.subschemeι ≫ V.ι).base ⁻¹' Mem) := hmem
    rw [← preimage_comap_subschemeι_preimageOpens_comp e V B Mem] at hmem2
    exact hmem2
  obtain ⟨O, hxO, hO⟩ := h ((comapSubschemeIso (preimageOpensIso e V) B).hom.base x) hx'
  refine ⟨preimageOpens (comapSubschemeIso (preimageOpensIso e V) B) O, hxO, ?_⟩
  rw [comap_preimageOpens_ι_comap_iso, comap_preimageOpens_ι_comap_iso, comap_subschemeι_comap_iso, comap_preimageOpens_ι_comap_iso, hO]

private theorem principalizationCertificate_comap_preimageOpensIso {k : Type u} [Field k] {W W' : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of k)) (e : W' ≅ W) (Z : W.IdealSheafData) (μ : ℕ)
    (Mem : Set ↥W) (V : W.Opens) (B : V.toScheme.IdealSheafData)
    (Jz : B.subscheme.IdealSheafData)
    (h : ∀ (T : Scheme.{u}) (f : T ≅ B.subscheme),
      PrincipalizationCertificate T (f.hom ≫ B.subschemeι ≫ V.ι ≫ p) (Jz.comap f.hom) μ
        (⇑f.hom.base ⁻¹' (⇑(B.subschemeι ≫ V.ι).base ⁻¹' Mem))
        (((Z.comap V.ι).comap B.subschemeι).comap f.hom)) :
    PrincipalizationCertificate (B.comap (preimageOpensIso e V).hom).subscheme
      ((B.comap (preimageOpensIso e V).hom).subschemeι ≫ (preimageOpens e V).ι ≫ e.hom ≫ p)
      (Jz.comap (comapSubschemeIso (preimageOpensIso e V) B).hom) μ
      (⇑((B.comap (preimageOpensIso e V).hom).subschemeι ≫ (preimageOpens e V).ι).base ⁻¹'
        (⇑e.hom.base ⁻¹' Mem))
      (((Z.comap e.hom).comap (preimageOpens e V).ι).comap
        (B.comap (preimageOpensIso e V).hom).subschemeι) := by
  have ht := h (B.comap (preimageOpensIso e V).hom).subscheme (comapSubschemeIso (preimageOpensIso e V) B)
  rw [← subschemeι_comp_preimageOpens_ι_comp_hom_assoc, ← preimage_comap_subschemeι_preimageOpens_comp, ← comap_subschemeι_comap_iso,
    ← comap_preimageOpens_ι_comap_iso] at ht
  exact ht

theorem isSmoothDivisor_comap_iso {k : Type u} [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) (D : Y.IdealSheafData)
    (h : IsSmoothDivisor q D) : IsSmoothDivisor (e.hom ≫ q) (D.comap e.hom) := by
  rw [isSmoothDivisor_iff] at h ⊢
  exact ⟨h.1.comap_iso e, smooth_comap_iso q e D h.2⟩

theorem isSmoothDivisor_comap_preimageOpensIso {k : Type u} [Field k] {W W' : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of k)) (e : W' ≅ W) (U : W.Opens)
    (H : U.toScheme.IdealSheafData) (h : IsSmoothDivisor (U.ι ≫ p) H) :
    IsSmoothDivisor ((preimageOpens e U).ι ≫ e.hom ≫ p) (H.comap (preimageOpensIso e U).hom) := by
  have h' := isSmoothDivisor_comap_iso (U.ι ≫ p) (preimageOpensIso e U) H h
  rwa [← Category.assoc, ← preimageOpens_ι_comp_hom, Category.assoc] at h'

theorem nonzeroOnComponents_comap_iso {X Y : Scheme.{u}} (f : X ≅ Y) (I : Y.IdealSheafData)
    (h : NonzeroOnComponents I) : NonzeroOnComponents (I.comap f.hom) := by
  rw [nonzeroOnComponents_iff] at h ⊢
  intro T hT hsub
  refine h (⇑f.hom.base '' T) ?_ ?_
  · exact image_mem_irreducibleComponents_of_homeomorph (Scheme.homeoOfIso f) hT
  · rintro y ⟨x, hx, rfl⟩
    have hx' : x ∈ ((I.comap f.hom).support : Set ↥X) := hsub hx
    rw [coe_support_comap_iso f I] at hx'
    exact hx'

end PrincipalizationIsoTransport

theorem isoInvariantOrderCertificateDescend : OrderCertificateIsoInvariantOfMaxContact.{u} := by
  intro k inst W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert hJtrans W' e
  have hsupp : ∀ z' : ↥W', z' ∈ (Z.comap e.hom).support → e.hom.base z' ∈ Z.support := by
    intro z' hz'
    have h1 : z' ∈ ((Z.comap e.hom).support : Set ↥W') := hz'
    rw [PrincipalizationIsoTransport.coe_support_comap_iso e Z] at h1
    exact h1
  refine OrderCertificate.descend
    (fun z' hz' => PrincipalizationIsoTransport.preimageOpens e (U (e.hom.base z') (hsupp z' hz')))
    (fun z' hz' => hU (e.hom.base z') (hsupp z' hz'))
    (fun z' hz' => (H (e.hom.base z') (hsupp z' hz')).comap
      (preimageOpensIso e (U (e.hom.base z') (hsupp z' hz'))).hom)
    (fun z' hz' => PrincipalizationIsoTransport.isSmoothDivisor_comap_preimageOpensIso p e
      (U (e.hom.base z') (hsupp z' hz')) (H (e.hom.base z') (hsupp z' hz'))
      (hH (e.hom.base z') (hsupp z' hz')))
    (fun z' hz' => PrincipalizationIsoTransport.support_comap_preimageOpens_subset e
      (U (e.hom.base z') (hsupp z' hz')) N (H (e.hom.base z') (hsupp z' hz'))
      (hNsubH (e.hom.base z') (hsupp z' hz')))
    (fun z' hz' => PrincipalizationIsoTransport.support_comap_preimageOpens_subset e
      (U (e.hom.base z') (hsupp z' hz')) Z (H (e.hom.base z') (hsupp z' hz'))
      (hZH (e.hom.base z') (hsupp z' hz')))
    (fun z' hz' => (J (e.hom.base z') (hsupp z' hz')).map
      (fun Jz => Jz.comap (PrincipalizationIsoTransport.comapSubschemeIso
        (preimageOpensIso e (U (e.hom.base z') (hsupp z' hz')))
        (H (e.hom.base z') (hsupp z' hz'))).hom))
    ?_ ?_ ?_ ?_
  · intro z' hz' hnone
    refine PrincipalizationIsoTransport.isOpen_preimage_support_comap_preimageOpensIso e (U (e.hom.base z') (hsupp z' hz')) Z
      (H (e.hom.base z') (hsupp z' hz'))
      (hJnone (e.hom.base z') (hsupp z' hz') ?_)
    exact PrincipalizationIsoTransport.eq_none_of_map_comap_eq_none _ hnone
  · intro z' hz' Jz' heq
    obtain ⟨Jz, hJz, rfl⟩ := PrincipalizationIsoTransport.exists_eq_some_of_map_comap_eq_some _ heq
    exact PrincipalizationIsoTransport.nonzeroOnComponents_comap_iso _ Jz
      (hJcomp (e.hom.base z') (hsupp z' hz') Jz hJz)
  · intro z' hz' Jz' heq x hx
    obtain ⟨Jz, hJz, rfl⟩ := PrincipalizationIsoTransport.exists_eq_some_of_map_comap_eq_some _ heq
    exact PrincipalizationIsoTransport.exists_isOpen_comap_eq_comap_preimageOpensIso e N Mem (U (e.hom.base z') (hsupp z' hz'))
      (H (e.hom.base z') (hsupp z' hz')) Jz
      (hJloc (e.hom.base z') (hsupp z' hz') Jz hJz) x hx
  · intro z' hz' Jz' heq
    obtain ⟨Jz, hJz, rfl⟩ := PrincipalizationIsoTransport.exists_eq_some_of_map_comap_eq_some _ heq
    exact PrincipalizationIsoTransport.principalizationCertificate_comap_preimageOpensIso p e Z μ Mem (U (e.hom.base z') (hsupp z' hz'))
      (H (e.hom.base z') (hsupp z' hz')) Jz
      (hJtrans (e.hom.base z') (hsupp z' hz') Jz hJz)

theorem OrderCertificate.comap_iso_hom_comp {k : Type u} [Field k] {W W' : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (e : W' ≅ W) (h : OrderCertificate W p N μ Mem Z) :
    OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  OrderCertificate.comap_iso isoInvariantOrderCertificateDescend e h

theorem PrincipalizationCertificate.comap_iso_of_eq_iso_hom_comp {k : Type u} [Field k] {W W' : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {p' : W' ⟶ Spec (CommRingCat.of k)}
    {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
    (e : W' ≅ W) (hp : p' = e.hom ≫ p) (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W' p' (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  PrincipalizationCertificate.comap_iso_of_eq isoInvariantOrderCertificateDescend e hp h

theorem OrderCertificate.comap_iso_of_eq_iso_hom_comp {k : Type u} [Field k] {W W' : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {p' : W' ⟶ Spec (CommRingCat.of k)}
    {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
    (e : W' ≅ W) (hp : p' = e.hom ≫ p) (h : OrderCertificate W p N μ Mem Z) :
    OrderCertificate W' p' (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  OrderCertificate.comap_iso_of_eq isoInvariantOrderCertificateDescend e hp h

end FunctorialResolution.EmbeddedResolution

end

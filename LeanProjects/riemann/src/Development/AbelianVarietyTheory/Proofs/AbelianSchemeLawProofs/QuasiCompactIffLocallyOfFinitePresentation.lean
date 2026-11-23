import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.SemiAbelianSchemes
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G

namespace GlobalTheory.SemiAbelianCompare

section General

theorem isPullback_torsor {S : Scheme.{u}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]
    (i : T ⟶ G) (q : G ⟶ B) [IsMonHom q] (h : IsPullback i (toUnit _) q η[B]) :
    IsPullback ((fst T G ≫ i) * snd T G) (snd T G) q q := by
  have hi : i ≫ q = 1 := h.w
  have : Mono i := h.flip.mono_snd_of_mono
  refine IsPullback.of_isLimit'
    ⟨by rw [MonObj.mul_comp, Category.assoc, hi, MonObj.comp_one, _root_.one_mul]⟩
    (PullbackCone.IsLimit.mk _ (fun s => lift (h.lift (s.fst * s.snd⁻¹) (toUnit _) (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, s.condition, mul_inv_cancel]; rfl)) s.snd)
      (fun s => ?_) (fun s => lift_snd _ _) (fun s m h₁ h₂ => ?_))
  · rw [MonObj.comp_mul, lift_fst_assoc, h.lift_fst, lift_snd, inv_mul_cancel_right]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, ← cancel_mono i, h.lift_fst, ← h₁, ← h₂, MonObj.comp_mul,
        mul_inv_cancel_right, Category.assoc]
    · rw [lift_snd, h₂]

theorem geometricallyConnected_of_isPullback {X Y X' Y' : Scheme.{u}}
    {a : X' ⟶ X} {p : X' ⟶ Y'} {q : X ⟶ Y} {s : Y' ⟶ Y} (h : IsPullback a p q s)
    [Surjective s] [GeometricallyConnected p] : GeometricallyConnected q := by
  refine ⟨fun k _ y Z fst snd hZ => ?_⟩
  obtain ⟨w⟩ : Nonempty ↥(pullback y s) := by
    obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstanceAs (Nonempty (PrimeSpectrum k))
    obtain ⟨w, -⟩ := (pullback.fst y s).surjective pt
    exact ⟨w⟩
  let r := (pullback y s).fromSpecResidueField w
  let b := r ≫ pullback.fst y s
  let x := r ≫ pullback.snd y s
  have hbx : b ≫ y = x ≫ s := by simp only [b, x, Category.assoc, pullback.condition]
  have hb : Surjective b := ⟨fun z => ⟨_, Subsingleton.elim (b (default : PrimeSpectrum _)) z⟩⟩
  have big : IsPullback (pullback.fst snd b ≫ fst) (pullback.snd snd b) q (x ≫ s) :=
    hbx ▸ (IsPullback.of_hasPullback snd b).paste_horiz hZ
  have sq : IsPullback (h.lift (pullback.fst snd b ≫ fst) (pullback.snd snd b ≫ x)
      (big.w.trans (Category.assoc _ _ _).symm)) (pullback.snd snd b) p x :=
    IsPullback.of_right (by rw [h.lift_fst]; exact big) (h.lift_snd _ _ _) h
  have : ConnectedSpace ↥(pullback snd b) :=
    GeometricallyConnected.geometrically_connectedSpace (f := p) x _ _ sq
  exact (pullback.fst snd b).surjective.connectedSpace (pullback.fst snd b).continuous

theorem quasiCompact_of_isPullback {X Y X' Y' : Scheme.{u}}
    {a : X' ⟶ X} {p : X' ⟶ Y'} {q : X ⟶ Y} {s : Y' ⟶ Y} (h : IsPullback a p q s)
    [Surjective s] (hs : IsOpenMap s) [QuasiCompact p] : QuasiCompact q := by
  refine ⟨fun U hUo hUc => ?_⟩
  have key : ∃ C : Set X, IsCompact C ∧ C ⊆ q ⁻¹' U ∧ q ⁻¹' U ⊆ C := by
    refine hUc.induction_on (p := fun t => ∃ C : Set X, IsCompact C ∧ C ⊆ q ⁻¹' U ∧ q ⁻¹' t ⊆ C)
      ⟨∅, isCompact_empty, Set.empty_subset _, by simp⟩
      (fun t t' htt' ⟨C, h₁, h₂, h₃⟩ => ⟨C, h₁, h₂, (Set.preimage_mono htt').trans h₃⟩)
      (fun t t' ⟨C, h₁, h₂, h₃⟩ ⟨C', h₁', h₂', h₃'⟩ =>
        ⟨C ∪ C', h₁.union h₁', Set.union_subset h₂ h₂', by
          rw [Set.preimage_union]; exact Set.union_subset_union h₃ h₃'⟩) (fun y hy => ?_)
    obtain ⟨y', rfl⟩ := s.surjective y
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := Y'.isBasis_affineOpens.exists_subset_of_mem_open
      (a := y') (u := s ⁻¹' U) hy (hUo.preimage s.continuous)
    refine ⟨s '' V, mem_nhdsWithin_of_mem_nhds ((hs _ V.isOpen).mem_nhds ⟨y', hyV, rfl⟩),
      a '' (p ⁻¹' V), (QuasiCompact.isCompact_preimage _ V.isOpen hV.isCompact).image a.continuous,
      ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      have := hVU hz
      rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply] at this
    · rintro x ⟨v, hv, hx⟩
      obtain ⟨z, rfl, rfl⟩ := Scheme.exists_preimage_of_isPullback h x v hx.symm
      exact ⟨z, hv, rfl⟩
  obtain ⟨C, h₁, h₂, h₃⟩ := key
  rwa [← h₂.antisymm h₃]

theorem geometricallyConnected_of_isAlgClosed {X S : Scheme.{u}} (f : X ⟶ S)
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S),
      ConnectedSpace ↥(pullback f s)) : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y => ?_⟩
  let b : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  have hb : Surjective b := ⟨fun z => ⟨_, Subsingleton.elim (b (default : PrimeSpectrum _)) z⟩⟩
  have := h _ (b ≫ y)
  let g := (pullbackLeftPullbackSndIso f y b).inv ≫ pullback.fst (pullback.snd f y) b
  exact g.surjective.connectedSpace g.continuous

end General

section Exact

variable {S : Scheme.{u}} {X : Type u} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  {i : Semi.splitTorus S X ⟶ G} {q : G ⟶ B}

theorem quasiCompact_iff_locallyOfFinitePresentation [Module.Finite ℤ X] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q η[B]) [hf : Flat q.left] [hs : Surjective q.left] :
    QuasiCompact q.left ↔ LocallyOfFinitePresentation q.left := by
  have sq := (isPullback_torsor i q hk).map (Over.forget _)
  constructor
  · intro hq
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFinitePresentation)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq.flip ⟨⟨hs, hf⟩, hq⟩ ?_
    exact MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (IsPullback.of_hasPullback _ _) (Diag.locallyOfFinitePresentation_hom S X)
  · intro hq
    have h₁ : QuasiCompact ((Over.forget _).map (snd (Semi.splitTorus S X) G)) :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback _ _)
        (have := Diag.isAffineHom_hom S X; inferInstance)
    exact @quasiCompact_of_isPullback _ _ _ _ _ _ _ _ sq hs q.left.isOpenMap h₁

theorem geometricallyConnected_quotient [Module.Free ℤ X] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q η[B]) [hs : Surjective q.left] :
    GeometricallyConnected q.left := by
  have sq := (isPullback_torsor i q hk).map (Over.forget _)
  have : TwoUniqueSums X := by
    let b := Module.Free.chooseBasis ℤ X
    exact TwoUniqueSums.of_injective_addHom b.repr.toAddEquiv.toAddHom b.repr.injective inferInstance
  have h₁ : GeometricallyConnected ((Over.forget _).map (snd (Semi.splitTorus S X) G)) :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) (IsPullback.of_hasPullback _ _)
      (Diag.geometricallyConnected_hom S X)
  exact @geometricallyConnected_of_isPullback _ _ _ _ _ _ _ _ sq hs h₁

end Exact

theorem isAbelianScheme_iff {S : Scheme.{u}} (A : Over S) [GrpObj A] :
    Semi.IsAbelianScheme A ↔ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsAbelianScheme A :=
  ⟨fun h => ⟨h.smooth, h.proper, h.geomConnected, h.comm⟩,
    fun h => ⟨h.comm, h.smooth, h.proper, h.geometricallyConnected⟩⟩

section Field

variable {k : Type u} [Field k] {G : Over (Spec (CommRingCat.of k))} [GrpObj G]

theorem isShortExact_of_torusExtension (E : Semi.TorusExtension G) :
    letI := E.addCommGroup; letI := E.grpB
    IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsAbelianScheme E.B ∧ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsShortExact E.i E.q := by
  letI := E.addCommGroup; letI := E.grpB
  have := E.finite
  have := E.q_hom
  have := E.q_flat
  have := E.q_surjective
  exact ⟨(isAbelianScheme_iff _).1 E.isAbelian, E.i_hom, E.q_hom, E.isKernel, E.q_flat,
    E.q_surjective, (quasiCompact_iff_locallyOfFinitePresentation E.isKernel).1 E.q_quasiCompact⟩

def torusExtensionOfIsShortExact {X : Type u} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] {B : Over (Spec (CommRingCat.of k))} [GrpObj B]
    {i : Semi.splitTorus (Spec (CommRingCat.of k)) X ⟶ G} {q : G ⟶ B}
    (hB : IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsAbelianScheme B) (h : IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsShortExact i q) :
    Semi.TorusExtension G where
  X := X
  B := B
  isAbelian := (isAbelianScheme_iff _).2 hB
  q := q
  q_hom := h.isMonHom_q
  q_flat := h.flat
  q_surjective := h.surjective
  q_quasiCompact :=
    have := h.isMonHom_q
    have := h.flat
    have := h.surjective
    (quasiCompact_iff_locallyOfFinitePresentation h.isKernel).2 h.finitePresentation
  i := i
  i_hom := h.isMonHom_i
  isKernel := h.isKernel

variable (G) in

theorem isTorusExtension_iff :
    IsCommMonObj G ∧ Nonempty (Semi.TorusExtension G) ↔ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsTorusExtension G :=
  and_congr_right fun _ =>
    ⟨fun ⟨E⟩ => ⟨E.X, E.addCommGroup, E.free, E.finite, E.B, E.grpB, E.i, E.q,
      isShortExact_of_torusExtension E⟩,
    fun ⟨_, _, _, _, _, _, _, _, hB, h⟩ => ⟨torusExtensionOfIsShortExact hB h⟩⟩

theorem geometricallyConnected_of_torusExtension (E : Semi.TorusExtension G) :
    GeometricallyConnected G.hom := by
  letI := E.addCommGroup; letI := E.grpB
  have := E.free
  have := E.q_hom
  have := E.q_flat
  have := E.q_surjective
  have := (isShortExact_of_torusExtension E).2.finitePresentation
  have := E.isAbelian.smooth
  have := E.isAbelian.geomConnected
  have := geometricallyConnected_quotient E.isKernel
  rw [← Over.w E.q]
  exact GeometricallyConnected.comp _ _

end Field

theorem isCommMonObj_of_torusExtension {k : Type} [Field k] {G : Over (Spec (CommRingCat.of k))}
    [GrpObj G] (E : Semi.TorusExtension G) : IsCommMonObj G := by
  have h := SemiRigid.square_eq_one E E ((fst G G * snd G G) * (snd G G * fst G G)⁻¹)
    (by simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, _root_.mul_one,
      _root_.one_mul, mul_inv_cancel])
    (by simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, _root_.mul_one,
      _root_.one_mul, mul_inv_cancel])
  rw [mul_inv_eq_one, Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, lift_snd_fst] at h
  exact ⟨h.symm⟩

theorem nonempty_torusExtension_iff {k : Type} [Field k] (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] : Nonempty (Semi.TorusExtension G) ↔ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsTorusExtension G :=
  ⟨fun ⟨E⟩ => (isTorusExtension_iff G).1 ⟨isCommMonObj_of_torusExtension E, ⟨E⟩⟩,
    fun h => ((isTorusExtension_iff G).2 h).2⟩

theorem isSemiAbelian_iff {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    Semi.IsSemiAbelian G ↔ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsSemiAbelianScheme G := by
  constructor
  · intro h
    have := h.smooth
    have := h.comm
    exact ⟨h.smooth, h.separated, inferInstance, h.quasiCompact, h.comm,
      fun k _ _ s => (isTorusExtension_iff _).1 ⟨inferInstance, h.fibres k s⟩⟩
  · intro h
    have hf := fun (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S) =>
      ((isTorusExtension_iff _).2 (h.geometricFibre k s)).2
    refine ⟨h.comm, h.smooth, h.separated, h.quasiCompact,
      geometricallyConnected_of_isAlgClosed _ fun k _ _ s => ?_, hf⟩
    obtain ⟨E⟩ := hf k s
    have := geometricallyConnected_of_torusExtension E
    exact GeometricallyConnected.connectedSpace_of_subsingleton ((Over.pullback s).obj G).hom

end GlobalTheory.SemiAbelianCompare

namespace GlobalTheory

open SemiAbelianCompare

theorem semiAbelian_notions_equiv :
    (∀ (S : Scheme.{u}) (A : Over S) [GrpObj A],
      Semi.IsAbelianScheme A ↔ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsAbelianScheme A) ∧
    (∀ (k : Type u) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
      (X : Type u) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
      (B : Over (Spec (CommRingCat.of k))) [GrpObj B]
      (i : Semi.splitTorus (Spec (CommRingCat.of k)) X ⟶ G) (q : G ⟶ B),
      (Semi.IsAbelianScheme B ∧ IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧
          QuasiCompact q.left ∧ IsMonHom i ∧ IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) ↔
        (IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsAbelianScheme B ∧ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsShortExact i q)) ∧
    (∀ (k : Type u) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G],
      IsCommMonObj G ∧ Nonempty (Semi.TorusExtension G) ↔ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsTorusExtension G) ∧
    (∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G],
      Nonempty (Semi.TorusExtension G) ↔ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsTorusExtension G) ∧
    (∀ (S : Scheme.{u}) (G : Over S) [GrpObj G],
      Semi.IsSemiAbelian G ↔ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsSemiAbelianScheme G) := by
  refine ⟨fun _ A _ => isAbelianScheme_iff A, fun k _ G _ X _ _ _ B _ i q => ⟨?_, ?_⟩,
    fun _ _ G _ => isTorusExtension_iff G, fun _ _ G _ => nonempty_torusExtension_iff G,
    fun _ G _ => isSemiAbelian_iff G⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
    exact isShortExact_of_torusExtension ⟨X, B, h₁, q, h₂, h₃, h₄, h₅, i, h₆, h₇⟩
  · rintro ⟨hB, h⟩
    let E := torusExtensionOfIsShortExact hB h
    exact ⟨E.isAbelian, E.q_hom, E.q_flat, E.q_surjective, E.q_quasiCompact, E.i_hom, E.isKernel⟩

end GlobalTheory

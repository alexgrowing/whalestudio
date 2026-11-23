import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOfIsClosedRange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfIsPullbackIsDominant
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteMulByNatAbelianVarietyAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuasiCompactIffLocallyOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsClosedImageOfIsClosedSubgroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.AbelianLimit

open RationalPoint in

theorem connectedSpace_of_surjective_pow {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (h : ∀ n : ℕ, 1 ≤ n → Surjective ((𝟙 G) ^ n : G ⟶ G).left) : ConnectedSpace G.left := by
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : IsNoetherian G.left := {}
  have key (f : G ⟶ G) {x y : 𝟙_ (Over (Sp k)) ⟶ G} (hx : pt x ∈ connectedComponent (pt y)) :
      pt (x ≫ f) ∈ connectedComponent (pt (y ≫ f)) :=
    f.left.continuous.image_connectedComponent_subset (pt y) ⟨_, hx, rfl⟩
  have tr (x z : 𝟙_ (Over (Sp k)) ⟶ G) : x ≫ (𝟙 G * (toUnit G ≫ z)) = x * z := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit G) (𝟙 _), Category.id_comp]
  have key' (z : 𝟙_ (Over (Sp k)) ⟶ G) {x y : 𝟙_ (Over (Sp k)) ⟶ G} (hx : pt x ∈ connectedComponent (pt y)) :
      pt (x * z) ∈ connectedComponent (pt (y * z)) := by
    simpa only [tr] using key (𝟙 G * (toUnit G ≫ z)) hx
  let H : Subgroup (𝟙_ (Over (Sp k)) ⟶ G) :=
    { carrier := {x | pt x ∈ connectedComponent (pt (1 : 𝟙_ (Over (Sp k)) ⟶ G))}
      one_mem' := mem_connectedComponent
      mul_mem' := fun {x y} hx hy => by
        have := key' y hx
        rw [_root_.one_mul, ← connectedComponent_eq hy] at this
        exact this
      inv_mem' := fun {x} hx => by
        have := key (𝟙 G)⁻¹ hx
        rwa [GrpObj.comp_inv, GrpObj.comp_inv, Category.comp_id, Category.comp_id, inv_one] at this }
  have : H.Normal := ⟨fun x hx g => by rwa [_root_.mul_comm g x, mul_inv_cancel_right]⟩
  have : DiscreteTopology (_root_.ConnectedComponents G.left) :=
    ConnectedComponents.discreteTopology_iff.2 isOpen_connectedComponent_of_noetherianSpace
  have : Finite (_root_.ConnectedComponents G.left) := finite_of_compact_of_discrete
  have : Finite ((𝟙_ (Over (Sp k)) ⟶ G) ⧸ H) := by
    refine Finite.of_injective (fun q => ConnectedComponents.mk (pt q.out)) fun q q' e => ?_
    rw [← q.out_eq, ← q'.out_eq]
    refine QuotientGroup.eq.2 ?_
    have := key' q.out⁻¹ (ConnectedComponents.coe_eq_coe'.1 e.symm)
    rwa [mul_inv_cancel, _root_.mul_comm] at this
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have all (x : 𝟙_ (Over (Sp k)) ⟶ G) : x ∈ H := by
    have := h H.index (Nat.one_le_iff_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero)
    obtain ⟨z, hz⟩ := ((𝟙 G) ^ H.index : G ⟶ G).left.surjective (pt x)
    obtain ⟨y, -, rfl⟩ := (pt_mem_image_iff ((𝟙 G) ^ H.index) isClosed_univ x).1 ⟨z, trivial, hz⟩
    rw [MonObj.comp_pow, Category.comp_id]
    exact H.pow_index_mem y
  have hu : connectedComponent (pt (1 : 𝟙_ (Over (Sp k)) ⟶ G)) = Set.univ := by
    by_contra hne
    obtain ⟨x, hx⟩ := exists_pt_mem (isOpen_connectedComponent_of_noetherianSpace _).isClosed_compl
      (Set.nonempty_compl.2 hne)
    exact hx (all x)
  exact connectedSpace_iff_connectedComponent.2 ⟨_, hu⟩

theorem pow_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    ((𝟙 G') ^ n : G' ⟶ G').left ≫ φ = φ ≫ ((𝟙 G) ^ n : G ⟶ G).left := by
  have e := congrArg (fun q => q.left) (map_pow (pushHom h G') (𝟙 G') n)
  have e' (x : Over.mk (G'.hom ≫ f) ⟶ G) : x ^ n = x ≫ (𝟙 G) ^ n := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [e'] at e
  refine Eq.trans e ?_
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem isPullback_pow {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    IsPullback φ ((𝟙 G') ^ n : G' ⟶ G').left ((𝟙 G) ^ n : G ⟶ G).left φ := by
  refine IsPullback.of_bot ?_ (pow_comm h n).symm h.1
  rw [Over.w, Over.w]
  exact h.1

theorem surjective_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (n : ℕ) (hn : 1 ≤ n) :
    Surjective ((𝟙 A) ^ n : A ⟶ A).left := by
  refine ⟨fun x => ?_⟩
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  let K := AlgebraicClosure (S.residueField (A.hom x))
  let t : Sp K ⟶ S := spMap (algebraMap (S.residueField (A.hom x)) K) ≫ S.fromSpecResidueField (A.hom x)
  have ht : A.hom x = t (IsLocalRing.closedPoint K) := by
    exact (Scheme.fromSpecResidueField_apply _ _).symm
  let B := (Over.pullback t).obj A
  have hB : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := inferInstanceAs (Smooth (pullback.snd A.hom t))
      proper := inferInstanceAs (IsProper (pullback.snd A.hom t))
      geomConnected := inferInstanceAs (GeometricallyConnected (pullback.snd A.hom t)) }
  have hm : IsMonHom ((𝟙 B) ^ n : B ⟶ B) := by
    have := hB.comm
    clear hn
    induction n with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit B ≫ η[B]))
    | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 B) ^ n) (𝟙 B) ≫ μ[B]))
  have hs := (flat_and_surjective_of_isFinite_abelianEnd
    (fun _ _ f _ _ => (geometricallyIntegral_of_smooth_of_geometricallyConnected.1 f).1) K B hB ((𝟙 B) ^ n)
    hm (MulFiniteAny.isFinite_mulA K B hB n hn)).2
  obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback (.of_hasPullback A.hom t) x _ ht
  obtain ⟨z, rfl⟩ := ((𝟙 B) ^ n : B ⟶ B).left.surjective y
  exact ⟨pullback.fst A.hom t z, (congrArg (fun g => g z) (pow_comm (isGrpPullback_pullback A t) n)).symm.trans hy⟩

theorem isAbelianScheme_of_isDominant {S S' : Scheme.{0}} {B : Over S} {A : Over S'} [GrpObj B] [GrpObj A]
    [IsCommMonObj B] [Smooth B.hom] [IsProper B.hom] {f : S' ⟶ S} [IsDominant f] {φ : A.left ⟶ B.left}
    (h : IsGrpPullback A B f φ) (hA : IsAbelianScheme A) : IsAbelianScheme B := by
  have hd : DenseRange φ := by
    rw [DenseRange, ProperLimit.range_eq_of_isPullback h.1.flip]
    exact f.denseRange.preimage B.hom.isOpenMap
  have hs (n : ℕ) (hn : 1 ≤ n) : Surjective ((𝟙 B) ^ n : B ⟶ B).left := by
    have := surjective_pow A hA n hn
    have : IsProper (((𝟙 B) ^ n : B ⟶ B).left ≫ B.hom) := by rw [Over.w]; infer_instance
    have : IsProper ((𝟙 B) ^ n : B ⟶ B).left := IsProper.of_comp _ B.hom
    refine ⟨Set.range_eq_univ.1 ?_⟩
    rw [← ((𝟙 B) ^ n : B ⟶ B).left.isClosedMap.isClosed_range.closure_eq]
    refine (Dense.mono ?_ hd).closure_eq
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := ((𝟙 A) ^ n : A ⟶ A).left.surjective y
    exact ⟨φ z, (congrArg (fun g => g z) (pow_comm h n)).symm⟩
  refine ⟨‹_›, ‹_›, ‹_›, SemiAbelianCompare.geometricallyConnected_of_isAlgClosed _ fun k _ _ s => ?_⟩
  have : LocallyOfFiniteType ((Over.pullback s).obj B).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd B.hom s))
  have : QuasiCompact ((Over.pullback s).obj B).hom := inferInstanceAs (QuasiCompact (pullback.snd B.hom s))
  exact connectedSpace_of_surjective_pow ((Over.pullback s).obj B) fun n hn =>
    MorphismProperty.of_isPullback (isPullback_pow (isGrpPullback_pullback B s) n) (hs n hn)

theorem abelianScheme_descends_to_fg_subring :
    ∀ (R : Type) [CommRing R] (g : ℕ) (A : Over (Sp R)) [GrpObj A] (F : Finset R), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧
      IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  intro R _ g A _ F hA hg
  have := hA.comm
  have := hA.proper
  obtain ⟨k, A₀, _, _, φ₀, hF, hk, _, _, _, h₀⟩ :=
    smooth_grpScheme_descends_to_fg_subring R A F hA.smooth inferInstance inferInstance
  have : IsNoetherianRing k := Algebra.FiniteType.isNoetherianRing ℤ k
  have h₁ : IsPullback φ₀ A.hom A₀.hom (spMap (algebraMap k R)) := h₀.1
  have : UniversallyClosed (pullback.snd A₀.hom (spMap (algebraMap k R))) := by
    rw [← h₁.isoPullback_inv_snd]
    infer_instance
  obtain ⟨s, hs⟩ := ProperLimit.exists_finset_isProper k R A₀.hom
  let S : Subalgebra k R := Algebra.adjoin k (s : Set R)
  let t : Sp S.toSubring ⟶ Sp k := spMap (algebraMap k S)
  have e : spMap S.toSubring.subtype ≫ t = spMap k.subtype := Spread.spMap_algHom_comp S.val
  obtain ⟨φ, hφ⟩ := GoodVal.exists_isGrpPullback_of_comp A₀ t (spMap S.toSubring.subtype) (e ▸ h₀)
  have hsm : Smooth ((Over.pullback t).obj A₀).hom := inferInstanceAs (Smooth (pullback.snd A₀.hom t))
  have : IsProper ((Over.pullback t).obj A₀).hom := hs
  have hd : IsDominant (spMap S.toSubring.subtype) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical S.toSubring.subtype).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]
      exact bot_le)⟩
  exact ⟨S.toSubring, (Over.pullback t).obj A₀, inferInstance, φ, fun x hx => S.algebraMap_mem ⟨x, hF hx⟩,
    SpreadGroup.finiteType_of_fg hk (Subalgebra.fg_adjoin_finset s), isAbelianScheme_of_isDominant hφ hA,
    smoothOfRelativeDimension_of_isPullback_isDominant _ _ _ _ _ _ _ _ g hφ.1 hd hsm hg, hφ⟩

end GlobalTheory.AbelianLimit

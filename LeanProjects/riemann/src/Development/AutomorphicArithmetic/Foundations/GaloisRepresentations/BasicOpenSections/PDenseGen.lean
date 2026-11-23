import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.BaseFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

private theorem mem_basicOpen_fn {O : Type} [CommRing O] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of O)) (a : O) (y : Y) :
    y ∈ Y.basicOpen (fn g a) ↔ g y ∈ PrimeSpectrum.basicOpen a := by
  rw [fn, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  rfl

private theorem exists_min {S : Scheme.{0}} (x : S) : ∃ x' : S, x' ⤳ x ∧ ∀ t : S, t ⤳ x' → t = x' := by
  obtain ⟨Z, hZ, hxZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := x)).closure
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hZi : IsIrreducible Z := hZ.1
  set η := hZi.genericPoint with hη
  have hgen : closure {η} = Z := (hZi.isGenericPoint_genericPoint_closure).trans hZc.closure_eq
  refine ⟨η, ?_, ?_⟩
  · rw [specializes_iff_mem_closure, hgen]
    exact hxZ (subset_closure rfl)
  · intro t ht
    have h1 : Z ⊆ closure {t} := by
      rw [← hgen]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp ht))
        isClosed_closure
    have h2 : closure {t} = Z := subset_antisymm (hZ.2 isIrreducible_singleton.closure h1) h1
    have h3 : η ⤳ t := by
      rw [specializes_iff_mem_closure, hgen, ← h2]
      exact subset_closure rfl
    exact (ht.antisymm h3).eq

private theorem dense_generic_points {O A k : Type} [CommRing O] [Field A] [Field k] (q : O →+* A) (hq : Function.Surjective q)
    (β₀ : A →+* k) (ϖ : O) (hϖ : RingHom.ker q = Ideal.span {ϖ}) (Y S : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of O))
    (s : S ⟶ Y) (bS : S ⟶ gp k) (hpb : IsPullback s bS g (sp (β₀.comp q))) :
    Dense {x : S | crystallineComparison.GenPt (fn g ϖ) (s x)} := by
  classical
  have hcomp : Mod.sp (β₀.comp q) = Mod.sp β₀ ≫ Mod.sp q := by
    simp only [Mod.sp, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI : IsClosedImmersion (Mod.sp q) := IsClosedImmersion.spec_of_surjective _ hq
  haveI hτ : Flat (Mod.sp β₀) := Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField A) _)
  have hsq : s ≫ g = (bS ≫ Mod.sp β₀) ≫ Mod.sp q := by
    rw [Category.assoc, ← hcomp]
    exact hpb.w
  have hφi : pullback.lift s (bS ≫ Mod.sp β₀) hsq ≫ pullback.fst g (Mod.sp q) = s :=
    pullback.lift_fst _ _ _
  have hφπ : pullback.lift s (bS ≫ Mod.sp β₀) hsq ≫ pullback.snd g (Mod.sp q) = bS ≫ Mod.sp β₀ :=
    pullback.lift_snd _ _ _
  set φ := pullback.lift s (bS ≫ Mod.sp β₀) hsq with hφ
  have hφpb : IsPullback φ bS (pullback.snd g (Mod.sp q)) (Mod.sp β₀) := by
    refine IsPullback.of_right ?_ hφπ (IsPullback.of_hasPullback g (Mod.sp q))
    rw [hφi, ← hcomp]
    exact hpb
  haveI : Flat φ := MorphismProperty.of_isPullback hφpb.flip hτ
  have hgenφ : GeneralizingMap φ := Flat.generalizingMap φ
  have hind : Topology.IsInducing (pullback.fst g (Mod.sp q)) :=
    (pullback.fst g (Mod.sp q)).isClosedEmbedding.isInducing
  have memV : ∀ y : Y, y ∉ Y.basicOpen (fn g ϖ) ↔ ϖ ∈ (g y).asIdeal := by
    intro y
    rw [mem_basicOpen_fn]
    change ¬ (ϖ ∉ (g y).asIdeal) ↔ _
    exact not_not
  have hϖker : ϖ ∈ RingHom.ker q := by
    rw [hϖ]
    exact Ideal.mem_span_singleton_self ϖ
  have hV_of : ∀ p : ↥(pullback g (Mod.sp q)),
      pullback.fst g (Mod.sp q) p ∉ Y.basicOpen (fn g ϖ) := by
    intro p
    rw [memV]
    have h1 : g (pullback.fst g (Mod.sp q) p) = Mod.sp q (pullback.snd g (Mod.sp q) p) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rw [h1]
    show ϖ ∈ Ideal.comap q _
    rw [Ideal.mem_comap, RingHom.mem_ker.mp hϖker]
    exact Ideal.zero_mem _
  have hV_to : ∀ y : Y, y ∉ Y.basicOpen (fn g ϖ) → y ∈ Set.range (pullback.fst g (Mod.sp q)) := by
    intro y hy
    rw [memV] at hy
    rw [Scheme.Pullback.range_fst]
    show g y ∈ Set.range (PrimeSpectrum.comap q)
    rw [range_comap_of_surjective _ q hq, hϖ]
    exact (PrimeSpectrum.mem_zeroLocus (g y) _).mpr
      (SetLike.coe_subset_coe.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hy))
  rw [dense_iff_inter_open]
  rintro U hU ⟨x, hx⟩
  obtain ⟨x', hx'x, hmin⟩ := exists_min x
  refine ⟨x', hx'x.mem_open hU hx, ?_⟩
  have hsx : s x' = pullback.fst g (Mod.sp q) (φ x') := by
    rw [← Scheme.Hom.comp_apply, hφi]
  refine ⟨hsx ▸ hV_of _, ?_⟩
  intro y' hy' hspec
  obtain ⟨p', rfl⟩ := hV_to y' hy'
  rw [hsx] at hspec ⊢
  have hp : p' ⤳ φ x' := hind.specializes_iff.mp hspec
  obtain ⟨x'', hx'', hφx''⟩ := hgenφ hp
  rw [hmin x'' hx''] at hφx''
  rw [hφx'']

theorem UpperTheory.Gal.Mod.denseGen :
    DenseGen := by
  intro O _ _ _ ϖ hϖ k _ β hβ Y S g s bS hpb
  obtain ⟨A, _, q, hq, β₀, hker, hβeq⟩ : ∃ (A : Type) (_ : Field A) (q : O →+* A),
      Function.Surjective q ∧ ∃ β₀ : A →+* k, RingHom.ker q = Ideal.span {ϖ} ∧ β₀.comp q = β := by
    haveI hmax : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
    refine ⟨O ⧸ Ideal.span {ϖ}, Ideal.Quotient.field _, Ideal.Quotient.mk _,
      Ideal.Quotient.mk_surjective, Ideal.Quotient.lift _ β (fun a ha => by
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        simp [hβ]), Ideal.mk_ker, Ideal.Quotient.lift_comp_mk _ _ _⟩
  subst hβeq
  exact dense_generic_points q hq β₀ ϖ hker Y S g s bS hpb

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ChartQF

section Alg

variable {A R : Type} [CommRing A] [CommRing R] [IsLocalRing A] [IsLocalRing R] (f : A →+* R)

theorem isAlgebraic_of_mem_closure {K : Type} [Field K] [Algebra (ResidueField A) K] (ev : R →+* K)
    (hev : ∀ a, ev (f a) = algebraMap (ResidueField A) K (residue A a)) {T G : Set R} (hT : T ⊆ Set.range f)
    {D : Subalgebra (ResidueField A) K} (hG : ∀ g ∈ G, ev g ∈ D) {b : R} (hb : b ∈ Subring.closure (T ∪ G)) :
    ev b ∈ D := by
  induction hb using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · obtain ⟨a, rfl⟩ := hT hx
      rw [hev]
      exact D.algebraMap_mem _
    · exact hG x hx
  | zero => rw [map_zero]; exact D.zero_mem
  | one => rw [map_one]; exact D.one_mem
  | add x y _ _ hx hy => rw [map_add]; exact D.add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact D.neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact D.mul_mem hx hy

theorem finite_residue [IsLocalHom f] {K : Type} [Field K] [Algebra (ResidueField A) K] (ev : R →+* K)
    (hk : RingHom.ker ev = maximalIdeal R)
    (hev : ∀ a, ev (f a) = algebraMap (ResidueField A) K (residue A a)) {T : Set R} {G : Finset R}
    (hT : T ⊆ Set.range f)
    (hb : ∀ r : R, ∃ a ∈ Subring.closure (T ∪ (G : Set R)), ∃ b ∈ Subring.closure (T ∪ (G : Set R)),
      b ∉ maximalIdeal R ∧ b * r - a ∈ maximalIdeal R)
    (hG : ∀ g ∈ G, IsAlgebraic (ResidueField A) (ev g)) : ((residue R).comp f).Finite := by
  classical
  have hker : ∀ r ∈ maximalIdeal R, ev r = 0 := fun r hr => by
    rw [← RingHom.mem_ker, hk]; exact hr

  let ι : ResidueField R →+* K := Ideal.Quotient.lift (maximalIdeal R) ev hker
  have hι : ∀ r, ι (residue R r) = ev r := fun r => rfl

  let D : Subalgebra (ResidueField A) K := Algebra.adjoin (ResidueField A) ((ev : R → K) '' (G : Set R))
  have hDfin : Module.Finite (ResidueField A) D :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (G.finite_toSet.image _)
      (by rintro _ ⟨g, hg, rfl⟩; exact (hG g hg).isIntegral)
  have hB : ∀ c ∈ Subring.closure (T ∪ (G : Set R)), ev c ∈ D := fun c hc =>
    isAlgebraic_of_mem_closure f ev hev hT (D := D)
      (fun g hg => Algebra.subset_adjoin (Set.mem_image_of_mem _ hg)) hc
  have hDint : ∀ d ∈ D, IsIntegral (ResidueField A) d := fun d hd =>
    (Algebra.IsIntegral.isIntegral (R := ResidueField A) (⟨d, hd⟩ : ↥D)).map D.val

  have hrange : ∀ x : ResidueField R, ι x ∈ D := by
    intro x
    obtain ⟨r, rfl⟩ := residue_surjective x
    obtain ⟨a, ha, c, hc, hcm, hca⟩ := hb r
    have h1 : ev c * ev r = ev a := by
      have := hker _ hca
      rw [map_sub, map_mul, sub_eq_zero] at this
      exact this
    have hc0 : ev c ≠ 0 := fun h0 => hcm (by rw [← hk]; exact RingHom.mem_ker.mpr h0)
    have h2 : ev r = ev a * (ev c)⁻¹ := by rw [← h1]; field_simp
    rw [hι, h2]
    exact D.mul_mem (hB a ha) ((hDint _ (hB c hc)).inv_mem (hB c hc))
  letI : Algebra (ResidueField A) (ResidueField R) := (ResidueField.map f).toAlgebra
  have hcompat : ∀ y : ResidueField A, ι (algebraMap _ _ y) = algebraMap (ResidueField A) K y := by
    intro y
    obtain ⟨a, rfl⟩ := residue_surjective y
    show ι (ResidueField.map f (residue A a)) = _
    rw [ResidueField.map_residue, hι, hev]
  let L : ResidueField R →ₗ[ResidueField A] D :=
    { toFun := fun x => ⟨ι x, hrange x⟩
      map_add' := fun x y => Subtype.ext (map_add ι x y)
      map_smul' := fun y x => Subtype.ext (by
        simp only [Algebra.smul_def, map_mul, hcompat, RingHom.id_apply]
        rfl) }
  have hfin : Module.Finite (ResidueField A) (ResidueField R) :=
    FiniteDimensional.of_injective L (fun x y h => ι.injective (congrArg Subtype.val h))
  rw [← ResidueField.map_comp_residue f]
  exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ residue_surjective)

end Alg

theorem exists_geomPoint {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (ξ : Sp R ⟶ S) (p : Sp R)
    (hp : ξ p = ξ (closedPoint R)) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) K)
      (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ ∧ RingHom.ker ev = p.asIdeal ∧
      (∀ a, ev ((Scheme.stalkClosedPointTo ξ).hom a) = algebraMap _ K (residue _ a)) ∧
      (∀ x, x ∈ k₀ ↔ IsAlgebraic (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) x) ∧
      (∀ q, (spMap ev ≫ ξ) q = ξ (closedPoint R)) ∧ ∃ P₀ : Sp k₀ ⟶ S, spMap k₀.subtype ≫ P₀ = spMap ev ≫ ξ := by
  classical
  haveI : p.asIdeal.IsPrime := p.isPrime
  haveI : IsDomain (R ⧸ p.asIdeal) := Ideal.Quotient.isDomain _

  have hcomap : p.asIdeal.comap (Scheme.stalkClosedPointTo ξ).hom = maximalIdeal (S.presheaf.stalk (ξ (closedPoint R))) := by
    have e2 : S.fromSpecStalk _ (Spec.map (Scheme.stalkClosedPointTo ξ) p) =
        S.fromSpecStalk _ (closedPoint (S.presheaf.stalk (ξ (closedPoint R)))) := by
      rw [Scheme.fromSpecStalk_closedPoint, ← Scheme.Hom.comp_apply,
        Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hp]
    have e3 := (S.fromSpecStalk (ξ (closedPoint R))).isEmbedding.injective e2
    exact congrArg PrimeSpectrum.asIdeal e3

  let ev : R →+* AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)) :=
    (algebraMap (FractionRing (R ⧸ p.asIdeal)) (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)))).comp ((algebraMap (R ⧸ p.asIdeal) (FractionRing (R ⧸ p.asIdeal))).comp (Ideal.Quotient.mk p.asIdeal))
  have hker0 : ∀ (P : Ideal R) [P.IsPrime],
      RingHom.ker ((algebraMap (FractionRing (R ⧸ P)) (AlgebraicClosure (FractionRing (R ⧸ P)))).comp
        ((algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mk P))) = P := by
    intro P _
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.comp_apply,
      map_eq_zero_iff _ (algebraMap (FractionRing (R ⧸ P)) (AlgebraicClosure (FractionRing (R ⧸ P)))).injective,
      map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P))), Ideal.Quotient.eq_zero_iff_mem]
  have hker : RingHom.ker ev = p.asIdeal := hker0 p.asIdeal
  have hev0 : ∀ a ∈ maximalIdeal (S.presheaf.stalk (ξ (closedPoint R))), (ev.comp (Scheme.stalkClosedPointTo ξ).hom) a = 0 := fun a ha => by
    rw [← hcomap] at ha
    show ev ((Scheme.stalkClosedPointTo ξ).hom a) = 0
    rw [← RingHom.mem_ker, hker]
    exact ha
  let ψ : ResidueField (S.presheaf.stalk (ξ (closedPoint R))) →+* AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)) := Ideal.Quotient.lift (maximalIdeal (S.presheaf.stalk (ξ (closedPoint R)))) (ev.comp (Scheme.stalkClosedPointTo ξ).hom) hev0
  letI alg : Algebra (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal))) := ψ.toAlgebra
  let k₀ : Subfield (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal))) := (algebraicClosure (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)))).toSubfield
  have hmem : ∀ x, x ∈ k₀ ↔ IsAlgebraic (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) x := fun x => mem_algebraicClosure_iff
  have hev : ∀ a, ev ((Scheme.stalkClosedPointTo ξ).hom a) = algebraMap (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal))) (residue (S.presheaf.stalk (ξ (closedPoint R))) a) := fun a => rfl
  have hk₀ : IsAlgClosed (algebraicClosure (ResidueField (S.presheaf.stalk (ξ (closedPoint R))))
      (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)))) :=
    IsAlgClosure.isAlgClosed (ResidueField (S.presheaf.stalk (ξ (closedPoint R))))

  have hpts : ∀ q, (spMap ev ≫ ξ) q = ξ (closedPoint R) := by
    intro q
    haveI : q.asIdeal.IsPrime := q.isPrime
    rw [Scheme.Hom.comp_apply, ← hp]
    congr 1
    apply PrimeSpectrum.ext
    show Ideal.comap ev q.asIdeal = p.asIdeal
    rw [Ideal.eq_bot_of_prime q.asIdeal, ← RingHom.ker_eq_comap_bot, hker]

  have hψ₀ : ∀ a, (ev.comp (Scheme.stalkClosedPointTo ξ).hom) a ∈ k₀ := fun a =>
    (hmem _).mpr (by rw [RingHom.comp_apply, hev]; exact isAlgebraic_algebraMap _)
  let ψ₀ : S.presheaf.stalk (ξ (closedPoint R)) →+* k₀ := (ev.comp (Scheme.stalkClosedPointTo ξ).hom).codRestrict k₀ hψ₀
  have hP₀ : spMap k₀.subtype ≫ (Spec.map (CommRingCat.ofHom ψ₀) ≫ S.fromSpecStalk (ξ (closedPoint R))) =
      spMap ev ≫ ξ := by
    conv_rhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  exact ⟨AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)), inferInstance, inferInstance, alg, ev, k₀, hk₀, hker, hev, hmem, hpts, _, hP₀⟩

theorem range_subset_stalk {F R : Type} [CommRing F] [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (ξ : Sp R ⟶ S)
    (σ : S ⟶ Sp F) (b : F →+* R) (h : ξ ≫ σ = spMap b) :
    Set.range b ⊆ Set.range (Scheme.stalkClosedPointTo ξ).hom := by
  rintro _ ⟨c, rfl⟩
  have key : ∀ g : Sp R ⟶ Sp F, g = spMap b →
      (Sp F).presheaf.germ ⊤ (g (closedPoint R)) trivial ≫ Scheme.stalkClosedPointTo g =
        (Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫ CommRingCat.ofHom b := by
    rintro g rfl
    exact Scheme.germ_stalkClosedPointTo_Spec _
  have e := key _ h
  rw [Scheme.stalkClosedPointTo_comp] at e
  refine ⟨σ.stalkMap (ξ (closedPoint R))
    ((Sp F).presheaf.germ ⊤ _ trivial ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c)), ?_⟩
  have h1 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c)) e
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫ CommRingCat.ofHom b).hom
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c) = b c := by simp
  rw [← h2, ← h1]
  rfl

theorem eq_spMap_of_injective {F R K : Type} [CommRing F] [CommRing R] [CommRing K] (u : R →+* K)
    (hu : Function.Injective u) (σ : Sp R ⟶ Sp F) (b : F →+* R) (h : spMap u ≫ σ = spMap u ≫ spMap b) :
    σ = spMap b := by
  obtain ⟨g, rfl⟩ := Spec.map_surjective σ
  have h' : g ≫ CommRingCat.ofHom u = CommRingCat.ofHom b ≫ CommRingCat.ofHom u := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    exact h
  show Spec.map g = Spec.map (CommRingCat.ofHom b)
  congr 1
  ext x
  apply hu
  simpa using congrArg (fun φ => φ.hom x) h'

private theorem nonempty_ringHom_of_algebraic_subfield {k K L : Type} [Field k] [Field K] [Field L] [IsAlgClosed L] [Algebra k K]
    (k₀ : Subfield K) (hmem : ∀ x, x ∈ k₀ ↔ IsAlgebraic k x) (ψ : k →+* L) : Nonempty (k₀ →+* L) := by
  letI : Algebra k L := ψ.toAlgebra
  let E : IntermediateField k K :=
    k₀.toIntermediateField (fun x => (hmem _).mpr (isAlgebraic_algebraMap x))
  haveI : Algebra.IsAlgebraic k E :=
    ⟨fun x => IntermediateField.isAlgebraic_iff.mpr ((hmem _).mp x.2)⟩
  exact ⟨(IsAlgClosed.lift : E →ₐ[k] L).toRingHom⟩

theorem quasiFinite_of_pointRigid {F R : Type} [CommRing F] [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (ξ : Sp R ⟶ S)
    (σ : S ⟶ Sp F) (b : F →+* R) (hb : ξ ≫ σ = spMap b) (hft : ((residue R).comp b).EssFiniteType)
    (hc : ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
      Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)) →
      (∀ q, (spMap ev ≫ ξ) q = ξ (closedPoint R)) → (∃ P₀ : Sp k₀ ⟶ S, spMap k₀.subtype ≫ P₀ = spMap ev ≫ ξ) →
      (∀ r ∈ maximalIdeal R, ev r = 0) ∧ ∀ r, ev r ∈ k₀) :
    (∀ p : Sp R, ξ p = ξ (closedPoint R) → p = closedPoint R) ∧
      ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).Finite := by
  classical

  have key : ∀ p : Sp R, ξ p = ξ (closedPoint R) → ∃ (K : Type) (_ : Field K)
      (_ : Algebra (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) K) (ev : R →+* K),
      RingHom.ker ev = p.asIdeal ∧
      (∀ a, ev ((Scheme.stalkClosedPointTo ξ).hom a) = algebraMap _ K (residue _ a)) ∧
      (∀ r ∈ maximalIdeal R, ev r = 0) ∧
      ∀ r, IsAlgebraic (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) (ev r) := by
    intro p hp
    obtain ⟨K, _, _, _, ev, k₀, hk₀, hker, hev, hmem, hpts, hP₀⟩ := exists_geomPoint ξ p hp
    have hemb : Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)) :=
      nonempty_ringHom_of_algebraic_subfield k₀ hmem ((algebraMap (ResidueField R) (AlgebraicClosure (ResidueField R))).comp
        (ResidueField.map (Scheme.stalkClosedPointTo ξ).hom))
    obtain ⟨h1, h2⟩ := hc K ev k₀ hk₀ hemb hpts hP₀
    exact ⟨K, inferInstance, inferInstance, ev, hker, hev, h1, fun r => (hmem _).mp (h2 r)⟩
  constructor
  · intro p hp
    obtain ⟨K, _, _, ev, hker, -, h1, -⟩ := key p hp
    apply PrimeSpectrum.ext
    refine le_antisymm (le_maximalIdeal p.isPrime.ne_top) ?_
    intro r hr
    rw [← hker]
    exact h1 r hr
  · obtain ⟨K, _, _, ev, hker, hev, -, h2⟩ := key (closedPoint R) rfl

    letI : Algebra F (ResidueField R) := ((residue R).comp b).toAlgebra
    haveI : Algebra.EssFiniteType F (ResidueField R) := hft
    obtain ⟨s, hs⟩ := Algebra.EssFiniteType.cond (R := F) (S := ResidueField R)
    let lift : ResidueField R → R := fun z => (residue_surjective z).choose
    have hlift : ∀ z, residue R (lift z) = z := fun z => (residue_surjective z).choose_spec
    let G : Finset R := s.image lift
    have hadj : ∀ z ∈ Algebra.adjoin F (s : Set (ResidueField R)),
        ∃ a ∈ Subring.closure (Set.range b ∪ (G : Set R)), residue R a = z := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem x hx =>
        exact ⟨lift x, Subring.subset_closure (Or.inr (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))),
          hlift x⟩
      | algebraMap x => exact ⟨b x, Subring.subset_closure (Or.inl ⟨x, rfl⟩), rfl⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨c, hc, rfl⟩ := hy
        exact ⟨a + c, add_mem ha hc, map_add _ _ _⟩
      | mul x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨c, hc, rfl⟩ := hy
        exact ⟨a * c, mul_mem ha hc, map_mul _ _ _⟩
    have hb' : ∀ r : R, ∃ a ∈ Subring.closure (Set.range b ∪ (G : Set R)),
        ∃ c ∈ Subring.closure (Set.range b ∪ (G : Set R)),
          c ∉ maximalIdeal R ∧ c * r - a ∈ maximalIdeal R := by
      intro r
      obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective
        ((IsUnit.submonoid (ResidueField R)).comap
          (algebraMap (Algebra.adjoin F (s : Set (ResidueField R))) (ResidueField R)))
        (S := ResidueField R) (residue R r)
      have hspec := IsLocalization.mk'_spec (ResidueField R) x y
      simp only at hxy
      rw [hxy] at hspec
      obtain ⟨a, ha, hae⟩ := hadj x.1 x.2
      obtain ⟨c, hc, hce⟩ := hadj y.1.1 y.1.2
      have hyu : IsUnit (y.1.1 : ResidueField R) := y.2
      refine ⟨a, ha, c, hc, ?_, ?_⟩
      · rw [← residue_eq_zero_iff, hce]
        exact hyu.ne_zero
      · rw [← residue_eq_zero_iff, map_sub, map_mul, hce, hae, mul_comm, sub_eq_zero]
        exact hspec
    exact finite_residue (Scheme.stalkClosedPointTo ξ).hom ev hker hev (range_subset_stalk ξ σ b hb) hb'
      (fun g _ => h2 g)

end GlobalTheory.ChartQF

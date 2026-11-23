import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperOfCompleteDVRLiftGenericPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DvrCriterion

open Scheme.IdealSheafData TopologicalSpace

theorem universallyClosed_of_finite_jointly_surjective {ι : Type} [Finite ι] {X Z : Scheme.{0}}
    (A : ι → Scheme.{0}) (g : ∀ i, A i ⟶ X) (k : X ⟶ Z) (hcov : ∀ x : X, ∃ i, ∃ a, g i a = x)
    (h : ∀ i, UniversallyClosed (g i ≫ k)) : UniversallyClosed k := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have c := fun i ↦ (h i).universally_isClosedMap _ _ _
    ((IsPullback.of_hasPullback i₁ (g i)).paste_horiz H)
  intro Zs hZ
  have e : f' '' Zs = ⋃ i, (pullback.fst i₁ (g i) ≫ f') '' (pullback.fst i₁ (g i) ⁻¹' Zs) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, a, ha⟩ := hcov (i₁ x)
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
      exact Set.mem_iUnion.2 ⟨i, z, by simpa [hz] using hx, by simp [hz]⟩
    · intro y hy
      obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.1 hy
      exact ⟨_, hz, by simp⟩
  rw [e]
  exact isClosed_iUnion_of_finite fun i ↦ c i _ (hZ.preimage (Scheme.Hom.continuous _))

theorem universallyClosed_snd_of_lift {Y S : Scheme.{0}} (π : Y ⟶ S) [LocallyOfFiniteType π]
    [QuasiCompact π] [IsSeparated π] (R : Type) [CommRing R] [IsNoetherianRing R] (u : Sp R ⟶ S)
    (H : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      (x : Sp (FractionRing V) ⟶ Y) (y : Sp V ⟶ S), x ≫ π = Out.jK V ≫ y →
        ∃ x' : Sp V ⟶ Y, Out.jK V ≫ x' = x ∧ x' ≫ π = y) :
    UniversallyClosed (pullback.snd π u) := by
  classical
  set s := pullback.snd π u with hs
  have : CompactSpace (pullback π u : Scheme.{0}) := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian (pullback π u : Scheme.{0}) := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsNoetherian (pullback π u : Scheme.{0}) := {}
  let C : irreducibleComponents (pullback π u : Scheme.{0}) → Closeds (pullback π u : Scheme.{0}) :=
    fun c ↦ ⟨c.1, isClosed_of_mem_irreducibleComponents _ c.2⟩
  have : Finite (irreducibleComponents (pullback π u : Scheme.{0})) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have hr : ∀ c, Set.range (vanishingIdeal (C c)).subschemeι = c.1 := fun c ↦ by
    rw [range_subschemeι, coe_support_vanishingIdeal]; rfl
  refine universallyClosed_of_finite_jointly_surjective (fun c ↦ (vanishingIdeal (C c)).subscheme)
    (fun c ↦ (vanishingIdeal (C c)).subschemeι) s (fun x ↦ ?_) (fun c ↦ ?_)
  · refine ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
    have : x ∈ Set.range (vanishingIdeal (C ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩)).subschemeι := by
      rw [hr]; exact mem_irreducibleComponent
    exact this
  set I := vanishingIdeal (C c)
  have : IsReduced I.subscheme := GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal _
  have : IrreducibleSpace (Set.range I.subschemeι) := by
    have h1 : IsIrreducible (Set.range I.subschemeι) := by rw [hr]; exact c.2.1
    exact Subtype.irreducibleSpace h1
  have : IrreducibleSpace I.subscheme :=
    I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.irreducibleSpace_iff.2 this
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hP : IsProper (I.subschemeι ≫ s) := by
    refine GlobalTheory.TraitProper.isProper_of_lift_genericPoint R I.subscheme (I.subschemeι ≫ s) ?_
    intro V K _ _ _ _ _ _ _ x y _ hxy
    let e : FractionRing V ≃ₐ[V] K := IsLocalization.algEquiv (nonZeroDivisors V) (FractionRing V) K
    let ε : K →+* FractionRing V := e.symm.toRingEquiv.toRingHom
    let ε' : FractionRing V →+* K := e.toRingEquiv.toRingHom
    have he1 : Spec.map (CommRingCat.ofHom ε) ≫ spMap (algebraMap V K) = Out.jK V := by
      rw [spMap, ← Spec.map_comp]
      congr 2
      ext a
      exact e.symm.commutes a
    have he2 : Spec.map (CommRingCat.ofHom ε') ≫ Out.jK V = spMap (algebraMap V K) := by
      rw [spMap, Out.jK, ← Spec.map_comp]
      congr 2
      ext a
      exact e.commutes a
    have he3 : Spec.map (CommRingCat.ofHom ε') ≫ Spec.map (CommRingCat.ofHom ε) = 𝟙 _ := by
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 2
      ext a
      exact e.apply_symm_apply a
    let xF : Sp (FractionRing V) ⟶ Y :=
      Spec.map (CommRingCat.ofHom ε) ≫ x ≫ I.subschemeι ≫ pullback.fst π u
    have hxF : xF ≫ π = Out.jK V ≫ (y ≫ u) := by
      have : xF ≫ π = Spec.map (CommRingCat.ofHom ε) ≫ (x ≫ I.subschemeι ≫ s) ≫ u := by
        simp [xF, hs, pullback.condition]
      rw [this, hxy, ← he1]
      simp
    obtain ⟨x'', hx1, hx2⟩ := H V xF (y ≫ u) hxF
    let x3 : Sp V ⟶ pullback π u := pullback.lift x'' y hx2
    have h3 : Out.jK V ≫ x3 = Spec.map (CommRingCat.ofHom ε) ≫ x ≫ I.subschemeι := by
      apply pullback.hom_ext
      · simp only [x3, Category.assoc, pullback.lift_fst]
        exact hx1
      · have : Spec.map (CommRingCat.ofHom ε) ≫ (x ≫ I.subschemeι ≫ s) = Out.jK V ≫ y := by
          rw [hxy, ← he1]; simp
        simp only [x3, Category.assoc, pullback.lift_snd]
        exact this.symm
    have hdom : IsDominant (Out.jK V) := by
      have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective _ _
      refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩
      exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
    have hrange : Set.range x3 ⊆ (C c : Set (pullback π u : Scheme.{0})) := by
      rintro _ ⟨v, rfl⟩
      have hv : v ∈ closure (Set.range (Out.jK V)) := (Out.jK V).denseRange v
      have := map_mem_closure x3.continuous hv (t := (C c : Set (pullback π u : Scheme.{0}))) (by
        rintro _ ⟨w, rfl⟩
        change x3 (Out.jK V w) ∈ c.1
        rw [← Scheme.Hom.comp_apply, h3, ← hr c]
        exact ⟨(Spec.map (CommRingCat.ofHom ε) ≫ x) w, by rw [← Scheme.Hom.comp_apply, Category.assoc]⟩)
      rwa [(C c).isClosed.closure_eq] at this
    have hker : I.subschemeι.ker ≤ x3.ker := by
      rw [I.ker_subschemeι]
      exact GlobalTheory.ReducedSubgroup.vanishingIdeal_le_ker x3 (C c) hrange
    refine ⟨IsClosedImmersion.lift I.subschemeι x3 hker, ?_⟩
    rw [← cancel_mono I.subschemeι, Category.assoc, IsClosedImmersion.lift_fac, ← he2,
      Category.assoc, h3, ← Category.assoc, ← Category.assoc, he3, Category.id_comp]
  exact inferInstance

theorem existence_of_lift_discreteValuationRing : ∀ {Y S : Scheme.{0}} [IsLocallyNoetherian S] (π : Y ⟶ S), LocallyOfFiniteType π → QuasiCompact π → IsSeparated π → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (x : Sp (FractionRing V) ⟶ Y) (y : Sp V ⟶ S), x ≫ π = Out.jK V ≫ y → ∃ x' : Sp V ⟶ Y, Out.jK V ≫ x' = x ∧ x' ≫ π = y) → ValuativeCriterion.Existence π := by
  intro Y S _ π _ _ _ H
  have hUC : UniversallyClosed π := by
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @UniversallyClosed) S.affineOpenCover.openCover]
    intro i
    have := S.affineOpenCover.map_prop i
    have hR : IsNoetherianRing (S.affineOpenCover.X i) :=
      isLocallyNoetherian_Spec.1 (isLocallyNoetherian_of_isOpenImmersion (S.affineOpenCover.f i))
    exact @universallyClosed_snd_of_lift Y S π _ _ _ (S.affineOpenCover.X i) _ hR
      (S.affineOpenCover.openCover.f i) H
  have h := hUC
  rw [UniversallyClosed.eq_valuativeCriterion] at h
  exact h.1

end GlobalTheory.DvrCriterion

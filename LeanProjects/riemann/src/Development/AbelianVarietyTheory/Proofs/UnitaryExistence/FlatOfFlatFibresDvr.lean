import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TensorProduct IsLocalRing

namespace GlobalTheory

namespace FibreFlat

section Algebra

variable {T : Type*} (K : Type*) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
  [Algebra T K] [IsFractionRing T K]

theorem includeRight_bijective {C : Type*} [CommRing C] [Algebra T C] {π : T} (hπ : Irreducible π)
    (hu : IsUnit (algebraMap T C π)) :
    Function.Bijective (Algebra.TensorProduct.includeRight : C →ₐ[T] K ⊗[T] C) := by
  have h : Algebra.algebraMapSubmonoid C (nonZeroDivisors T) ≤ IsUnit.submonoid C := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero ht) hπ
    change IsUnit _
    rw [map_mul, map_pow]
    exact (u.isUnit.map _).mul (hu.pow n)
  have h2 : Function.Bijective (algebraMap C (C ⊗[T] K)) :=
    (IsLocalization.atUnits C (S := C ⊗[T] K) _ h).bijective
  exact (Algebra.TensorProduct.comm T C K).bijective.comp h2

theorem ringHom_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra T A] [Algebra T B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat T B] (φ : A →ₐ[T] B)
    (hK : (Algebra.TensorProduct.map (AlgHom.id T K) φ : K ⊗[T] A →+* K ⊗[T] B).Flat)
    (hκ : (Algebra.TensorProduct.map (AlgHom.id T (ResidueField T)) φ :
      ResidueField T ⊗[T] A →+* ResidueField T ⊗[T] B).Flat) : (φ : A →+* B).Flat := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have key : ∀ (P : Ideal B) [P.IsPrime],
      (((IsScalarTower.toAlgHom T B (Localization.AtPrime P)).comp φ : A →ₐ[T] _) :
        A →+* Localization.AtPrime P).Flat := by
    intro P _
    let l := IsScalarTower.toAlgHom T B (Localization.AtPrime P)
    have hl : (l : B →+* Localization.AtPrime P).Flat :=
      RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ P.primeCompl)
    have hbc : ∀ (L : Type _) [CommRing L] [Algebra T L],
        (Algebra.TensorProduct.map (AlgHom.id T L) φ : L ⊗[T] A →+* L ⊗[T] B).Flat →
        (Algebra.TensorProduct.map (AlgHom.id T L) (l.comp φ) :
          L ⊗[T] A →+* L ⊗[T] Localization.AtPrime P).Flat := by
      intro L _ _ h
      rw [Algebra.TensorProduct.map_id_comp]
      exact h.comp (RingHom.Flat.lTensor (S := T) L hl)
    by_cases hu : IsUnit (algebraMap T (Localization.AtPrime P) π)
    · have := IsLocalization.flat K (nonZeroDivisors T)
      refine ringHom_flat_of_square
        (α := (Algebra.TensorProduct.includeRight : A →ₐ[T] K ⊗[T] A))
        (β := (Algebra.TensorProduct.includeRight : _ →ₐ[T] K ⊗[T] Localization.AtPrime P))
        (φ' := (Algebra.TensorProduct.map (AlgHom.id T K) (l.comp φ) :
          K ⊗[T] A →+* K ⊗[T] Localization.AtPrime P)) (by ext a; simp [l]) ?_
        (.of_bijective (includeRight_bijective K hπ hu)) ?_
      · have h1 : (algebraMap A (A ⊗[T] K)).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
        exact h1.comp (g := (Algebra.TensorProduct.comm T A K : A ⊗[T] K →+* K ⊗[T] A))
          (.of_bijective (Algebra.TensorProduct.comm T A K).bijective)
      · rw [Algebra.TensorProduct.map_id_comp]
        exact hK.comp (RingHom.Flat.lTensor (S := T) K hl)
    · have : IsLocalHom (algebraMap T (Localization.AtPrime P)) := by
        refine ((local_hom_TFAE (algebraMap T (Localization.AtPrime P))).out 0 2).mpr ?_
        rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
          Ideal.span_singleton_le_iff_mem]
        exact hu
      exact flat_of_flat_residueField_baseChange_dvr _ (hbc _ hκ)
  letI := (φ : A →+* B).toAlgebra
  change Module.Flat A B
  refine Module.flat_of_isLocalized_maximal B B (fun P ↦ Localization.AtPrime P)
    (fun P ↦ Algebra.linearMap B _) fun P _ => ?_
  exact RingHom.flat_algebraMap_iff.mp (key P)

end Algebra

def FlatOver {X Y S S' : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S) (s : S' ⟶ S) : Prop :=
  ∀ ⦃W Z : Scheme.{0}⦄ (a : W ⟶ X) (b : W ⟶ Z) (j : Z ⟶ Y) (h : Z ⟶ S'),
    IsPullback a b f j → j ≫ g = h ≫ s → Flat b

variable {X Y S S' : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ S} {s : S' ⟶ S}

theorem FlatOver.target (H : FlatOver f g s) {X' Y' : Scheme.{0}} {a' : X' ⟶ X} {f' : X' ⟶ Y'}
    {u : Y' ⟶ Y} (sq : IsPullback a' f' f u) : FlatOver f' (u ≫ g) s :=
  fun _ _ a b j h sq' e => H (a ≫ a') b (j ≫ u) h (sq'.paste_horiz sq) (by simpa using e)

theorem FlatOver.source (H : FlatOver f g s) {X' : Scheme.{0}} (i : X' ⟶ X) [Flat i] :
    FlatOver (i ≫ f) g s := by
  intro W Z a b j h sq e
  have h1 := H _ _ j h (IsPullback.of_hasPullback f j) e
  let c : W ⟶ pullback f j := pullback.lift (a ≫ i) b (by simpa using sq.w)
  have hc : c ≫ pullback.snd f j = b := pullback.lift_snd _ _ _
  have sq2 : IsPullback a c i (pullback.fst f j) :=
    IsPullback.of_bot (by rw [hc]; exact sq) (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback f j)
  have h2 : Flat c := MorphismProperty.of_isPullback sq2 ‹Flat i›
  rw [← hc]
  infer_instance

theorem flatOver_of_pullback {X Y : Over S} (φ : X ⟶ Y) (s : S' ⟶ S)
    (H : Flat ((Over.pullback s).map φ).left) : FlatOver φ.left Y.hom s := by
  intro W Z a b j h sq e
  have sq0 : IsPullback (pullback.fst X.hom s) ((Over.pullback s).map φ).left φ.left
      (pullback.fst Y.hom s) := by
    have e1 : ((Over.pullback s).map φ).left ≫ pullback.fst Y.hom s =
        pullback.fst X.hom s ≫ φ.left := pullback.lift_fst _ _ _
    have e2 : ((Over.pullback s).map φ).left ≫ pullback.snd Y.hom s =
        pullback.snd X.hom s := pullback.lift_snd _ _ _
    refine IsPullback.of_bot ?_ e1.symm (IsPullback.of_hasPullback Y.hom s)
    rw [e2, Over.w]
    exact IsPullback.of_hasPullback X.hom s
  let j' : Z ⟶ pullback Y.hom s := pullback.lift j h e
  have hj : j' ≫ pullback.fst Y.hom s = j := pullback.lift_fst _ _ _
  let a' := sq0.lift a (b ≫ j') (by rw [Category.assoc, hj]; exact sq.w)
  have sq1 : IsPullback a' b ((Over.pullback s).map φ).left j' :=
    IsPullback.of_right (by rw [hj, sq0.lift_fst]; exact sq) (sq0.lift_snd _ _ _) sq0
  exact MorphismProperty.of_isPullback sq1 H

theorem FlatOver.tensor {T L A B : Type} [CommRing T] [CommRing L] [CommRing A] [CommRing B]
    [Algebra T L] [Algebra T A] [Algebra T B] (φ : A →ₐ[T] B)
    (H : FlatOver (spMap (φ : A →+* B)) (spMap (algebraMap T A)) (spMap (algebraMap T L))) :
    (Algebra.TensorProduct.map (AlgHom.id T L) φ : L ⊗[T] A →+* L ⊗[T] B).Flat := by
  have hA := CommRingCat.isPushout_tensorProduct T L A
  have hB := CommRingCat.isPushout_tensorProduct T L B
  have sq : IsPushout (CommRingCat.ofHom (φ : A →+* B))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[T] L ⊗[T] A).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[T] L ⊗[T] B).toRingHom)
      (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id T L) φ : L ⊗[T] A →+* L ⊗[T] B)) := by
    refine IsPushout.of_left ?_ ?_ hA.flip
    · convert hB.flip using 1
      · ext t; simp
      · ext t; simp
    · ext t; simp
  have := H _ _ _ (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[T] A)))
    (isPullback_SpecMap_of_isPushout _ _ _ _ sq)
    (isPullback_SpecMap_of_isPushout _ _ _ _ hA).w.symm
  exact Flat.SpecMap_iff.mp this

set_option backward.isDefEq.respectTransparency false in
theorem flat_of_flatOver (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Field K] [Algebra T K] [IsFractionRing T K] {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Sp T)
    (h1 : Flat (f ≫ g)) (h2 : LocallyOfFiniteType (f ≫ g)) (h3 : LocallyOfFiniteType g)
    (hK : FlatOver f g (spMap (algebraMap T K))) (hκ : FlatOver f g (spMap (residue T))) :
    Flat f := by
  wlog hY : ∃ A, Y = Spec A generalizing X Y
  · refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    have sq := IsPullback.of_hasPullback f (Y.affineCover.f i)
    have e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g =
        pullback.fst f (Y.affineCover.f i) ≫ f ≫ g := by
      rw [← Category.assoc, ← sq.w, Category.assoc]
    exact this (pullback.snd f (Y.affineCover.f i)) (Y.affineCover.f i ≫ g)
      (by rw [e]; infer_instance) (by rw [e]; infer_instance) inferInstance
      (hK.target sq) (hκ.target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hY
  wlog hX : ∃ B, X = Spec B generalizing X
  · refine IsZariskiLocalAtSource.of_openCover X.affineCover fun i => ?_
    exact this (X.affineCover.f i ≫ f) (by rw [Category.assoc]; infer_instance)
      (by rw [Category.assoc]; infer_instance) (hK.source _) (hκ.source _) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h1 h2
  rw [Flat.SpecMap_iff] at h1 ⊢
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h2 h3
  letI : Algebra T A := g.hom.toAlgebra
  letI : Algebra T B := (g ≫ f).hom.toAlgebra
  haveI : Module.Flat T B := h1
  haveI : Algebra.FiniteType T B := h2
  haveI : Algebra.FiniteType T A := h3
  haveI := Algebra.FiniteType.isNoetherianRing T A
  haveI := Algebra.FiniteType.isNoetherianRing T B
  let φ : A →ₐ[T] B := { f.hom with commutes' := fun _ => rfl }
  exact ringHom_flat K φ (FlatOver.tensor φ hK) (FlatOver.tensor φ hκ)

end FibreFlat

theorem flat_of_flat_fibres_dvr :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (X Y : Over (Sp T)) (φ : X ⟶ Y), Flat X.hom → Flat Y.hom →
      LocallyOfFiniteType X.hom → LocallyOfFiniteType Y.hom →
      Flat ((Over.pullback (spMap (algebraMap T K))).map φ).left →
      Flat ((Over.pullback (spMap (IsLocalRing.residue T))).map φ).left → Flat φ.left := by
  intro T K _ _ _ _ _ _ X Y φ h1 _ h2 h3 hK hκ
  exact FibreFlat.flat_of_flatOver T K φ.left Y.hom (by rwa [Over.w]) (by rwa [Over.w]) h3
    (FibreFlat.flatOver_of_pullback φ _ hK) (FibreFlat.flatOver_of_pullback φ _ hκ)

end GlobalTheory

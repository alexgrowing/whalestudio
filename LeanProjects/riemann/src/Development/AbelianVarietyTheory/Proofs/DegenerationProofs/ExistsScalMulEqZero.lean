import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoGenericOfDenseFibres
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsAffineOpenDisjointImageOfIsConstructible
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TensorProduct

namespace GlobalTheory

namespace GenericEq

open GenericIso

theorem map_eq_generic (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X : Over (Sp R))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (Sg : Set (Sp R)) (hD : Dense Sg)
    (Y : Over (Sp R)) [IsSeparated Y.hom] (f g : X ⟶ Y)
    (H : ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
      (Over.pullback t).map f = (Over.pullback t).map g) :
    (Over.pullback (Out.jK R)).map f = (Over.pullback (Out.jK R)).map g := by
  have : IsClosedImmersion (equalizer.ι f g).left := inferInstance
  have : LocallyOfFiniteType (equalizer f g).hom := by
    rw [← Over.w (equalizer.ι f g)]; infer_instance
  have h := isIso_generic_of_dense_fibres R (equalizer f g) X (equalizer.ι f g) Sg hD
    fun x hx => by
      obtain ⟨K, _, t, ht, e⟩ := H x hx
      refine ⟨K, inferInstance, t, ht, ?_⟩
      rw [← equalizerComparison_comp_π]
      have := equalizer.ι_of_eq e
      infer_instance
  rw [← cancel_epi ((Over.pullback (Out.jK R)).map (equalizer.ι f g)), ← Functor.map_comp,
    ← Functor.map_comp, equalizer.condition]

theorem exists_smul_eq_zero {R A : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A] {D : Set (PrimeSpectrum R)} (hD : Dense D)
    (y : A) (H : ∀ x ∈ D, ∃ (K : Type) (_ : Field K) (_ : Algebra R K),
      x.asIdeal = RingHom.ker (algebraMap R K) ∧ (1 : K) ⊗ₜ[R] y = 0) :
    ∃ a : R, a ≠ 0 ∧ algebraMap R A a * y = 0 := by
  let F := Ideal.Quotient.mkₐ R (Ideal.span {y})
  have hF : Function.Surjective F := Ideal.Quotient.mkₐ_surjective _ _
  obtain ⟨a, ha0, ha⟩ := exists_pow_smul_ker_eq_zero_of_dense F hD fun x hx => by
    obtain ⟨K, _, _, hK, hy⟩ := H x hx
    refine (bijective_residueField F K x hK ⟨?_,
      Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hF⟩).1
    rw [RingHom.injective_iff_ker_eq_bot, Algebra.TensorProduct.lTensor_ker F hF,
      show RingHom.ker F = Ideal.span {y} from Ideal.mk_ker,
      Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_bot]
    exact hy
  obtain ⟨n, hn⟩ := ha y (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self y))
  exact ⟨a ^ n, pow_ne_zero _ ha0, by rw [← Algebra.smul_def]; exact hn⟩

theorem appTop_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (q : Z ⟶ Y) (p : Y ⟶ Sp R)
    (a : R) : q.appTop.hom (Out.scal p a) = Out.scal (q ≫ p) a := by
  rfl

theorem exists_scal_mul_chart {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (X : Over (Sp R)) [LocallyOfFiniteType X.hom] {Sg : Set (Sp R)} (hD : Dense Sg)
    (u : Γ(X.left, ⊤))
    (H : ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
      (pullback.fst X.hom t).appTop.hom u = 0)
    (A : CommRingCat.{0}) (j : Spec A ⟶ X.left) [IsOpenImmersion j] :
    ∃ a : R, a ≠ 0 ∧ j.appTop.hom (Out.scal X.hom a * u) = 0 := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ X.hom)
  let : Algebra R A := φ.hom.toAlgebra
  have : Algebra.FiniteType R A := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hφ' : Spec.map (CommRingCat.ofHom (algebraMap R A)) = j ≫ X.hom := hφ
  obtain ⟨a, ha0, ha⟩ := exists_smul_eq_zero (R := R) hD
    ((Scheme.ΓSpecIso A).hom.hom (j.appTop.hom u)) fun x hx => by
      obtain ⟨K, _, t, ht, hu⟩ := H x hx
      obtain ⟨ψ, rfl⟩ := Spec.map_surjective t
      let : Algebra R K := ψ.hom.toAlgebra
      refine ⟨K, inferInstance, inferInstance, ?_, ?_⟩
      · have : Spec.map ψ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) = x :=
          ht.le (Set.mem_range_self _)
        rw [← this]
        rfl
      · have w := (isPullback_tensor (R := R) K A).w
        rw [hφ', ← Category.assoc] at w
        have e := congrArg (fun k => k.appTop.hom u) (pullback.lift_fst _ _ w)
        simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at e
        erw [hu, map_zero] at e
        have n := congrArg (fun k => k.hom (j.appTop.hom u)) (Scheme.ΓSpecIso_naturality
          (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
            (R := R) (A := K) (B := A)).toRingHom))
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at n
        erw [← e, map_zero] at n
        exact n.symm
  refine ⟨a, ha0, ?_⟩
  apply (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.injective
  rw [map_zero, ← ha, map_mul, map_mul, appTop_scal, ← hφ]
  congr 1
  have n := congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.ΓSpecIso_naturality φ)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at n
  refine n.trans ?_
  rw [Iso.inv_hom_id_apply]
  rfl

theorem exists_scal_mul_eq_zero (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (X : Over (Sp R)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (Sg : Set (Sp R))
    (hD : Dense Sg) (u : Γ(X.left, ⊤))
    (H : ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
      (pullback.fst X.hom t).appTop.hom u = 0) :
    ∃ a : R, a ≠ 0 ∧ Out.scal X.hom a * u = 0 := by
  classical
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let 𝒰 : X.left.OpenCover := X.left.affineCover.finiteSubcover
  have hc : ∀ i : 𝒰.I₀, ∃ a : R, a ≠ 0 ∧ (𝒰.f i).appTop.hom (Out.scal X.hom a * u) = 0 := by
    intro i
    obtain ⟨a, ha0, ha⟩ :=
      exists_scal_mul_chart X hD u H _ ((𝒰.X i).isoSpec.inv ≫ 𝒰.f i)
    refine ⟨a, ha0, ?_⟩
    rw [← (𝒰.X i).isoSpec.hom_inv_id_assoc (𝒰.f i), Scheme.Hom.comp_appTop,
      CommRingCat.hom_comp, RingHom.comp_apply, ha, map_zero]
  choose a ha0 ha using hc
  refine ⟨∏ i, a i, Finset.prod_ne_zero_iff.2 fun i _ => ha0 i,
    Scheme.zero_of_zero_cover _ 𝒰 fun i => ?_⟩
  obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
  have e : Out.scal X.hom (∏ i, a i) * u = Out.scal X.hom b * (Out.scal X.hom (a i) * u) := by
    rw [hb]
    simp only [Out.scal, map_mul]
    ring
  rw [e, map_mul]
  exact mul_eq_zero_of_right _ (ha i)

theorem exists_mem_of_not_mem (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (X : Over (Sp R)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (Sg : Set (Sp R))
    (hD : Dense Sg) (V : X.left.Opens) (H : ∀ x : X.left, X.hom x ∈ Sg → x ∈ V) :
    ∃ a : R, a ≠ 0 ∧ ∀ x : X.left, a ∉ (X.hom x).asIdeal → x ∈ V := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  have hC : Topology.IsConstructible ((V : Set X.left)ᶜ) :=
    (IsCompact.isConstructible (TopologicalSpace.NoetherianSpace.isCompact _) V.isOpen).compl
  obtain ⟨W, ⟨y, hy⟩, -, hW⟩ :=
    exists_isAffineOpen_disjoint_image_of_isConstructible_of_disjoint_dense X.left (Sp R) X.hom
      _ Sg hC hD (Set.disjoint_left.2 (by rintro _ ⟨x, hx, rfl⟩ h; exact hx (H x h)))
  obtain ⟨_, ⟨a, rfl⟩, hya, haW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hy W.isOpen
  refine ⟨a, ?_, fun x hx => ?_⟩
  · rintro rfl
    exact hya (Ideal.zero_mem _)
  · by_contra hxV
    exact Set.disjoint_left.1 hW ⟨x, hxV, rfl⟩ (haW hx)

end GenericEq

open GenericEq

theorem generic_of_dense_fibres :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X : Over (Sp R)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (Sg : Set (Sp R)), Dense Sg → (∀ (Y : Over (Sp R)) [IsSeparated Y.hom] (f g : X ⟶ Y), (∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧ (Over.pullback t).map f = (Over.pullback t).map g) → (Over.pullback (Out.jK R)).map f = (Over.pullback (Out.jK R)).map g) ∧ (∀ u : Γ(X.left, ⊤), (∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧ (pullback.fst X.hom t).appTop.hom u = 0) → ∃ a : R, a ≠ 0 ∧ Out.scal X.hom a * u = 0) ∧ (∀ V : X.left.Opens, (∀ x : X.left, X.hom x ∈ Sg → x ∈ V) → ∃ a : R, a ≠ 0 ∧ ∀ x : X.left, a ∉ (X.hom x).asIdeal → x ∈ V) := by
  intro R _ _ _ X _ _ Sg hD
  exact ⟨fun Y _ f g => map_eq_generic R X Sg hD Y f g, exists_scal_mul_eq_zero R X Sg hD,
    exists_mem_of_not_mem R X Sg hD⟩

end GlobalTheory

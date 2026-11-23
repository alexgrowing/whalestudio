import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafSHSysPf

open CategoryTheory Limits TensorProduct

noncomputable section

namespace UpperTheory.Cb.FilteredPoints

structure Pt (R Ω : Type) [CommRing R] [Field Ω] [Algebra R Ω] where
  n : ℕ
  I : Ideal (MvPolynomial (Fin n) R)
  et : Algebra.Etale R (MvPolynomial (Fin n) R ⧸ I)
  ψ : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] Ω

variable {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω]

abbrev Pt.A (X : Pt R Ω) : Type := MvPolynomial (Fin X.n) R ⧸ X.I

instance (X : Pt R Ω) : Algebra.Etale R X.A := X.et

theorem exists_pt (E : Type) [CommRing E] [Algebra R E] [Algebra.Etale R E] (ψ : E →ₐ[R] Ω) :
    ∃ (X : Pt R Ω) (e : E ≃ₐ[R] X.A), ∀ x, X.ψ (e x) = ψ x := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType R E)
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  have het : Algebra.Etale R (MvPolynomial (Fin n) R ⧸ RingHom.ker f) :=
    Algebra.Etale.of_equiv e.symm
  refine ⟨⟨n, RingHom.ker f, het, ψ.comp e.toAlgHom⟩, e.symm, fun x => ?_⟩
  simp

instance : SmallCategory (Pt R Ω) where
  Hom X Y := {f : X.A →ₐ[R] Y.A // ∀ x, Y.ψ (f x) = X.ψ x}
  id X := ⟨AlgHom.id R _, fun _ => rfl⟩
  comp f g := ⟨g.1.comp f.1, fun x => by simp [g.2, f.2]⟩
  id_comp _ := Subtype.ext (AlgHom.ext fun _ => rfl)
  comp_id _ := Subtype.ext (AlgHom.ext fun _ => rfl)
  assoc _ _ _ := Subtype.ext (AlgHom.ext fun _ => rfl)

theorem upper (X Y : Pt R Ω) : ∃ (Z : Pt R Ω) (_ : X ⟶ Z) (_ : Y ⟶ Z), True := by
  have h1 : Algebra.Etale X.A (X.A ⊗[R] Y.A) := Algebra.Etale.baseChange R Y.A X.A
  have h2 : Algebra.Etale R (X.A ⊗[R] Y.A) := Algebra.Etale.comp R X.A _
  obtain ⟨Z, e, he⟩ := exists_pt (X.A ⊗[R] Y.A)
    (Algebra.TensorProduct.lift X.ψ Y.ψ (fun _ _ => Commute.all _ _))
  refine ⟨Z, ⟨e.toAlgHom.comp Algebra.TensorProduct.includeLeft, fun x => ?_⟩,
    ⟨e.toAlgHom.comp Algebra.TensorProduct.includeRight, fun x => ?_⟩, trivial⟩
  · simp [he]
  · simp [he]

theorem coeq {X Y : Pt R Ω} (f g : X ⟶ Y) : ∃ (Z : Pt R Ω) (h : Y ⟶ Z), f ≫ h = g ≫ h := by
  obtain ⟨t, ht, ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := X.A)).1
    inferInstance
  let L : X.A ⊗[R] X.A →ₐ[R] Y.A := Algebra.TensorProduct.lift f.1 g.1 (fun _ _ => Commute.all _ _)
  have hcomp : Y.ψ.comp L = X.ψ.comp (Algebra.TensorProduct.lmul' R) := by
    apply Algebra.TensorProduct.ext
    · ext x; simp [L, f.2]
    · ext x; simp [L, g.2]
  have hs : Y.ψ (L t) = 1 := by
    have := congrArg (fun φ => φ t) hcomp
    simpa [ht1] using this
  have hs' : ∀ x, (g.1 x - f.1 x) * L t = 0 := fun x => by
    have := congrArg L (ht x)
    simpa [L, map_mul, map_sub] using this
  let B := Localization.Away (L t)
  have h1 : Algebra.Etale Y.A B := Algebra.Etale.of_isLocalizationAway (L t)
  have h2 : Algebra.Etale R B := Algebra.Etale.comp R Y.A B
  let ψB : B →ₐ[R] Ω := IsLocalization.Away.liftAlgHom (L t) (f := Y.ψ) (by rw [hs]; exact isUnit_one)
  have hψB : ∀ y, ψB (algebraMap Y.A B y) = Y.ψ y := fun y => by
    simp [ψB]
  obtain ⟨Z, e, he⟩ := exists_pt B ψB
  refine ⟨Z, ⟨e.toAlgHom.comp (IsScalarTower.toAlgHom R Y.A B), fun y => ?_⟩, ?_⟩
  · simp [he, hψB]
  · apply Subtype.ext
    apply AlgHom.ext
    intro x
    have hu : IsUnit (algebraMap Y.A B (L t)) := IsLocalization.Away.algebraMap_isUnit (L t)
    have h0 : algebraMap Y.A B (g.1 x - f.1 x) = 0 := by
      apply hu.mul_left_injective
      simp only [zero_mul, ← map_mul, hs' x, map_zero]
    have h3 : algebraMap Y.A B (f.1 x) = algebraMap Y.A B (g.1 x) := by
      rw [map_sub, sub_eq_zero] at h0; exact h0.symm
    show e (algebraMap Y.A B (f.1 x)) = e (algebraMap Y.A B (g.1 x))
    rw [h3]

instance : IsFilteredOrEmpty (Pt R Ω) := ⟨upper, fun _ _ => coeq⟩

instance : IsFiltered (Pt R Ω) where
  nonempty := by
    obtain ⟨X, -, -⟩ := exists_pt (R := R) (Ω := Ω) R (Algebra.ofId R Ω)
    exact ⟨X⟩

def D : Pt R Ω ⥤ CommRingCat.{0} where
  obj X := CommRingCat.of X.A
  map f := CommRingCat.ofHom f.1.toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

def tc : Cocone (D (R := R) (Ω := Ω)) where
  pt := CommRingCat.of Ω
  ι :=
    { app := fun X => CommRingCat.ofHom X.ψ.toRingHom
      naturality := fun X Y f => by
        ext x
        exact f.2 x }

theorem cof_step (X : Pt R Ω) (E : Type) [CommRing E] [Algebra X.A E] [Algebra.Etale X.A E]
    (ψ : E →+* Ω) (h : ψ.comp (algebraMap X.A E) = X.ψ.toRingHom) :
    ∃ (Y : Pt R Ω) (g : X ⟶ Y) (φ : E →+* Y.A),
      φ.comp (algebraMap X.A E) = g.1.toRingHom ∧ Y.ψ.toRingHom.comp φ = ψ := by
  letI : Algebra R E := ((algebraMap X.A E).comp (algebraMap R X.A)).toAlgebra
  haveI : IsScalarTower R X.A E := .of_algebraMap_eq' rfl
  haveI : Algebra.Etale R E := Algebra.Etale.comp R X.A E
  let ψ' : E →ₐ[R] Ω :=
    { ψ with
      commutes' := fun r => by
        have := RingHom.congr_fun h (algebraMap R X.A r)
        simpa [IsScalarTower.algebraMap_apply R X.A E] using this }
  obtain ⟨Y, e, he⟩ := exists_pt E ψ'
  refine ⟨Y, ⟨e.toAlgHom.comp (IsScalarTower.toAlgHom R X.A E), fun x => ?_⟩,
    e.toAlgHom.toRingHom, rfl, ?_⟩
  · have := RingHom.congr_fun h x
    simpa [he, ψ'] using this
  · ext x
    exact he x

theorem sys (R : CommRingCat.{0}) (p : PrimeSpectrum R) (Ω : Type) [Field Ω] [IsSepClosed Ω]
    [Algebra R Ω] (hk : RingHom.ker (algebraMap R Ω) = p.asIdeal) :
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
      (u : ∀ j, R ⟶ D.obj j),
      (∀ {j j' : J} (g : j ⟶ j'), u j ≫ D.map g = u j') ∧ (∀ j, (u j).hom.Etale) ∧
      (∀ j, ∃ q : PrimeSpectrum (D.obj j), q.comap (u j).hom = p) ∧
      ∃ (c : Cocone D), Nonempty (IsColimit c) ∧ LateralTheory.E.LeafSHSysPf.Cof D c := by
  refine ⟨Pt R Ω, inferInstance, inferInstance, D,
    fun X => CommRingCat.ofHom (algebraMap R X.A), ?_, ?_, ?_,
    colimit.cocone D, ⟨colimit.isColimit D⟩, ?_⟩
  · intro j j' g
    ext x
    exact g.1.commutes x
  · intro j
    exact (RingHom.etale_algebraMap (R := R) (S := j.A)).2 j.et
  · intro X
    refine ⟨⟨RingHom.ker X.ψ.toRingHom, RingHom.ker_isPrime _⟩, ?_⟩
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro x
    rw [← hk]
    show X.ψ (algebraMap R X.A x) = 0 ↔ algebraMap R Ω x = 0
    rw [X.ψ.commutes]
  · let ω : (colimit.cocone (D (R := R) (Ω := Ω))).pt →+* Ω := ((colimit.isColimit D).desc tc).hom
    have hω : ∀ X : Pt R Ω, ω.comp ((colimit.cocone D).ι.app X).hom = X.ψ.toRingHom := fun X => by
      have := (colimit.isColimit (D (R := R) (Ω := Ω))).fac tc X
      exact congrArg CommRingCat.Hom.hom this
    refine ⟨Ω, inferInstance, inferInstance, ω, ?_⟩
    intro j E i1 i2 i3 ψ h
    obtain ⟨Y, g, φ, h1, h2⟩ := @cof_step R Ω _ _ _ j E i1 i2 i3 ψ (h.trans (hω j))
    refine ⟨Y, g, φ, h1, ?_⟩
    ext x
    exact (RingHom.congr_fun (hω Y) (φ x)).trans (RingHom.congr_fun h2 x)

theorem closure_inj (K : Type) [Field K] : Function.Injective (algebraMap K (AlgebraicClosure K)) :=
  (algebraMap K (AlgebraicClosure K)).injective

end UpperTheory.Cb.FilteredPoints

theorem UpperTheory.Cb.sepClosed_point_filtered_etale_colimit :
    LateralTheory.E.LeafSHSysPf.LeafRingSys := by
  intro R p
  refine UpperTheory.Cb.FilteredPoints.sys R p (AlgebraicClosure p.asIdeal.ResidueField) ?_
  rw [IsScalarTower.algebraMap_eq R p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField),
    RingHom.ker_comp_of_injective _ (UpperTheory.Cb.FilteredPoints.closure_inj _)]
  exact Ideal.ker_algebraMap_residueField p.asIdeal

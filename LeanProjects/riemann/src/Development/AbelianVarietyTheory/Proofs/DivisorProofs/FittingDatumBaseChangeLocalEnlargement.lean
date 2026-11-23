import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorFiniteProjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenFibMapAlgebraMap

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EnlargeBaseChange

end GlobalTheory.EnlargeBaseChange

namespace GlobalTheory.EnlargeBaseChange

open IsLocalRing Polynomial in
open scoped TensorProduct in
private theorem exists_ringHom_tensor_of_comp_eq {R S E : Type} [CommRing R] [CommRing S]
    [CommRing E] [Algebra R S] [Algebra R E] (Z : Type) [CommRing Z] (u : S →+* Z) (v : E →+* Z)
    (h : u.comp (algebraMap R S) = v.comp (algebraMap R E)) :
    ∃ w : S ⊗[R] E →+* Z, w.comp (algebraMap S (S ⊗[R] E)) = u ∧
      w.comp (Algebra.TensorProduct.includeRight.toRingHom : E →+* S ⊗[R] E) = v := by
  letI : Algebra R Z := (v.comp (algebraMap R E)).toAlgebra
  let u' : S →ₐ[R] Z := { u with commutes' := fun r => RingHom.congr_fun h r }
  let v' : E →ₐ[R] Z := { v with commutes' := fun _ => rfl }
  refine ⟨(Algebra.TensorProduct.lift u' v' fun _ _ => Commute.all _ _).toRingHom, ?_, ?_⟩
  · refine RingHom.ext fun s => ?_
    simp [Algebra.TensorProduct.algebraMap_apply, u', v']
  · refine RingHom.ext fun e => ?_
    simp [u', v']

open IsLocalRing Polynomial in
open scoped TensorProduct in
private theorem includeRight_comp_algebraMap_eq {R S E : Type} [CommRing R] [CommRing S]
    [CommRing E] [Algebra R S] [Algebra R E] :
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := E)).toRingHom.comp
        (algebraMap R E) = (algebraMap S (S ⊗[R] E)).comp (algebraMap R S) := by
  ext r
  simp [Algebra.TensorProduct.algebraMap_apply]

open IsLocalRing Polynomial in
open scoped TensorProduct in
private theorem tensorProduct_ringHom_ext_of_comp_eq {R S E Z : Type} [CommRing R] [CommRing S] [CommRing E]
    [CommRing Z] [Algebra R S] [Algebra R E] (w₁ w₂ : S ⊗[R] E →+* Z)
    (h₁ : w₁.comp (algebraMap S (S ⊗[R] E)) = w₂.comp (algebraMap S (S ⊗[R] E)))
    (h₂ : w₁.comp (Algebra.TensorProduct.includeRight.toRingHom : E →+* S ⊗[R] E) =
      w₂.comp (Algebra.TensorProduct.includeRight.toRingHom : E →+* S ⊗[R] E)) : w₁ = w₂ := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s e =>
    have hs := RingHom.congr_fun h₁ s
    have he : w₁ ((1 : S) ⊗ₜ[R] e) = w₂ ((1 : S) ⊗ₜ[R] e) := RingHom.congr_fun h₂ e
    simp only [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply] at hs
    rw [show s ⊗ₜ[R] e = (s ⊗ₜ[R] (1 : E)) * ((1 : S) ⊗ₜ[R] e) by simp, map_mul, map_mul, hs, he]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

open IsLocalRing Polynomial in
open scoped TensorProduct in

theorem _root_.GlobalTheory.EnlargeBaseChange.fits_baseChange : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], _root_.GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = _root_.GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : _root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* _root_.GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    _root_.GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] (f : A →+* A₁) (i₁ : A₁ →+* T),
    Function.Injective i₁ → IsLocalHom i₁ → i₁.comp f = i →
    ∃ (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A₁) EA') (_ : Algebra A₁ EA')
      (_ : IsScalarTower A₁ (Polynomial A₁) EA') (_ : Algebra.Etale (Polynomial A₁) EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : _root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA') →+* _root_.GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')] DA')),
      _root_.GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA' QA' jA' ψA' DA' actA' ∧
      (∃ (β : _root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* _root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA'))
        (h : DA →+* DA'), ψA'.comp β = ψA ∧
        h.comp (algebraMap (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
          (algebraMap (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) DA').comp β) ∧
      ∃ γ : EA →+* EA',
        γ.comp (algebraMap (Polynomial A) EA) = (algebraMap (Polynomial A₁) EA').comp (Polynomial.mapRingHom f) ∧
        jA'.comp ((algebraMap EA' (Localization.AtPrime QA')).comp γ) = jA.comp (algebraMap EA (Localization.AtPrime QA)) ∧
        QA' = (maximalIdeal O).comap (jA'.comp (algebraMap EA' (Localization.AtPrime QA'))) ∧
        (∀ (Z : Type) [CommRing Z] (u : Polynomial A₁ →+* Z) (v : EA →+* Z),
          u.comp (Polynomial.mapRingHom f) = v.comp (algebraMap (Polynomial A) EA) →
          ∃ w : EA' →+* Z, w.comp (algebraMap (Polynomial A₁) EA') = u ∧ w.comp γ = v) ∧
        (∀ (Z : Type) [CommRing Z] (w₁ w₂ : EA' →+* Z),
          w₁.comp (algebraMap (Polynomial A₁) EA') = w₂.comp (algebraMap (Polynomial A₁) EA') →
          w₁.comp γ = w₂.comp γ → w₁ = w₂) := by
  intro T O _ _ _ _ _ _ _ _ _ P _ φ hφ hφs hP q hq _ A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _
    actA hfits A₁ _ _ _ f i₁ hi₁ hloc hcomp
  obtain ⟨hi, -, hqA, -, hjA, hψA, htors⟩ := hfits
  haveI : IsLocalHom φ := hφs.2.2.1
  letI : Algebra A[X] A₁[X] := (Polynomial.mapRingHom f).toAlgebra

  have huv : ((algebraMap T[X] O).comp (Polynomial.mapRingHom i₁)).comp (algebraMap A[X] A₁[X]) =
      (jA.comp (algebraMap EA (Localization.AtPrime QA))).comp (algebraMap A[X] EA) := by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hjA,
      RingHom.algebraMap_toAlgebra, Polynomial.mapRingHom_comp, hcomp]
  obtain ⟨g, hgu, hgv⟩ := exists_ringHom_tensor_of_comp_eq O _ _ huv
  let QA' : Ideal (A₁[X] ⊗[A[X]] EA) := (maximalIdeal O).comap g
  have hmemQ : ∀ z, z ∈ QA' ↔ ¬IsUnit (g z) := fun z => by
    simp [QA', Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  haveI : QA'.IsPrime := Ideal.comap_isPrime _ _
  let jA' : Localization.AtPrime QA' →+* O :=
    IsLocalization.lift (M := QA'.primeCompl) (g := g) fun s => by
      by_contra hs
      exact s.2 ((hmemQ s).2 hs)
  have hjA'comp : jA'.comp (algebraMap _ (Localization.AtPrime QA')) = g :=
    IsLocalization.lift_comp _
  have hjA'g : ∀ z, jA' (algebraMap _ (Localization.AtPrime QA') z) = g z := fun z =>
    RingHom.congr_fun hjA'comp z
  have hgγ : ∀ e, g (Algebra.TensorProduct.includeRight e) =
      jA (algebraMap EA (Localization.AtPrime QA) e) := fun e => RingHom.congr_fun hgv e
  have hgA₁ : ∀ a : A₁, g (algebraMap A₁ _ a) = algebraMap T O (i₁ a) := fun a => by
    have := RingHom.congr_fun hgu (Polynomial.C a)
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C] at this
    rw [IsScalarTower.algebraMap_apply A₁ A₁[X] (A₁[X] ⊗[A[X]] EA), Polynomial.algebraMap_eq,
      IsScalarTower.algebraMap_apply T T[X] O, Polynomial.algebraMap_eq]
    exact this
  have hjA'A₁ : ∀ a : A₁, jA' (algebraMap A₁ (Localization.AtPrime QA') a) = algebraMap T O (i₁ a) :=
    fun a => by
      rw [IsScalarTower.algebraMap_apply A₁ (A₁[X] ⊗[A[X]] EA) (Localization.AtPrime QA'), hjA'g, hgA₁]
  have hunitT : ∀ a : A₁, a ∈ nonZeroDivisors A₁ →
      IsUnit (algebraMap O (_root_.GlobalTheory.LocAcyc.GenFib T O) (algebraMap T O (i₁ a))) := fun a ha =>
    IsLocalization.map_units (M := Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
      (_root_.GlobalTheory.LocAcyc.GenFib T O)
      ⟨algebraMap T O (i₁ a), ⟨i₁ a, mem_nonZeroDivisors_of_ne_zero
        ((map_ne_zero_iff i₁ hi₁).2 (nonZeroDivisors.ne_zero ha)), rfl⟩⟩
  haveI hlocA₁ : IsLocalization
      (Algebra.algebraMapSubmonoid (Localization.AtPrime QA') (nonZeroDivisors A₁))
      (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) := by
    unfold _root_.GlobalTheory.LocAcyc.GenFib
    exact Localization.isLocalization
  let ψA' : _root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA') →+* _root_.GlobalTheory.LocAcyc.GenFib T O :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid (Localization.AtPrime QA') (nonZeroDivisors A₁))
      (g := (algebraMap O (_root_.GlobalTheory.LocAcyc.GenFib T O)).comp jA') fun s => by
        obtain ⟨a, ha, hs⟩ := s.2
        rw [RingHom.comp_apply, ← hs, hjA'A₁]
        exact hunitT a ha
  have hψA'comp : ψA'.comp (algebraMap _ (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA'))) =
      (algebraMap O (_root_.GlobalTheory.LocAcyc.GenFib T O)).comp jA' := IsLocalization.lift_comp _
  have hψA'alg : ∀ y, ψA' (algebraMap _ (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) y) =
      algebraMap O (_root_.GlobalTheory.LocAcyc.GenFib T O) (jA' y) := fun y => RingHom.congr_fun hψA'comp y
  let ℓ : Localization.AtPrime QA →+* Localization.AtPrime QA' :=
    IsLocalization.lift (M := QA.primeCompl)
      (g := (algebraMap _ (Localization.AtPrime QA')).comp
        (Algebra.TensorProduct.includeRight.toRingHom : EA →+* A₁[X] ⊗[A[X]] EA)) fun s => by
        refine IsLocalization.map_units (M := QA'.primeCompl) (Localization.AtPrime QA')
          (⟨Algebra.TensorProduct.includeRight (s : EA), ?_⟩ : QA'.primeCompl)
        rw [Ideal.mem_primeCompl_iff, hmemQ, not_not, hgγ]
        exact (IsLocalization.map_units (Localization.AtPrime QA) s).map jA
  have hℓ : ∀ e, ℓ (algebraMap EA (Localization.AtPrime QA) e) =
      algebraMap (A₁[X] ⊗[A[X]] EA) (Localization.AtPrime QA')
        (Algebra.TensorProduct.includeRight (R := A[X]) (A := A₁[X]) e) := fun e =>
    IsLocalization.lift_eq _ e
  have hγ1 : (Algebra.TensorProduct.includeRight.toRingHom : EA →+* A₁[X] ⊗[A[X]] EA).comp
      (algebraMap A[X] EA) = (algebraMap A₁[X] (A₁[X] ⊗[A[X]] EA)).comp (Polynomial.mapRingHom f) :=
    includeRight_comp_algebraMap_eq
  have hγC : ∀ a : A, Algebra.TensorProduct.includeRight (R := A[X]) (A := A₁[X]) (algebraMap A EA a) =
      algebraMap A₁ (A₁[X] ⊗[A[X]] EA) (f a) := fun a => by
    rw [IsScalarTower.algebraMap_apply A A[X] EA, Polynomial.algebraMap_eq,
      IsScalarTower.algebraMap_apply A₁ A₁[X] (A₁[X] ⊗[A[X]] EA), Polynomial.algebraMap_eq]
    have := RingHom.congr_fun hγ1 (Polynomial.C a)
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
      AlgHom.coe_toRingHom] at this
    exact this
  let β : _root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+*
      _root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA') :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid (Localization.AtPrime QA) (nonZeroDivisors A))
      (g := (algebraMap _ (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA'))).comp ℓ) fun s => by
        obtain ⟨a, ha, hs⟩ := s.2
        rw [RingHom.comp_apply, ← hs, IsScalarTower.algebraMap_apply A EA (Localization.AtPrime QA),
          hℓ, hγC, ← IsScalarTower.algebraMap_apply A₁ (A₁[X] ⊗[A[X]] EA) (Localization.AtPrime QA')]
        refine IsLocalization.map_units
          (M := Algebra.algebraMapSubmonoid (Localization.AtPrime QA') (nonZeroDivisors A₁)) _
          ⟨_, ⟨f a, mem_nonZeroDivisors_of_ne_zero fun h0 => ?_, rfl⟩⟩
        apply nonZeroDivisors.ne_zero ha
        apply hi
        rw [map_zero, ← hcomp, RingHom.comp_apply, h0, map_zero]
  have hβalg : ∀ y, β (algebraMap _ (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) y) =
      algebraMap _ (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) (ℓ y) := fun y =>
    IsLocalization.lift_eq _ y
  letI : Algebra (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))
      (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) := β.toAlgebra
  have htors' : _root_.GlobalTheory.LocAcyc.IsZModTorsor _ DA q actA := by
    unfold _root_.GlobalTheory.KeyOriginCut.IsZTorsor at htors
    unfold _root_.GlobalTheory.LocAcyc.IsZModTorsor
    exact htors
  obtain ⟨act', -, hact'⟩ := _root_.GlobalTheory.LocAcyc.isZModTorsor_baseChange
    (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))
    (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) DA q hq actA htors'
  refine ⟨A₁[X] ⊗[A[X]] EA, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    QA', inferInstance, jA', ψA',
    _root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA') ⊗[_root_.GlobalTheory.LocAcyc.GenFib A
      (Localization.AtPrime QA)] DA, inferInstance, inferInstance, act', ?_,
    ⟨β, Algebra.TensorProduct.includeRight.toRingHom, ?_, includeRight_comp_algebraMap_eq⟩,
    Algebra.TensorProduct.includeRight.toRingHom, hγ1, ?_, ?_, ?_, ?_⟩
  · unfold _root_.GlobalTheory.KeyOriginEnlarge.Fits
    refine ⟨hi₁, hloc, by simpa using hqA.map f, ?_, ?_, hψA'comp, ?_⟩
    · have hO : (maximalIdeal O).comap (algebraMap T[X] O) = _root_.GlobalTheory.KeyOriginCut.originIdeal T := by
        rw [← hφ, ← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap φ, ← hP]
        exact IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P
      show ((maximalIdeal O).comap g).comap _ = _
      rw [Ideal.comap_comap, hgu, ← Ideal.comap_comap, hO]
      exact _root_.GlobalTheory.VertUnitsNoeth.comap_originIdeal' A₁ T i₁
    · rw [IsScalarTower.algebraMap_eq A₁[X] (A₁[X] ⊗[A[X]] EA) (Localization.AtPrime QA'),
        ← RingHom.comp_assoc, hjA'comp, hgu]
    · unfold _root_.GlobalTheory.LocAcyc.IsZModTorsor at hact'
      unfold _root_.GlobalTheory.KeyOriginCut.IsZTorsor
      exact hact'
  · refine _root_.GlobalTheory.LocAcyc.genFib_ringHom_ext fun y => ?_
    have key : (ψA'.comp β).comp
        (algebraMap (Localization.AtPrime QA) (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        ψA.comp (algebraMap (Localization.AtPrime QA)
          (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) := by
      refine IsLocalization.ringHom_ext QA.primeCompl (RingHom.ext fun e => ?_)
      simp only [RingHom.comp_apply]
      rw [hβalg, hℓ, hψA'alg, hjA'g, hgγ]
      exact (RingHom.congr_fun hψA _).symm
    exact RingHom.congr_fun key y
  · rw [← RingHom.comp_assoc, hjA'comp, hgv]
  · rw [hjA'comp]
  · intro Z _ u v huv'
    exact exists_ringHom_tensor_of_comp_eq Z u v huv'
  · intro Z _ w₁ w₂ h₁ h₂
    exact tensorProduct_ringHom_ext_of_comp_eq w₁ w₂ h₁ h₂

end GlobalTheory.EnlargeBaseChange

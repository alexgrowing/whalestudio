import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AdaptedParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealEtaleBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LeadingForm
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

namespace EtaleCoordinates

theorem partialDeriv_comm (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (T : Type*) [CommRing T] [Algebra k T] [Algebra (MvPolynomial ι k) T]
    [IsScalarTower k (MvPolynomial ι k) T] [Algebra.FormallyEtale (MvPolynomial ι k) T]
    (i j : ι) (a : T) :
    partialDeriv k ι T i (partialDeriv k ι T j a)
      = partialDeriv k ι T j (partialDeriv k ι T i a) := by
  have hzero : ⁅partialDeriv k ι T i, partialDeriv k ι T j⁆ = (0 : Derivation k T T) := by
    refine derivation_ext_of_coord k ι T T _ _ ?_
    intro l
    rw [Derivation.commutator_apply]
    simp only [partialDeriv_coord]
    split_ifs <;> simp
  have h2 : ⁅partialDeriv k ι T i, partialDeriv k ι T j⁆ a = 0 := by
    rw [hzero]; simp
  rw [Derivation.commutator_apply] at h2
  linear_combination h2

end EtaleCoordinates

private theorem exists_commuting_dual_derivations (k : Type*) [CommRing k] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (A : Type*) [CommRing A] [Algebra k A] [Algebra.FormallySmooth k A]
    (e : Module.Basis ι A (KaehlerDifferential k A)) (w : ι → A)
    (hdet : IsUnit (e.det fun i : ι => KaehlerDifferential.D k A (w i))) :
    ∃ D : ι → Derivation k A A,
      (∀ i j : ι, D i (w j) = if i = j then 1 else 0) ∧
      (∀ i j : ι, ∀ a : A, D i (D j a) = D j (D i a)) := by
  let _ : Algebra (MvPolynomial ι k) A :=
    (MvPolynomial.aeval w : MvPolynomial ι k →ₐ[k] A).toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial ι k) A :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [RingHom.algebraMap_toAlgebra]
      simp [MvPolynomial.algebraMap_eq]
  have : Algebra.FormallyEtale (MvPolynomial ι k) A :=
    EtaleCoordinates.formallyEtale_aeval_of_isUnit_det e w hdet
  have hcoord : ∀ i : ι, EtaleCoordinates.coord k ι A i = w i := by
    intro i
    rw [EtaleCoordinates.coord_def, RingHom.algebraMap_toAlgebra]
    simp
  refine ⟨fun i => EtaleCoordinates.partialDeriv k ι A i, ?_, ?_⟩
  · intro i j
    rw [← hcoord j]
    exact EtaleCoordinates.partialDeriv_coord k ι A i j
  · intro i j a
    exact EtaleCoordinates.partialDeriv_comm k ι A i j a

theorem exists_regularParameters_of_formallyEtale (k : Type*) [CommRing k] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (q : Ideal S) [q.IsPrime] (A : Type*) [CommRing A] [Algebra S A] [Algebra k A]
    [IsScalarTower k S A] [IsLocalization q.primeCompl A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k (IsLocalRing.ResidueField A)] [IsScalarTower k A (IsLocalRing.ResidueField A)]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] :
    ∃ (h : ℕ) (x : Fin h → A) (D : Fin h → Derivation k A A),
      Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A ∧
      (∀ i j : Fin h, D i (x j) = if i = j then 1 else 0) ∧
      (∀ i j : Fin h, ∀ a : A, D i (D j a) = D j (D i a)) := by
  obtain ⟨g, w, J, hgq, -, hspan, -, hgdet, -⟩ :=
    EtaleCoordinates.exists_adapted_parameters k ι S q A
  let _ : Algebra (MvPolynomial ι k) A :=
    ((algebraMap S A).comp (algebraMap (MvPolynomial ι k) S)).toAlgebra
  have halg : (algebraMap (MvPolynomial ι k) A)
      = (algebraMap S A).comp (algebraMap (MvPolynomial ι k) S) := rfl
  have : IsScalarTower (MvPolynomial ι k) S A :=
    IsScalarTower.of_algebraMap_eq fun z => by rw [halg]; rfl
  have : IsScalarTower k (MvPolynomial ι k) A :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [halg, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S,
        ← IsScalarTower.algebraMap_apply k S A]
  have : Algebra.FormallyEtale S A := Algebra.FormallyEtale.of_isLocalization q.primeCompl
  have : Algebra.FormallyEtale (MvPolynomial ι k) A :=
    Algebra.FormallyEtale.comp (MvPolynomial ι k) S A
  have : Algebra.FormallySmooth k A := Algebra.FormallySmooth.comp k (MvPolynomial ι k) A
  obtain ⟨e, he⟩ : ∃ e : Module.Basis ι A (KaehlerDifferential k A),
      IsUnit (e.det fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i))) := by
    refine ⟨EtaleCoordinates.basisKaehler k ι A, ?_⟩
    rw [← EtaleCoordinates.algebraMap_det_basisKaehler k ι S A w, ← hgdet]
    exact IsLocalization.map_units (M := q.primeCompl) A ⟨g, hgq⟩
  obtain ⟨D, hD, hDD⟩ :=
    exists_commuting_dual_derivations k ι A e (fun i => algebraMap S A (w i)) he
  obtain ⟨h, ix, hix, hrange⟩ :
      ∃ (h : ℕ) (ix : Fin h → ι), Function.Injective ix ∧ Set.range ix = (↑J : Set ι) := by
    refine ⟨J.card, fun i => ((J.equivFin.symm i : {a : ι // a ∈ J}) : ι), ?_, ?_⟩
    · intro a b hab
      exact J.equivFin.symm.injective (Subtype.ext hab)
    · ext l
      simp only [Set.mem_range, Finset.mem_coe]
      constructor
      · rintro ⟨i, rfl⟩
        exact (J.equivFin.symm i).2
      · intro hl
        exact ⟨J.equivFin ⟨l, hl⟩, by simp⟩
  have hset : (algebraMap S A) '' (w '' (↑J : Set ι))
      = Set.range fun i => algebraMap S A (w (ix i)) := by
    rw [← hrange]
    ext a
    constructor
    · rintro ⟨b, ⟨l, ⟨i, rfl⟩, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨w (ix i), ⟨ix i, ⟨i, rfl⟩, rfl⟩, rfl⟩
  refine ⟨h, fun i => algebraMap S A (w (ix i)), fun i => D (ix i), ?_, ?_, ?_⟩
  · rw [← hspan, Ideal.map_span, hset]
  · intro i j
    rw [hD]
    simp only [show (ix i = ix j) ↔ (i = j) from ⟨fun hc => hix hc, fun hc => by rw [hc]⟩]
  · intro i j a
    exact hDD (ix i) (ix j) a

theorem exists_regularParameters_stalk_of_smooth (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    letI := stalkAlgebra k p x
    ∃ (h : ℕ) (y : Fin h → X.presheaf.stalk x)
      (D : Fin h → Derivation k (X.presheaf.stalk x) (X.presheaf.stalk x)),
      Ideal.span (Set.range y) = IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
      (∀ i j : Fin h, D i (y j) = if i = j then 1 else 0) ∧
      (∀ i j : Fin h, ∀ a : X.presheaf.stalk x, D i (D j a) = D j (D i a)) := by
  let _ := stalkAlgebra k p x
  obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p x
  let _ := sectionsAlgebra k p U
  let _ := c.algebra
  let _ : DecidableEq (ULift.{u} (Fin m)) := Classical.decEq _
  have := c.algebra_formallyEtale hU
  have := c.isScalarTower
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  have : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) :=
    isScalarTower_stalk k p U x hxU (algebraMap_sectionsAlgebra k p U)
      (algebraMap_stalkAlgebra k p x) rfl
  have : IsLocalization ((hU.primeIdealOf ⟨x, hxU⟩).asIdeal).primeCompl
      (X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hxU⟩
  have := isNoetherianRing_stalk k p x
  let _ : Algebra k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    ((IsLocalRing.residue (X.presheaf.stalk x)).comp (stalkAlgebraMap k p x)).toAlgebra
  have : IsScalarTower k (X.presheaf.stalk x)
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsLocalRing.ResidueField.algebraMap_eq]
      rfl
  have := formallySmooth_residueField k p x rfl
  exact exists_regularParameters_of_formallyEtale k (ULift.{u} (Fin m)) Γ(X, U)
    ((hU.primeIdealOf ⟨x, hxU⟩).asIdeal) (X.presheaf.stalk x)

theorem orderAt_mul (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (I J : X.IdealSheafData) (x : X) :
    orderAt (I * J) x = orderAt I x + orderAt J x := by
  let _ := stalkAlgebra k p x
  have := isNoetherianRing_stalk k p x
  obtain ⟨h, y, D, hspan, hD, hDD⟩ := exists_regularParameters_stalk_of_smooth k p x
  simp only [orderAt_eq_idealOrder, stalkIdeal_mul]
  exact idealOrder_mul y D hspan hD hDD (fun n hn => isUnit_natCast_stalk k p x hn)
    (stalkIdeal I x) (stalkIdeal J x)

theorem orderAt_pow (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (I : X.IdealSheafData) (c : ℕ) (x : X) :
    orderAt (I ^ c) x = (c : ℕ∞) * orderAt I x := by
  let _ := stalkAlgebra k p x
  have := isNoetherianRing_stalk k p x
  obtain ⟨h, y, D, hspan, hD, hDD⟩ := exists_regularParameters_stalk_of_smooth k p x
  simp only [orderAt_eq_idealOrder, stalkIdeal_pow]
  exact idealOrder_pow y D hspan hD hDD (fun n hn => isUnit_natCast_stalk k p x hn)
    (stalkIdeal I x) c

theorem natCast_mul_le_mul_iff {c : ℕ} (hc : 1 ≤ c) (m : ℕ) (a : ℕ∞) :
    (c : ℕ∞) * (m : ℕ∞) ≤ (c : ℕ∞) * a ↔ (m : ℕ∞) ≤ a := by
  induction a using ENat.recTopCoe with
  | top =>
    have hc0 : (c : ℕ∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have htop : (c : ℕ∞) * ⊤ = ⊤ := by simp [hc0]
    simp [htop]
  | coe n =>
    constructor
    · intro hle
      have h' : c * m ≤ c * n := by exact_mod_cast hle
      have h'' : m ≤ n := Nat.le_of_mul_le_mul_left h' (by omega)
      exact_mod_cast h''
    · intro hle
      have h' : m ≤ n := by exact_mod_cast hle
      have h'' : c * m ≤ c * n := Nat.mul_le_mul (le_refl c) h'
      exact_mod_cast h''

theorem orderAtLeastLocus_pow_mul (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (I : X.IdealSheafData) {c : ℕ} (hc : 1 ≤ c) (m : ℕ) :
    orderAtLeastLocus (I ^ c) (c * m) = orderAtLeastLocus I m := by
  ext x
  rw [mem_orderAtLeastLocus_iff, mem_orderAtLeastLocus_iff, orderAt_pow k p I c x, Nat.cast_mul]
  exact natCast_mul_le_mul_iff hc m (orderAt I x)

end FunctorialResolution.EmbeddedResolution

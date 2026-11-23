import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.BlowupDerivativeIdealBound
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private theorem le_natCast_iff_not_succ_le (a : ℕ∞) (m : ℕ) :
    a ≤ (m : ℕ∞) ↔ ¬ ((m + 1 : ℕ) : ℕ∞) ≤ a := by
  induction a using ENat.recTopCoe with
  | top =>
      refine iff_of_false ?_ ?_
      · intro h
        have h1 : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := le_trans le_top h
        have h2 : m + 1 ≤ m := by exact_mod_cast h1
        omega
      · exact fun h => h le_top
  | coe n =>
      constructor
      · intro h h'
        have h1 : n ≤ m := by exact_mod_cast h
        have h2 : m + 1 ≤ n := by exact_mod_cast h'
        omega
      · intro h
        have h2 : n ≤ m := by
          by_contra hc
          exact h (by exact_mod_cast (by omega : m + 1 ≤ n))
        exact_mod_cast h2

theorem orderAt_le_iff_notMem_orderAtLeastLocus {X : Scheme.{u}} (I : X.IdealSheafData) (m : ℕ)
    (x : X) :
    orderAt I x ≤ (m : ℕ∞) ↔ x ∉ orderAtLeastLocus I (m + 1) := by
  rw [mem_orderAtLeastLocus_iff]
  exact le_natCast_iff_not_succ_le (orderAt I x) m

theorem notMem_support_derivIdealSheafIterate_iff_orderAt_le (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (I : X.IdealSheafData) (m : ℕ) (x : X) :
    x ∉ (derivIdealSheafIterate k p m I).support ↔ orderAt I x ≤ (m : ℕ∞) := by
  have h0 := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I (m := m + 1) (hm := by omega)
  rw [Nat.add_sub_cancel] at h0
  have hiff : x ∈ (derivIdealSheafIterate k p m I).support ↔ x ∈ orderAtLeastLocus I (m + 1) := by
    rw [← SetLike.mem_coe, h0]
  rw [orderAt_le_iff_notMem_orderAtLeastLocus, hiff]

theorem stalkIdeal_derivIdealSheafIterate_eq_top_iff_orderAt_le (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (I : X.IdealSheafData) (m : ℕ) (x : X) :
    stalkIdeal (derivIdealSheafIterate k p m I) x = ⊤ ↔ orderAt I x ≤ (m : ℕ∞) := by
  rw [← notMem_support_derivIdealSheafIterate_iff_orderAt_le k p I m x,
    mem_support_iff_stalkIdeal_ne_top]
  simp

theorem orderAt_controlledTransform_le (k : Type u) [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [IsLocallyNoetherian X₁] (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (I : X.IdealSheafData) (m : ℕ)
    (hI : I ≤ Z ^ m) (z : X) (hz : orderAt I z ≤ (m : ℕ∞)) (x₁ : X₁)
    (hx₁ : π.base x₁ = z) :
    orderAt (controlledTransform π Z I m hπ hI) x₁ ≤ (m : ℕ∞) := by
  subst hx₁
  have hsm : AlgebraicGeometry.Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hZ hπ
  have h1 : stalkIdeal (derivIdealSheafIterate k p m I) (π.base x₁) = ⊤ :=
    (stalkIdeal_derivIdealSheafIterate_eq_top_iff_orderAt_le k p I m (π.base x₁)).2 hz
  have h2 : (derivIdealSheafIterate k p m I).comap π ≤
      Blowup.exceptionalIdeal π Z ^ (m - m) *
        derivIdealSheafIterate k (π ≫ p) m (controlledTransform π Z I m hπ hI) :=
    comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p π Z E hZ hπ I m hI m le_rfl
  rw [Nat.sub_self, pow_zero, one_mul] at h2
  have h3 : stalkIdeal ((derivIdealSheafIterate k p m I).comap π) x₁ = ⊤ := by
    rw [stalkIdeal_comap, h1, Ideal.map_top]
  have h4 := stalkIdeal_mono h2 x₁
  rw [h3, top_le_iff] at h4
  exact (stalkIdeal_derivIdealSheafIterate_eq_top_iff_orderAt_le k (π ≫ p)
    (controlledTransform π Z I m hπ hI) m x₁).1 h4

theorem orderAt_controlledTransform_le_of_orderAt_image_le (k : Type u) [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [IsLocallyNoetherian X₁] (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (I : X.IdealSheafData) (m : ℕ)
    (hI : I ≤ Z ^ m) (x₁ : X₁) (hx₁ : orderAt I (π.base x₁) ≤ (m : ℕ∞)) :
    orderAt (controlledTransform π Z I m hπ hI) x₁ ≤ (m : ℕ∞) :=
  orderAt_controlledTransform_le k p π Z E hZ hπ I m hI (π.base x₁) hx₁ x₁ rfl

theorem orderAt_controlledTransform_le_of_not_succ_le (k : Type u) [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [IsLocallyNoetherian X₁] (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (I : X.IdealSheafData) (m : ℕ)
    (hI : I ≤ Z ^ m) (z : X) (hz : ¬ (((m + 1 : ℕ) : ℕ∞) ≤ orderAt I z)) (x₁ : X₁)
    (hx₁ : π.base x₁ = z) :
    orderAt (controlledTransform π Z I m hπ hI) x₁ ≤ (m : ℕ∞) :=
  orderAt_controlledTransform_le k p π Z E hZ hπ I m hI z
    ((orderAt_le_iff_notMem_orderAtLeastLocus I m z).2 hz) x₁ hx₁

theorem orderAt_controlledTransform_le_of_forall_le (k : Type u) [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [IsLocallyNoetherian X₁] (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (I : X.IdealSheafData) (m : ℕ)
    (hI : I ≤ Z ^ m) (h : ∀ x : X, orderAt I x ≤ (m : ℕ∞)) (x₁ : X₁) :
    orderAt (controlledTransform π Z I m hπ hI) x₁ ≤ (m : ℕ∞) :=
  orderAt_controlledTransform_le k p π Z E hZ hπ I m hI (π.base x₁) (h (π.base x₁)) x₁ rfl

theorem orderAtLeastLocus_controlledTransform_subset_preimage (k : Type u) [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [IsLocallyNoetherian X₁] (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (I : X.IdealSheafData) (m : ℕ)
    (hI : I ≤ Z ^ m) :
    orderAtLeastLocus (controlledTransform π Z I m hπ hI) (m + 1) ⊆
      ⇑π.base ⁻¹' orderAtLeastLocus I (m + 1) := by
  intro x₁ hx₁
  by_contra hz
  rw [Set.mem_preimage, mem_orderAtLeastLocus_iff] at hz
  have h := orderAt_controlledTransform_le_of_not_succ_le k p π Z E hZ hπ I m hI
    (π.base x₁) hz x₁ rfl
  rw [mem_orderAtLeastLocus_iff] at hx₁
  have hle : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := le_trans hx₁ h
  have hcontra : m + 1 ≤ m := by exact_mod_cast hle
  omega

end FunctorialResolution.EmbeddedResolution

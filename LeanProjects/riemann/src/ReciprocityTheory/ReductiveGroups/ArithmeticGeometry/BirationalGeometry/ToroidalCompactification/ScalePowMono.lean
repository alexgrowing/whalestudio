import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DualMapSCompScaleS

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

section Maps

variable {S : Type} [CommRing S]

def awayHom (u : S) (B : Type) [CommRing B] [Algebra S B] (hu : IsUnit (algebraMap S B u)) :
    Localization.Away u →ₐ[S] B :=
  { IsLocalization.Away.lift u hu with commutes' := fun r => IsLocalization.Away.lift_eq u hu r }

def qHom (u v : S) (B : Type) [CommRing B] [Algebra S B] (hu : IsUnit (algebraMap S B u))
    (hv : IsUnit (algebraMap S B v)) : Qv u v →ₐ[S] B :=
  { IsLocalization.Away.lift (algebraMap S (Localization.Away u) v) (g := (awayHom u B hu).toRingHom)
      (by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]; exact hv) with
    commutes' := fun r => by
      show IsLocalization.Away.lift (algebraMap S (Localization.Away u) v) _
        (algebraMap (Localization.Away u) (Qv u v) (algebraMap S (Localization.Away u) r)) = algebraMap S B r
      rw [IsLocalization.Away.lift_eq]
      exact (awayHom u B hu).commutes r }

theorem away_unit (u : S) : IsUnit (algebraMap S (Localization.Away u) u) :=
  IsLocalization.Away.algebraMap_isUnit u

theorem unit_of_map {B B' : Type} [CommRing B] [Algebra S B] [CommRing B'] [Algebra S B'] [Algebra B B']
    [IsScalarTower S B B'] {u : S} (h : IsUnit (algebraMap S B u)) : IsUnit (algebraMap S B' u) := by
  rw [IsScalarTower.algebraMap_apply S B B']
  exact h.map _

end Maps

section Extend

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

theorem scale_pow_add {A : Type} [CommRing A] [Algebra S A] (x : A) (a b : ℕ) (y : sp (R₀ := S) (DualNumber A) ⟶ G) :
    spMap (scaleS (S := S) (x ^ a)) ≫ spMap (scaleS (x ^ b)) ≫ y = spMap (scaleS (x ^ (a + b))) ≫ y := by
  rw [scale_scale, pow_add]

theorem scale_pow_mono {A : Type} [CommRing A] [Algebra S A] (x : A) {m M : ℕ} (hm : m ≤ M)
    {y₁ y₂ : sp (R₀ := S) (DualNumber A) ⟶ G} (h : spMap (scaleS (S := S) (x ^ m)) ≫ y₁ = spMap (scaleS (x ^ m)) ≫ y₂) :
    spMap (scaleS (S := S) (x ^ M)) ≫ y₁ = spMap (scaleS (x ^ M)) ≫ y₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [add_comm m d, ← scale_pow_add x d m y₁, ← scale_pow_add x d m y₂, h]

variable [∀ s : S, Smooth (Gs G s).hom]

include G in
theorem fp_chart {s : S} (C : Chart (Gs G s)) : Algebra.FinitePresentation (Localization.Away s) Γ((Gs G s).left, C.U) := by
  haveI := chart_smooth (C := C)
  infer_instance

theorem tanS_away_lift {s : S} (C : Chart (Gs G s)) {A : Type} [CommRing A] [Algebra S A]
    [Algebra (Localization.Away s) A] [IsScalarTower S (Localization.Away s) A] (t : S)
    {y' : sp (R₀ := S) (DualNumber (Localization.Away (algebraMap S A t))) ⟶ G} (hy' : TanS y') :
    ∃ N : ℕ, ∃ y : sp (R₀ := S) (DualNumber A) ⟶ G, TanS y ∧
      spMap (dualMapS (IsScalarTower.toAlgHom S A (Localization.Away (algebraMap S A t)))) ≫ y =
        spMap (scaleS (S := S) (algebraMap S (Localization.Away (algebraMap S A t)) t ^ N)) ≫ y' := by
  haveI := fp_chart C
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A
      (Submonoid.powers (algebraMap S (Localization.Away s) t)))
      (Localization.Away (algebraMap S A t)) := by
    have e : Algebra.algebraMapSubmonoid A (Submonoid.powers (algebraMap S (Localization.Away s) t)) =
        Submonoid.powers (algebraMap S A t) := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, ← IsScalarTower.algebraMap_apply]
    rw [e]
    infer_instance
  obtain ⟨m, hm, y, hy, heq⟩ := tanS_lift C (A := A) (A' := Localization.Away (algebraMap S A t))
    (Submonoid.powers (algebraMap S (Localization.Away s) t)) hy'
  obtain ⟨N, rfl⟩ := hm
  refine ⟨N, y, hy, ?_⟩
  rw [heq, map_pow, ← IsScalarTower.algebraMap_apply]

theorem tanS_away_uniq {s : S} (C : Chart (Gs G s)) {A : Type} [CommRing A] [Algebra S A]
    [Algebra (Localization.Away s) A] [IsScalarTower S (Localization.Away s) A] (t : S)
    {y₁ y₂ : sp (R₀ := S) (DualNumber A) ⟶ G} (h₁ : TanS y₁) (h₂ : TanS y₂)
    (he : spMap (dualMapS (IsScalarTower.toAlgHom S A (Localization.Away (algebraMap S A t)))) ≫ y₁ =
      spMap (dualMapS (IsScalarTower.toAlgHom S A (Localization.Away (algebraMap S A t)))) ≫ y₂) :
    ∃ N : ℕ, spMap (scaleS (S := S) (algebraMap S A t ^ N)) ≫ y₁ = spMap (scaleS (algebraMap S A t ^ N)) ≫ y₂ := by
  haveI := fp_chart C
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A
      (Submonoid.powers (algebraMap S (Localization.Away s) t)))
      (Localization.Away (algebraMap S A t)) := by
    have e : Algebra.algebraMapSubmonoid A (Submonoid.powers (algebraMap S (Localization.Away s) t)) =
        Submonoid.powers (algebraMap S A t) := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, ← IsScalarTower.algebraMap_apply]
    rw [e]
    infer_instance
  obtain ⟨m, hm, heq⟩ := tanS_uniq C (A := A) (A' := Localization.Away (algebraMap S A t))
    (Submonoid.powers (algebraMap S (Localization.Away s) t)) h₁ h₂ he
  obtain ⟨N, rfl⟩ := hm
  refine ⟨N, ?_⟩
  rw [map_pow, ← IsScalarTower.algebraMap_apply] at heq
  exact heq

end Extend

end ReciprocityTheory.ChartRestriction.G.Chart

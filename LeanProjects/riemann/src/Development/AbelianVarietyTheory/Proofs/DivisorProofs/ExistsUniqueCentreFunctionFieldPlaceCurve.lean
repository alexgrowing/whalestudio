import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem existsUnique_centre : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ p : Place k E, ∃! b : Sp p.O ⟶ C, spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x := by
  intro k K E _ _ _ _ _ _ _ _ _ _ C _ x hx p
  obtain ⟨⟨-, hproj, -⟩, -, hxs⟩ := hx
  have hprop : IsProper (strHom k C) := (isProper_and_exists_isAmpleLB_of_isProjOver hproj).1
  have hk : ∀ c : k, algebraMap k E c ∈ p.O := by
    intro c
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · rw [p.2.2 c hc]
  let ik : k →+* p.O := (algebraMap k E).codRestrict p.O hk
  have hik : p.O.subtype.comp ik = algebraMap k E := RingHom.ext fun _ => rfl
  have hsq : (spMap (algebraMap K E) ≫ x) ≫ strHom k C = spMap (algebraMap p.O E) ≫ spMap ik := by
    rw [Category.assoc, hxs, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
    rfl
  have hv : ValuativeCriterion (strHom k C) := by
    rw [IsProper.eq_valuativeCriterion] at hprop
    exact hprop.1.1.1
  let S : ValuativeCommSq (strHom k C) :=
    { R := p.O, K := E, i₁ := spMap (algebraMap K E) ≫ x, i₂ := spMap ik, commSq := ⟨hsq⟩ }
  obtain ⟨U⟩ := hv S

  have hover : ∀ b : Sp p.O ⟶ C, spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x → b ≫ strHom k C = spMap ik := by
    intro b hb
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (b ≫ strHom k C)
    have e : Spec.map (φ ≫ CommRingCat.ofHom p.O.subtype) = Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
      rw [Spec.map_comp, hφ, ← Category.assoc, hb, Category.assoc, hxs, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq]
    have e2 := Spec.map_injective e
    rw [← hφ]
    congr 1
    ext c
    exact congrArg (fun f => (CommRingCat.Hom.hom f) c) e2
  refine ⟨U.default.l, U.default.fac_left, fun b hb => ?_⟩
  let L : S.commSq.LiftStruct := { l := b, fac_left := hb, fac_right := hover b hb }
  exact congrArg CommSq.LiftStruct.l (U.uniq L)

end GlobalTheory.Nef

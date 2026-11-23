import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.CLiftEx

theorem thick_isNilpotent {b : Base} {L : b.Fun} (T : Thick L) (x : T.B) (hx : x ∈ T.J) :
    IsNilpotent x := by
  by_cases hp : b.p = 0
  · obtain ⟨k, hk⟩ := T.adm.2 hp
    refine ⟨k, ?_⟩
    simpa [hk] using Ideal.pow_mem_pow hx k
  · obtain ⟨k, hk⟩ := T.adm.1 hp
    refine ⟨b.p * k, ?_⟩
    have hfac : ((b.p.factorial : ℕ) : T.B) = (b.p : T.B) * ((b.p - 1).factorial : T.B) := by
      rw [← Nat.cast_mul, Nat.mul_factorial_pred hp]
    rw [pow_mul, ← T.δ.factorial_mul_dpow_eq_pow hx, hfac, mul_assoc, mul_pow, hk, zero_mul]

theorem unit_lift {B : Type} [CommRing B] (J : Ideal B) (hJ : ∀ x ∈ J, IsNilpotent x) (u : (B ⧸ J)ˣ) :
    ∃ w : Bˣ, Ideal.Quotient.mk J (w : B) = (u : B ⧸ J) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : B ⧸ J)
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (B ⧸ J)ˣ) : B ⧸ J)
  have hmem : a * c - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ha, hc, Units.mul_inv, map_one, sub_self]
  have hunit : IsUnit (a * c) := by
    have h1 := (hJ _ hmem).isUnit_one_add
    have h2 : (1 : B) + (a * c - 1) = a * c := by ring
    rwa [h2] at h1
  obtain ⟨w, hw⟩ := isUnit_of_mul_isUnit_left hunit
  exact ⟨w, by rw [hw, ha]⟩

theorem nonempty_cLift : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
    {κ : O →+* b.R ⧸ b.I} {C : Type 1} [Category.{0} C] (G : C ⥤ Thick ((B.schFn q).cr b ht κ)) (D : E.LineData X),
    (∀ T, ∃ p : Spec (CommRingCat.of ((G.obj T).B ⧸ (G.obj T).J)) ⟶ D.Y, p ≫ D.f = B.thPt (G.obj T)) → Nonempty (B.CLift G D) := by
  intro O _ X q b ht κ C _ G D h
  classical
  choose p hp using h
  refine ⟨⟨p, hp, fun {T T'} φ =>
    if h : (B.thSp (G.map φ) ≫ p T) ≫ D.f = p T' ≫ D.f then
      (unit_lift (G.obj T').J (fun x hx => thick_isNilpotent (G.obj T') x hx)
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of ((G.obj T').B ⧸ (G.obj T').J))).hom.hom.toMonoidHom
          (D.u (B.thSp (G.map φ) ≫ p T) (p T') h))).choose
    else 1, fun {T T'} φ h => ?_⟩⟩
  rw [dif_pos h]
  exact (unit_lift (G.obj T').J (fun x hx => thick_isNilpotent (G.obj T') x hx)
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of ((G.obj T').B ⧸ (G.obj T').J))).hom.hom.toMonoidHom
      (D.u (B.thSp (G.map φ) ≫ p T) (p T') h))).choose_spec

end GlobalTheory.CompanionTheory.CLiftEx

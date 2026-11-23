import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.FromTestIffOfValAtCx

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FrameLift
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ClassSumCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem exists_frUnder {S : Type} [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S]
    (hc : ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a) (y₂ : FrPt d.Xo₂ d.c₂ S)
    (hx : (y₂.x ≫ d.r) ≫ Xo.s = sOf c S) : ∃ y : FrPt Xo c S, FrOver d y₂ y := by
  have hc' : ∀ τ a, algebraMap d.c₂.F S (embK d.c₂ τ a) = algebraMap c.F S (embK c τ a) := fun τ a => by
    rw [← embK_eF, hc]
  have e : y₂.x ≫ d.r = y₂.x ≫ d.r := rfl
  obtain ⟨w, hw, hw', -⟩ := d.m.lin
  obtain ⟨p, k, p₁, p₂, hk, hk'⟩ := exists_pm_iso d.m e
  have hL := Xo.univ.t.PP.isLB
  have hL₂ := d.Xo₂.univ.t.PP.isLB
  obtain ⟨s, hs⟩ := exists_up hL hL₂ hw p₁ hk hk' y₂.s
  refine ⟨⟨y₂.x ≫ d.r, hx, fun τ i => y₂.u τ i ≫ d.m.φ, fun τ i => (tan_iff d.m e (y₂.tan τ i).1).1 (y₂.tan τ i),
    fun τ i => (eig_iff d.m τ (hc' τ) (y₂.tan τ i).1).1 (y₂.eig τ i), fun τ v hv hv' => ?_, s, fun s' => ?_⟩,
    (frOver_iff d _ _).2 ⟨e, fun _ _ => rfl, w, p, ⟨hw, hw'⟩, p₁, p₂, hs⟩⟩
  · obtain ⟨v₂, rfl, h₂⟩ := exists_lift d.m e hv.1
    refine (existsUnique_congr fun a => ?_).1
      (y₂.basis τ v₂ ((tan_iff d.m e h₂).2 hv) ((eig_iff d.m τ (hc' τ) h₂).2 hv'))
    exact comb_iff d.m e (fun i => (y₂.tan τ i).1) a h₂
  · obtain ⟨s₂', hs'⟩ := exists_down hL hL₂ hw p₁ s'
    refine (existsUnique_congr fun a => ?_).1 (y₂.gen s₂')
    exact (scal_iff (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left (toΓ S a) y₂.s s₂').trans
      ((rel_scal_iff hL hL₂ p₁ hk p₂ (toΓ S a) hs hs').trans
        (scal_iff (fst (Over.mk (y₂.x ≫ d.r)) Xo.univ.t.G).left (toΓ S a) s s').symm)

theorem rel_unique {A A₂ Y Y₂ : Scheme.{0}} {L : LB A} {L₂ : LB A₂} {φ : A₂ ⟶ A} (hL₂ : L₂.IsLB)
    {w : LB.Iso L₂ (L.pull φ)} {q₂ : Y₂ ⟶ A₂} {q : Y ⟶ A} {p : Y₂ ⟶ Y} (hp : p ≫ q = q₂ ≫ φ) {k : Y ⟶ Y₂}
    (hk : k ≫ p = 𝟙 _) {s₂ : LB.Sec (LOne L₂ q₂)} {s s' : LB.Sec (LOne L q)} (H : Rel w p s₂ s)
    (H' : Rel w p s₂ s') : s = s' := by
  have : s.f = s'.f := funext fun i => by
    obtain ⟨i, rfl⟩ := exists_const i
    refine fn_ext fun z hz => ?_
    obtain ⟨j, hj⟩ := exists_chart hL₂ (q₂ (k z))
    have hi' : φ (q₂ (k z)) ∈ L.U i :=
      (congrArg (· ∈ L.U i) (pt_eq hp (k z))).mp ((congrArg (fun t => q t ∈ L.U i) (pt_eq hk z)).mpr (mem_ch.1 hz))
    have a := (H Y k z i j hi' hj).trans (H' Y k z i j hi' hj).symm
    rw [hk] at a
    exact a
  cases s; cases s'
  congr

theorem frUnder_unique {S : Type} [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S] {y₂ : FrPt d.Xo₂ d.c₂ S}
    {y z : FrPt Xo c S} (h : FrOver d y₂ y) (h' : FrOver d y₂ z) : y = z := by
  obtain ⟨e, hu, w, p, hw, p₁, p₂, H⟩ := (frOver_iff d _ _).1 h
  obtain ⟨e', hu', w', p', hw', p₁', p₂', H'⟩ := (frOver_iff d _ _).1 h'
  obtain rfl : w = w' := rigidified_iso_unique GlobalTheory.abelianSchemeLaws_all.1.globalFns (UnivPol.pol d.Xo₂)
    Xo.univ.t.PP.isLB d.m.φ w w' hw.1 hw'.1 _ _ hw.2 hw'.2
  obtain ⟨x, xo, u, t, ei, b, s, g⟩ := y
  obtain ⟨x', xo', u', t', ei', b', s', g'⟩ := z
  dsimp only at e e' hu hu' p p' p₁ p₂ p₁' p₂' H H'
  obtain rfl : x = x' := e.symm.trans e'
  obtain rfl : u = u' := funext fun τ => funext fun i => (hu τ i).symm.trans (hu' τ i)
  obtain rfl : p = p' := pm_ext (p₁.trans p₁'.symm) (p₂.trans p₂'.symm)
  obtain ⟨q, k, q₁, q₂, hk, -⟩ := exists_pm_iso d.m e
  obtain rfl : p = q := pm_ext (p₁.trans q₁.symm) (p₂.trans q₂.symm)
  obtain rfl : s = s' := rel_unique d.Xo₂.univ.t.PP.isLB p₁ hk H H'
  rfl

end GlobalTheory.ClassSumCompare

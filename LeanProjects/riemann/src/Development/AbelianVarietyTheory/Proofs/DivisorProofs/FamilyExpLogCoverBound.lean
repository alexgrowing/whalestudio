import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsStableFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFiniteFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaEquivariantFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalModuleActionLaws
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open GlobalTheory.TanPtMod

namespace GlobalTheory.UPel.HT.ES.WTors

theorem killedBy_iff_map {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) {T : Over S} (x : T ⟶ o.A) :
    GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x ↔ KilledBy o w x := by
  constructor
  · intro h a ha
    exact h _ (Ideal.mem_map_of_mem _ ha)
  · intro h a ha
    simp only [GlobalTheory.IwLevel.htAct_act]
    refine Submodule.span_induction (p := fun y _ => x ≫ o.act.act y = 1) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨c, hc, rfl⟩
      exact h c hc
    · have h0 : o.act.act 0 = 1 := by
        have := o.act.add 0 0
        rw [add_zero] at this
        exact mul_left_cancel (this.symm.trans (_root_.mul_one _).symm)
      rw [h0, comp_one]
    · intro y z _ _ hy hz
      rw [o.act.add, comp_mul, hy, hz, _root_.mul_one]
    · intro c y _ hy
      haveI := o.act.hom c
      rw [smul_eq_mul, o.act.mul, ← Category.assoc, hy, one_comp]

end GlobalTheory.UPel.HT.ES.WTors

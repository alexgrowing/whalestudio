import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumProjSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTCount

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R] {b : GlobalTheory.UPel.HT.Base D R}
  {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R}

def crysAct (o₀ : GlobalTheory.UPel.HT.Obj b N t) : D.O →+* Module.End k (HdR o₀.A) :=
  RingHom.mk'
    { toFun x := haveI := o₀.act.hom x; push (dp0 k) (𝟙 _) (o₀.act.act x)
      map_one' := by
        haveI := o₀.act.hom 1
        exact (push_congr (dp0 k) (𝟙 _) o₀.act.one).trans (push_id (dp0 k) (𝟙 _))
      map_mul' x y := by
        haveI := o₀.act.hom
        exact (push_congr (dp0 k) (𝟙 _) (o₀.act.mul x y)).trans (push_comp (dp0 k) (𝟙 _) _ _) }
    fun x y ↦ by
      haveI := o₀.act.hom
      haveI : IsMonHom (o₀.act.act x * o₀.act.act y) := o₀.act.add x y ▸ o₀.act.hom _
      exact (push_congr (dp0 k) (𝟙 _) (o₀.act.add x y)).trans (push_mul (dp0 k) (𝟙 _) _ _)

theorem crysAct_apply (o₀ : GlobalTheory.UPel.HT.Obj b N t) (x : D.O) :
    crysAct o₀ x = (haveI := o₀.act.hom x; push (dp0 k) (𝟙 _) (o₀.act.act x)) := rfl

def rhoPart (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) : Submodule k (HdR o₀.A) :=
  LinearMap.range (crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : k) - β b.ρ) • 1)

def lieZ (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) : Submodule k (HdR o₀.A) :=
  Submodule.span k {z | ∃ (r : ℕ) (lam : Fin r → k) (c : Fin r → 𝓞 D.F) (y : HdR o₀.A), y ∈ rhoPart o₀ β ∧
    (∀ i, ∑ l, lam l * β (b.t i (c l)) = 0) ∧ z = ∑ l, lam l • crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) y}

end GlobalTheory.HTCount

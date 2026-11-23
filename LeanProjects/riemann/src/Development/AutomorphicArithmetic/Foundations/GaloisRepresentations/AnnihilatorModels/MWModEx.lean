import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermSystemHeightFree

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private def killedSub {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) (T : Over S) :
    letI := ptModuleWvs o T
    Submodule (𝓞 D.F) (Additive (T ⟶ o.A)) :=
  letI := ptModuleWvs o T
  { carrier := {g | KilledBy o w g.toMul}
    zero_mem' := KilledBy.one o w T
    add_mem' := fun {g h} hg hh a ha => by
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
      show (g.toMul * h.toMul) ≫ _ = 1
      rw [mul_comp, hg a ha, hh a ha, _root_.mul_one]
    smul_mem' := fun c g hg a ha => by
      show (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
      rw [Category.assoc, ← o.act.mul, ← map_mul, mul_comm, map_mul, o.act.mul, ← Category.assoc, hg a ha,
        one_comp] }

theorem UpperTheory.Gal.crystallineComparison.Mod.wModEx_of :
    WModEx := by
  intro p _ D R _ b N S s o w T
  letI := ptModuleWvs o T
  have htor : Module.IsTorsionBySet (𝓞 D.F) (killedSub o w T) (w : Set (𝓞 D.F)) := by
    intro x a
    apply Subtype.ext
    show (a : 𝓞 D.F) • (x : Additive (T ⟶ o.A)) = Additive.ofMul 1
    exact x.2 a a.2
  letI : Module (𝓞 D.F ⧸ w) (killedSub o w T) := htor.module
  refine ⟨⟨killedSub o w T, fun x => Additive.toMul (x : Additive (T ⟶ o.A)), ?_, ?_, ?_, ?_⟩⟩
  · intro x y h
    exact Subtype.ext (Additive.toMul.injective h)
  · intro g
    constructor
    · rintro ⟨h, rfl⟩
      exact h.2
    · intro hg
      exact ⟨⟨Additive.ofMul g, hg⟩, rfl⟩
  · intro x y
    rfl
  · intro a x
    rw [Module.IsTorsionBySet.mk_smul]
    rfl

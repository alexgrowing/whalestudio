import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

private theorem exists_isDiffOf_of_isMonHom {S : AlgebraicGeometry.Scheme} {R : Type} [CommRing R] {G : CategoryTheory.Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) (f : G ⟶ G) (hf : IsMonHom f) :
    ∃ A : E →ₗ[R] E, M.IsDiffOf f A := by
  have htan : ∀ e : E, IsTanAt G x (M.pt e ≫ f) := by
    intro e
    have h := M.tan e
    unfold IsTanAt at h ⊢
    rw [CategoryTheory.Over.comp_left, ← Category.assoc, h, ← CategoryTheory.Over.comp_left, MonObj.one_comp]
  choose g hg using fun e => M.onto _ (htan e)
  refine ⟨{ toFun := g, map_add' := ?_, map_smul' := ?_ }, fun e => hg e⟩
  · intro e e'
    apply M.inj
    rw [hg, M.add, M.add, hg, hg, MonObj.mul_comp]
  · intro c e
    simp only [RingHom.id_apply]
    apply M.inj
    apply CategoryTheory.Over.OverMorphism.ext
    rw [hg, CategoryTheory.Over.comp_left, M.smul, M.smul, hg, CategoryTheory.Over.comp_left, Category.assoc]

private theorem isDiffOf_unique {S : AlgebraicGeometry.Scheme} {R : Type} [CommRing R] {G : CategoryTheory.Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) {f : G ⟶ G} {A B : E →ₗ[R] E}
    (hA : M.IsDiffOf f A) (hB : M.IsDiffOf f B) : A = B := by
  ext e
  exact M.inj ((hA e).trans (hB e).symm)

theorem exists_lieModel_act_gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (T : CDVR) (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), ∃ (EC : Type) (_ : AddCommGroup EC) (_ : Module T.Fr EC) (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or T zV
  obtain ⟨EC, i1, i2, ⟨MC⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ Or.𝔐.t.G T.Fr (FinRd.Roots.gen T zV)
  choose D hD using fun o : 𝓞 E => exists_isDiffOf_of_isMonHom MC (Or.𝔐.t.act.act o) (Or.𝔐.t.act.hom o)
  have hD' : ∀ (o : 𝓞 E) (e : EC), MC.pt (D o e) = MC.pt e ≫ Or.𝔐.t.act.act o := fun o e => hD o e
  refine ⟨EC, i1, i2, MC, RingHom.mk' ⟨⟨D, ?_⟩, ?_⟩ ?_, fun o => hD o⟩
  · show D 1 = 1
    apply isDiffOf_unique MC (hD 1)
    intro e
    rw [Or.𝔐.t.act.one, Module.End.one_apply, Category.comp_id]
  · intro o o'
    show D (o * o') = D o * D o'
    apply isDiffOf_unique MC (hD (o * o'))
    intro e
    rw [Module.End.mul_apply, hD', hD', mul_comm, Or.𝔐.t.act.mul, Category.assoc]
  · intro o o'
    show D (o + o') = D o + D o'
    apply isDiffOf_unique MC (hD (o + o'))
    intro e
    rw [LinearMap.add_apply, MC.add, hD', hD', Or.𝔐.t.act.add, MonObj.comp_mul]

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

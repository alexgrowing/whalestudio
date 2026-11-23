import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def powSuccIso {S : Scheme.{0}} (A : Over S) (k : ℕ) :
    GlobalTheory.KS.pow A (k + 1) ≅ A ⨯ GlobalTheory.KS.pow A k :=
  let f : GlobalTheory.KS.pow A (k + 1) ⟶ A := Pi.π _ 0
  let g : GlobalTheory.KS.pow A (k + 1) ⟶ GlobalTheory.KS.pow A k :=
    Pi.lift fun i : Fin k => Pi.π (fun _ : Fin (k + 1) => A) i.succ
  have hf : Limits.prod.lift f g ≫ Limits.prod.fst = f := Limits.prod.lift_fst f g
  have hg : Limits.prod.lift f g ≫ Limits.prod.snd = g := Limits.prod.lift_snd f g
  have hgi (i : Fin k) : g ≫ Pi.π (fun _ : Fin k => A) i = Pi.π (fun _ : Fin (k + 1) => A) i.succ :=
    Pi.lift_π _ _
  let b : A ⨯ GlobalTheory.KS.pow A k ⟶ GlobalTheory.KS.pow A (k + 1) :=
    Pi.lift (Fin.cases Limits.prod.fst (fun i => Limits.prod.snd ≫ Pi.π _ i))
  have hb0 : b ≫ Pi.π (fun _ : Fin (k + 1) => A) 0 = Limits.prod.fst := Pi.lift_π _ _
  have hbs (i : Fin k) : b ≫ Pi.π (fun _ : Fin (k + 1) => A) i.succ =
      Limits.prod.snd ≫ Pi.π (fun _ : Fin k => A) i := Pi.lift_π _ _
  { hom := Limits.prod.lift f g
    inv := b
    hom_inv_id := by
      apply Pi.hom_ext
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [Category.assoc, hb0, hf, Category.id_comp]
      · rw [Category.assoc, hbs, ← Category.assoc, hg, hgi, Category.id_comp]
    inv_hom_id := by
      apply Limits.prod.hom_ext
      · rw [Category.assoc, hf, Category.id_comp]
        exact hb0
      · rw [Category.assoc, hg, Category.id_comp]
        apply Pi.hom_ext
        intro i
        rw [Category.assoc, hgi, hbs] }

private theorem flat_pow {S : Scheme.{0}} (A : Over S) (h : Flat A.hom) :
    ∀ k, Flat (GlobalTheory.KS.pow A k).hom
  | 0 => by
    have t : IsTerminal (GlobalTheory.KS.pow A 0) :=
      IsTerminal.ofUniqueHom (fun Y => Pi.lift (fun i => i.elim0))
        (fun Y m => Pi.hom_ext _ _ (fun i => i.elim0))
    let e := t.uniqueUpToIso Over.mkIdTerminal
    have h1 : (GlobalTheory.KS.pow A 0).hom = e.hom.left := by simpa using (Over.w e.hom).symm
    haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
    rw [h1]
    infer_instance
  | k + 1 => by
    haveI := flat_pow A h k
    let e := powSuccIso A k
    have h1 : (GlobalTheory.KS.pow A (k + 1)).hom = e.hom.left ≫ (Over.prodLeftIsoPullback A (GlobalTheory.KS.pow A k)).hom ≫
        pullback.fst A.hom (GlobalTheory.KS.pow A k).hom ≫ A.hom := by
      rw [← Category.assoc (Over.prodLeftIsoPullback A (GlobalTheory.KS.pow A k)).hom, Over.prodLeftIsoPullback_hom_fst]
      simp
    haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
    rw [h1]
    infer_instance

theorem UpperTheory.Gal.crystallineComparison.Mod.powExt_of :
    PowExt := by
  intro S A k
  refine ⟨fun h => flat_pow A inferInstance k, ?_⟩
  intro X u v h1 h2
  exact GlobalTheory.KS.PowPB.pow_left_hom_ext u v h1 h2

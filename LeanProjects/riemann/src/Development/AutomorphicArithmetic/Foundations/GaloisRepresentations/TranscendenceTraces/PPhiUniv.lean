import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped DirectSum Classical

namespace UpperTheory.Gal.TranscendenceTraces

private def famL {Q : ℕ} {Z S : Scheme.{0}} (p : Z ⟶ S) {G J : Shv (ZMod Q)} (t : Fam0 p G J)
    {U : Scheme.{0}} (u : U ⟶ S) : Sec G (pullback p u) →ₗ[ULift.{1} (ZMod Q)] Sec J U where
  toFun := t.app (Sq.of p u)
  map_add' := map_add _
  map_smul' c a := by
    obtain ⟨c⟩ := c
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective c
    have hc : (⟨(n : ZMod Q)⟩ : ULift.{1} (ZMod Q)) = ((n : ℤ) : ULift.{1} (ZMod Q)) :=
      ULift.ext _ _ (by simp)
    rw [hc, RingHom.id_apply, Int.cast_smul_eq_zsmul]
    exact (map_zsmul (t.app (Sq.of p u)) n a).trans (Int.cast_smul_eq_zsmul _ n _).symm

private def famS {Q : ℕ} {Z S : Scheme.{0}} (p : Z ⟶ S) {G J : Shv (ZMod Q)} (t : Fam0 p G J)
    (U : Scheme.{0}) : DS p G U →ₗ[ULift.{1} (ZMod Q)] Sec J U :=
  DirectSum.toModule _ _ _ fun u => famL p t u

private theorem famS_inc {Q : ℕ} {Z S : Scheme.{0}} (p : Z ⟶ S) {G J : Shv (ZMod Q)} (t : Fam0 p G J)
    {U : Scheme.{0}} (u : U ⟶ S) (a : Sec G (pullback p u)) :
    famS p t U (inc p G u a) = t.app (Sq.of p u) a :=
  DirectSum.toModule_lof _ _ _

private def famP {Q : ℕ} {Z S : Scheme.{0}} (p : Z ⟶ S) {G J : Shv (ZMod Q)} (t : Fam0 p G J) :
    phiP p G ⟶ J.obj where
  app U := ModuleCat.ofHom (famS p t U.unop)
  naturality U V g := ModuleCat.hom_ext (DS.hom_ext p fun u a => by
    change famS p t _ (DS.res p G g.unop (inc p G u a)) = Sec.res g.unop (famS p t _ (inc p G u a))
    rw [DS.res_inc p G g.unop u _ rfl, famS_inc, famS_inc]
    exact (t.nat (A := Sq.of p (g.unop ≫ u)) (B := Sq.of p u)
      ⟨g.unop, pbm p g.unop u _ rfl, rfl, pbm_fst .., pbm_snd ..⟩ a).symm)

theorem phiUniv_of : PhiUniv := by
  intro Q Z S p G J t
  obtain ⟨ψ, hψ, huniq⟩ := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift (ZMod Q) (phiP p G)).2.2 J (famP p t)
  have key : ∀ (U : Scheme) (y : DS p G U), Sec.map ψ (phiSec p G U y) = famS p t U y := by
    intro U y
    exact congrArg (fun φ => ModuleCat.Hom.hom (φ.app (op U)) y) hψ
  refine ⟨ψ, fun A a => ?_, fun m hm => huniq m ?_⟩
  · change Sec.map ψ (phiSec p G A.U (inc p G A.u (Sec.res A.cmp a))) = _
    rw [key, famS_inc]
    have hn : Sec.res (𝟙 A.U) (t.app A a) = t.app (Sq.of p A.u) (Sec.res A.cmp a) :=
      t.nat (A := Sq.of p A.u) (B := A)
        ⟨𝟙 _, A.cmp, Category.id_comp _, A.cmp_v, A.cmp_r.trans (Category.comp_id _).symm⟩ a
    rw [res_id] at hn
    exact hn.symm
  · apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply DS.hom_ext p
    intro u a
    change Sec.map m (phiSec p G U.unop (inc p G u a)) = famS p t U.unop (inc p G u a)
    rw [← phiE_of]
    exact (hm (Sq.of p u) a).trans (famS_inc p t u a).symm

end UpperTheory.Gal.TranscendenceTraces

end

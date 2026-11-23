import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointsSubsetAbLocus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalBundleOfSymmetricSemiAbelian
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TqOfGtCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationSpecialFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationRingActionAdjointCubeBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.PrimCube

open GlobalTheory.PrimNorm GlobalTheory.MulPull

theorem evenOn_of_prim : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (P : GlobalTheory.UU.CP G) (a : G ⟶ G), IsMonHom a → LBIso P.L.L (cubeLB G ![𝟙 G, a] P.L.L) → EvenOn P := by
  intro R _ _ _ hR D A G _ _ hS U P a ha hw
  have hp : IsProper (pullback.snd G.hom (jK R)) := by
    have := A.isAb.proper
    have e : pullback.snd G.hom (jK R) = U.gen.hom.left ≫ A.A.hom := (Over.w U.gen.hom).symm
    have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
    exact e ▸ MorphismProperty.comp_mem @IsProper U.gen.hom.left A.A.hom inferInstance A.isAb.proper
  have hB : IsAbelianScheme (thickObj R (maximalIdeal R) 0 D.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb
  let Q₀ := GlobalTheory.Mum.tqOfGtCoord (U.gt 0) hB
  obtain ⟨P₀, v, hv⟩ := GlobalTheory.UU.exists_isLevelCP (maximalIdeal R) 0 P
  have hm : (maximalIdeal R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI : Field (R ⧸ maximalIdeal R ^ (0 + 1)) := Ideal.Quotient.field _
  have hS0 := IsSemiAbelian.pullback (thick R (maximalIdeal R) 0) G hS
  have := hS0.smooth
  have := hS0.geomConnected
  have := Q₀.i_hom
  letI := D.toPre.addX
  haveI := D.toPre.freeX
  haveI := D.toPre.finX
  obtain ⟨s⟩ := GlobalTheory.BiextTriv.main (R ⧸ maximalIdeal R ^ (0 + 1)) D.toPre.X (thickObj R (maximalIdeal R) 0 G) P₀.L P₀.c Q₀.i
    Q₀.i_hom
  obtain ⟨σ, hσ⟩ := GlobalTheory.EvenTriv.exists_even_of_surjective (GlobalTheory.EvenTriv.surjective_cube_of_generic G hS hp) P a hw P₀
    (IsPullback.of_hasPullback G.hom (thick R (maximalIdeal R) 0)) hv Q₀.i s
  exact ⟨D.toPre.X, D.toPre.addX, D.toPre.freeX, D.toPre.finX, Q₀, P₀, ⟨v, hv⟩, σ, hσ⟩

theorem exists_cp_evenOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, w + star w = 1 → TraceFormTwistIso D.toPre o w → ∃ P : GlobalTheory.UU.CP G, LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) ∧ EvenOn P := by
  intro R _ _ _ hR D A G _ _ hS U O _ _ _ o oA oG hlin w hw _
  obtain ⟨hno, -, hic, -⟩ := hR.1
  have ha := oG.hom w
  have hb := oG.hom (star w)
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hgh := U.gen_hom
  have hp : IsProper (pullback.snd G.hom (jK R)) := by
    have := A.isAb.proper
    have e : pullback.snd G.hom (jK R) = U.gen.hom.left ≫ A.A.hom := (Over.w U.gen.hom).symm
    have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
    exact e ▸ MorphismProperty.comp_mem @IsProper U.gen.hom.left A.A.hom inferInstance A.isAb.proper
  have hM := U.LG.isLB
  have hT : ∃ t : LB.Gen (Theta G U.LG.L), t.IsGen := ⟨U.cubG.t, U.cubG.isGen⟩
  have hadd : oG.act w * oG.act (star w) = 𝟙 G := by
    have e := oG.map_add w (star w)
    rw [hw, oG.map_one] at e
    exact (e.trans rfl).symm
  have hadj := GlobalTheory.T.uniformisation_ringAction_adjoint_cubeBundle R hR.1 D A G hS U O o oA oG hlin w
  have hc := fun T : Over (Sp R) => diff₃_ptCls (T := T) hM hT
  have hq : ∀ T : Over (Sp R), (fun x : T ⟶ G => normCls U.LG.L (oG.act w) x.left) =
      fun x => diff₂ (ptCls U.LG.L T) x (postHom (oG.act w) T x) := fun T => funext fun x => normCls_left _ x
  have hs : ∀ (T : Over (Sp R)) (y : T ⟶ G), postHom (oG.act w) T y * postHom (oG.act (star w)) T y = y :=
    fun T y => (MonObj.comp_mul y _ _).symm.trans (by rw [hadd, Category.comp_id])
  have hadj' : ∀ (T : Over (Sp R)) (x y : T ⟶ G), diff₂ (ptCls U.LG.L T) (postHom (oG.act w) T x) y =
      diff₂ (ptCls U.LG.L T) x (postHom (oG.act (star w)) T y) := fun T x y => diff₂_ptCls_adj hM hadj x y
  have iso : ∀ (T : Over (Sp R)) (x y : T ⟶ G),
      LBIso (cubeLB G ![x, y] (cubeLB G ![𝟙 G, oG.act w] U.LG.L)) (cubeLB G ![x, y] U.LG.L) := fun T x y => by
    refine lbIso_nested hM _ _ _ _ _ _ ((prod_square_id x y (normCls U.LG.L (oG.act w))).trans
      (Eq.trans ?_ (prod_square_id x y (cls U.LG.L)).symm))
    rw [hq]
    exact diff₂_quadratic (hc T) _ _ (hs _) (hadj' _) x y
  have symN : HasGen (cubeLB G ![𝟙 G, oG.act w] U.LG.L) (K := Fin 2) ![(GrpObj.inv (X := G)).left, 𝟙 _] ![1, -1] := by
    refine hasGen_nested hM _ _ _ _ ?_
    rw [Fin.prod_univ_two]
    show normCls U.LG.L (oG.act w) (GrpObj.inv (X := G)).left ^ (1 : ℤ) *
      normCls U.LG.L (oG.act w) (𝟙 G : G ⟶ G).left ^ (-1 : ℤ) = 1
    have e : GrpObj.inv (X := G) = (𝟙 G)⁻¹ := by simp [Hom.inv_def]
    have e' : (𝟙 G)⁻¹ ≫ oG.act w = (𝟙 G ≫ oG.act w)⁻¹ := map_inv (postHom (oG.act w) G) _
    rw [normCls_left, normCls_left, e, e', diff₂_inv_inv (hc G), zpow_neg, mul_inv_cancel]
  have hN := GlobalTheory.LamCalc.cubeLB_isLB hM ![𝟙 G, oG.act w]
  obtain ⟨L', c', hL'⟩ := GlobalTheory.RigCube.exists_rigLB_cubicalStr R G hS hp _ hN
  have hsym : L'.IsSymmetric := isSymmetric_of_hasGen L' (hL' ▸ symN)
  obtain ⟨P, hP, -⟩ := GlobalTheory.UU.exists_cp_of_isSymmetric hL R A G hS U.gen hgh L' c' hsym
  have hPN : P.L.L = cubeLB G ![𝟙 G, oG.act w] U.LG.L := by rw [hP, hL']
  refine ⟨P, hPN ▸ GlobalTheory.PolBaseChange.lbIso_refl P.L.isLB, evenOn_of_prim R hR D A G hS U P (oG.act w) ha ?_⟩
  rw [hPN]
  exact (iso G (𝟙 G) (oG.act w)).symm

end GlobalTheory.Mum.PrimCube

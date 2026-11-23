import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsSymmetricOfSymmetryGenerator
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_pelUnif_of_unifPow : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (n : ℕ) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' t.G n) (U' : Unif (maximalIdeal V) D' A' G') (_PU : UnifPowOf3 pD pA pG U' P.U), letI := H.starRing; ∀ [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∃ (oA' : A'.OAct (𝓞 E)), (∀ (a : 𝓞 E) (i : Fin n), oA'.act a ≫ pA.pr i = pA.pr i ≫ P.oA.act a) ∧ ∃ (t' : SAB H (Sp V)) (P' : PELUnif (maximalIdeal V) t'), t'.G = G' ∧ HEq t'.grp (inferInstance : GrpObj G') ∧ HEq t'.comm (inferInstance : IsCommMonObj G') ∧ P'.D = D' ∧ HEq P'.mod (inferInstance : Module (𝓞 E) D'.toPre.X) ∧ HEq P'.oD oD' ∧ P'.A = A' ∧ HEq P'.oA oA' ∧ HEq P'.U U' := by
  intro _ _ _ _ V _ _ _ _ E _ _ _ H t P n D' A' G' _ _ pD pA pG U' Q
  letI := H.starRing
  intro md oD' hxi hoD
  have hx : ∀ (a : 𝓞 E) (x : D'.toPre.X), pD.xe (a • x) = a • pD.xe x := fun a x => funext fun i => hxi a x i
  obtain ⟨act', hact⟩ := (GlobalTheory.exists_powAct _ _ _ n pG).2 _ t.act
  have iso : LBIso U'.LG.L (boxLB t.PP.L pG.pr) := by
    rw [← P.bundle]; exact ⟨Q.wL, Q.wL_gen⟩
  let t' : SAB H (Sp V) :=
    { G := G'
      semi := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ n pG t.semi
      act := act'
      PP := U'.LG
      cub := U'.cubG
      sym := isSymmetric_of_symmetry_generator U'.LG U'.symG U'.symG_gen U'.symG_rig
      adj := fun a => GlobalTheory.PowAdj.lbIso_cube_pow _ _ _ n pG _ _ t.PP.isLB U'.LG.isLB iso _ _ _ _ (hact a) (hact (H.bar a)) (t.adj a)
      prim := GlobalTheory.PowPrimitive.lbIso_cube_pow _ _ _ n pG _ _ t.PP.isLB U'.LG.isLB iso _ _ (hact H.w0) t.prim }
  obtain ⟨rA, hrA⟩ := (GlobalTheory.exists_powAct _ _ _ n pA.toIsPowGrp).1 _ P.oA.toRingAct
  let oA' : A'.OAct (𝓞 E) :=
    { toRingAct := rA
      rosati := fun a => GlobalTheory.rosatiAdj_pow _ _ _ n pA.toIsPowGrp _ _ P.A.isLB A'.isLB ⟨pA.w, pA.w_gen⟩ _ _ _ _ (hrA a)
        (hrA (star a)) (P.oA.rosati a) }
  let P' : PELUnif (maximalIdeal V) t' :=
    { D := D'
      oD := oD'
      A := A'
      oA := oA'
      U := U'
      bundle := rfl
      lin := GlobalTheory.oLinear_of_unifPow V (maximalIdeal V) n _ _ _ _ _ _ pD pA pG U' P.U Q _ hx P.oD oD' P.oA oA'
        t.act.toRingAct act'.toRingAct hoD hrA hact P.lin
      w0 := GlobalTheory.PsiWZeroProd.main V n _ _ pD _ hx P.oD oD' hoD H.w0 P.w0 }
  exact ⟨oA', hrA, t', P', rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl⟩

end GlobalTheory

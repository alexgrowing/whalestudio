import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LbIsoLinCombPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtendsFromGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.PullbackSquarePartialSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.GenericDec

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison in

theorem gen_pull_div_of_gen_div {X Y : Scheme.{0}} (M N : LB X) (a : Y ⟶ X)
    (h : ∃ t : LB.Gen (LB.div (M.pull a) (N.pull a)), t.IsGen) :
    ∃ t : LB.Gen ((LB.div M N).pull a), t.IsGen := by
  refine exists_gen_transfer (L := LB.div (M.pull a) (N.pull a)) (L' := (LB.div M N).pull a)
    (fun p => ((fun _ => (p PUnit.unit).1), (fun _ => (p PUnit.unit).2))) (fun j y hy => ?_)
    (fun i j y hy => ?_) h
  · exact ⟨Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hy PUnit.unit).1,
      Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hy PUnit.unit).2⟩
  · have hM : a.base y ∈ M.U (i PUnit.unit).1 ⊓ M.U (j PUnit.unit).1 :=
      ⟨(Set.mem_iInter.1 hy.1 PUnit.unit).1, (Set.mem_iInter.1 hy.2 PUnit.unit).1⟩
    have hN : a.base y ∈ N.U (i PUnit.unit).2 ⊓ N.U (j PUnit.unit).2 :=
      ⟨(Set.mem_iInter.1 hy.1 PUnit.unit).2, (Set.mem_iInter.1 hy.2 PUnit.unit).2⟩
    refine (germ_pull (LB.div M N) a i j y hy ⟨⟨hM.1, hN.1⟩, ⟨hM.2, hN.2⟩⟩).trans ?_
    refine (gU_pullU a _ y _ _).trans ?_
    refine (congrArg _ (germ_div M N _ _ (a.base y) _)).trans ?_
    rw [map_mul, map_inv]
    refine Eq.trans ?_ (germ_div _ _ _ _ y _).symm
    exact congrArg₂ (· * ·) ((germ_pull M a (fun _ => (i PUnit.unit).1) (fun _ => (j PUnit.unit).1) y _ hM).trans (gU_pullU a _ y _ _)).symm
      (congrArg (·⁻¹) ((germ_pull N a (fun _ => (i PUnit.unit).2) (fun _ => (j PUnit.unit).2) y _ hN).trans (gU_pullU a _ y _ _)).symm)

theorem lbIso_of_generic {R' : Type} [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R']
    [IsLocalRing R'] (G : Over (Sp R')) [GrpObj G] (hG : IsSemiAbelian G) {P Q : LB G.left} (hP : P.IsLB)
    (hQ : Q.IsLB) (h : LBIso (P.pull (pullback.fst G.hom (jK R'))) (Q.pull (pullback.fst G.hom (jK R')))) :
    LBIso P Q :=
  PicGenericInj.exists_gen_of_generic R' G hG (LB.div Q P) (LB.isLB_div hQ hP)
    (gen_pull_div_of_gen_div Q P _ h)

theorem sqDec_of_generic : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R']
    [IsLocalRing R'] (G : Over (Sp R')) [GrpObj G], IsSemiAbelian G → ∀ (L M : LB G.left), L.IsLB → M.IsLB →
    SqDec ((Over.pullback (jK R')).obj G) (L.pull (pullback.fst G.hom (jK R')))
      (M.pull (pullback.fst G.hom (jK R'))) → SqDec G L M := by
  intro R' _ _ _ _ _ G _ hG L M hL hM hD
  obtain ⟨N, a₀, r, a, β, hN, ha₀, hβ, H⟩ := hD
  have ext : ∀ i, ∃ B : G ⟶ G, IsMonHom B ∧ (Over.pullback (jK R')).map B = β i := fun i =>
    (semiAbelian_hom_extend_generic R' G G hG hG (β i) (hβ i)).exists
  choose B hBm hBe using ext
  refine ⟨N, a₀, r, a, B, hN, ha₀, hBm, ?_⟩
  set f := pullback.fst G.hom (jK R') with hf
  have hc : ∀ o : Option (Fin r), (o.elim (𝟙 _) fun i => (β i).left) ≫ f =
      f ≫ (o.elim (𝟙 G.left) fun i => (B i).left) := by
    intro o
    cases o with
    | none => simp
    | some i =>
      simp only [Option.elim_some]
      rw [← hBe i]
      simp only [hf, Over.pullback_map_left]
      exact pullback.lift_fst _ _ _
  have i1 := (lbIso_lbPow_pull hL f N).symm
  have i5 := GlobalTheory.SymExtend.lbIso_linComb_pull hM f (fun o : Option (Fin r) => o.elim (𝟙 _) fun i => (β i).left)
    (fun o : Option (Fin r) => o.elim (𝟙 G.left) fun i => (B i).left) (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)) f hc
  have j1 := i1.trans (pull_isLB (isLB_lbPow hL N) f) (isLB_lbPow (pull_isLB hL f) N)
    (LB.isLB_linComb (pull_isLB hM f) _ _) H
  have j2 := j1.trans (pull_isLB (isLB_lbPow hL N) f) (LB.isLB_linComb (pull_isLB hM f) _ _)
    (pull_isLB (LB.isLB_linComb hM _ _) f) i5
  exact lbIso_of_generic G hG (isLB_lbPow hL N) (LB.isLB_linComb hM _ _) j2

end GlobalTheory.GenericDec

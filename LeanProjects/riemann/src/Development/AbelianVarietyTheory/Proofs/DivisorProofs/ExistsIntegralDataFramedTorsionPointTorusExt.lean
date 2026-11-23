import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConstMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HRedFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusPairOfTorsionPointOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTorsionPointLiftSectionTorusExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGeneratorRigidificationAllLevels
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAddInjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Sep.LiesData

theorem isPullF_gtExt {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F F' : Type} [Field F]
    [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
    {g' : GtPt D (𝟙_ (Over (Sp R)))} {g₁ : GtPtF D F} (H : GtPt.IsPullF F (toUnit (TF (R := R) F)).left g' g₁) :
    GtPt.IsPullF F' (toUnit (TF (R := R) F')).left g' (GlobalTheory.TorusExt.gtExt D f hf g₁) := by
  have e : GlobalTheory.TorusExt.extMap f hf ≫ toUnit (TF (R := R) F) = toUnit (TF (R := R) F') := comp_toUnit _
  refine (GlobalTheory.FieldRestrictionTest.isPullF_iff (toUnit (TF (R := R) F')) g' _).2 ⟨?_, fun χ y J hJ => ?_⟩
  · have b₁ : g₁.b = toUnit (TF (R := R) F) ≫ g'.b :=
      ((GlobalTheory.FieldRestrictionTest.isPullF_iff (toUnit (TF (R := R) F)) g' g₁).1 H).1
    exact (GlobalTheory.TorusExt.gtExt_b f hf g₁).trans ((congrArg (GlobalTheory.TorusExt.extMap f hf ≫ ·) b₁).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ g'.b) e)))
  · refine (GlobalTheory.TorusExt.gtExt_val f hf g₁ χ hJ).trans ((val_corr hJ (H.2 χ) _).trans ((val_pull hJ _ _ _).trans ?_))
    have e' : (GlobalTheory.TorusExt.extMap f hf).left ≫ (toUnit (TF (R := R) F)).left = (toUnit (TF (R := R) F')).left := by
      rw [← Over.comp_left, e]
    rw [← e']

theorem exists_data : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → w.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → ∃ (h : (𝟙_ (Over (Sp V))) ⟶ G) (g' : GtPt D.toPre (𝟙_ (Over (Sp V)))) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => (h).left) (fun _ => 1))) (t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, (g'.b).left] (DegPre.lineε 1))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g' ∧ IntTerm.Ext U.toUnifPre x h ∧ GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g' g ∧ f.IsGen ∧ t.IsGen ∧ ∀ e : ℕ, GlobalTheory.Poinc.IntEval.TRel U.toUnifPre h g'.b f t e := by
  intro V _ _ _ hCN D A G _ _ hG U w₀ hw₀ N hN g w x fr hg hw hfr hlies
  haveI : CharZero V := hCN.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hB := D.tau_bimult
  obtain ⟨p, hy, rfl, hp⟩ :=
    GlobalTheory.Poinc.Sep.LiesPair.exists_pair_of_liesOver V hCN D A G hG U w₀ hw₀ N hN _ w x fr hg hw hfr hlies
  have hf : (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (algebraMap (FractionRing V) (FractionRing V)) = algebraMap _ _ := RingHom.comp_id _
  have hq := (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow U hN
    ((GlobalTheory.TorusExt.qkExt_iff hB _ hf p _).2 rfl) x).1 hp
  obtain ⟨h, g', -, -, hform, hext, hpull⟩ := GlobalTheory.Poinc.TorsLift.lift V hCN D A G hG U N hN x _ _ rfl hy hq
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (FractionRing V))) g'
  have e : g₁ = p.g := GlobalTheory.Balanced.gtExt_injective _ hf D.toPre
    (GlobalTheory.FieldRestrictionTest.isPullF_unique (isPullF_gtExt _ hf hg₁) hpull)
  obtain ⟨i, hi⟩ := exists_chart U.LG.isLB (h.left (cpt V))
  obtain ⟨f, hf₀⟩ := GlobalTheory.TorsFrameInt.exists_gen_of_chart U.LG.isLB (K := Fin 1) (fun _ => h.left) (fun _ => 1)
    (fun _ => i) (fun y => Set.mem_iInter.2 fun _ => (top_le_iff_cpt (A := V) h.left _).2 hi (show y ∈ ⊤ from trivial))
  obtain ⟨t, ht, hrel⟩ := GlobalTheory.Poinc.IntEval.exists_integral_frame V hCN D A G U.toUnifPre h g' hform f hf₀
  exact ⟨h, g', f, t, hform, hext, e ▸ hg₁, hf₀, ht, hrel⟩

end GlobalTheory.Poinc.Sep.LiesData

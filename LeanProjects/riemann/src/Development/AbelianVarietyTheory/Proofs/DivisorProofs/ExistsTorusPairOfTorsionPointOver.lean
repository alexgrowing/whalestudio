import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConstMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFramedPointLiesOverTorusExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAdicSumAtImageOfZeroPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointLiesOverAfterFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul

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

namespace GlobalTheory.Poinc.Sep.LiesPair

theorem exists_pair_of_liesOver : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → w.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → ∃ p : QkPt D.toPre (FractionRing V) N, p.y = 0 ∧ p.g = g ∧ QkToAkU U.toUnifPre (FractionRing V) N p x := by
  intro V _ _ _ hCN D A G _ _ hG U w₀ hw₀ N hN g w x fr hg hw hfr hov
  haveI : CharZero V := hCN.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩
  have hB := D.tau_bimult
  obtain ⟨o, ho₁, ho₂⟩ := hg
  letI := GlobalTheory.TorusExt.gtGroup D.toPre (FractionRing V)
  have hkg : N • g = GlobalTheory.TorusExt.iota hB (FractionRing V) 0 := by
    rw [map_zero]
    exact ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho₁).symm.trans ((GlobalTheory.TorusExt.isZero_iff_eq _).1 ho₂)
  let p := GlobalTheory.TorusExt.qkMk hB 0 g hkg
  have hf : (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (algebraMap (FractionRing V) (FractionRing V)) = algebraMap _ _ := RingHom.comp_id _
  let pb := GlobalTheory.TorusExt.qkExt hB _ hf p
  have hp := (GlobalTheory.TorusExt.qkExt_iff hB _ hf p _).2 rfl
  let xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A :=
    GlobalTheory.TorsionExt.fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ x
  obtain ⟨wb, frb, hwb, hfrb, hlb⟩ := GlobalTheory.T.torusExtension_point_liesOver_after_field_extension V _ hA D A G hG U (AlgebraicClosure (FractionRing V)) w₀
    hw₀ g w x fr hw hfr hov xb rfl
  obtain ⟨f', f₁, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U (AlgebraicClosure (FractionRing V)) N hN
  have hq := (f₁ pb (f' pb)).2 rfl
  obtain ⟨w', fr', hw', hfr', hl'⟩ := GlobalTheory.Poinc.Tors.ValPair.liesOver_of_qkToAkU V _ hA D A G hG U
    (AlgebraicClosure (FractionRing V)) w₀ hw₀ _ hN pb (f' pb) rfl hq
  have e := GlobalTheory.Poinc.Tors.OneOver.eq_of_liesOver hL V _ hA D A G hG U (AlgebraicClosure (FractionRing V)) w₀ hw₀
    pb.g wb w' xb (f' pb) frb fr' hwb hw' hfrb hfr' hlb hl'
  refine ⟨p, rfl, rfl, ?_⟩
  refine (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow U hN hp x).2 ?_
  rw [← e] at hq
  exact hq

end GlobalTheory.Poinc.Sep.LiesPair

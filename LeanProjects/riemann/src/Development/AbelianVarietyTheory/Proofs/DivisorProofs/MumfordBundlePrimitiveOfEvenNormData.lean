import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationCompleteLocalEvenOnTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDeterminedByDegenerationDataNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCpEvenOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVGeneric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTripleLinearTorsionIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUBalanced
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordAdjointPrimitiveOfTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedDegenerationDataIsoOfMumfordBundleIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegenerationDataIsoOfPolarisedIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbackAlongIdLiesOverDataIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomExtOfInducedMapsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum

theorem mumfordBundle_primitive_of_evenNorm_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ (w : O) (ν : ℕ), w + star w = 1 → w * star w = (ν : O) → 1 ≤ ν → Even ν → TraceFormTwistIso D.toPre o w → LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG hlin w ν hw hν hν1 hev hpsi
  haveI : CharZero R := hR.2
  obtain ⟨P, hP, hE⟩ := GlobalTheory.Mum.PrimCube.exists_cp_evenOn R hR D A G hG U O o oA oG hlin w hw hpsi
  obtain ⟨A', gen', hgen, hgL⟩ := GlobalTheory.Mum.GenPol.exists_polAV_generic R hR D A G hG U O o oA oG hlin w hw hpsi P hP
  obtain ⟨D', U', hLG, -⟩ := GlobalTheory.Mum.exists_unif_even R hR G P hG hE A' gen' hgen hgL
  obtain ⟨hlam, hadj, hprim⟩ := GlobalTheory.T.lineBundleIso_mumford_adjoint_primitive_of_twist R hR D A G hG U O o oA oG hlin w hw P hP
  rw [← hLG] at hlam hadj hprim
  obtain ⟨hbal1, hbal2⟩ := GlobalTheory.UT.allU_balanced R (maximalIdeal R) hR.1 D' A' G hG U'
  obtain ⟨oA', hoA'⟩ := GlobalTheory.PELOfUnif.exists_oAct_unif U'.toUnifPre oG hadj
  obtain ⟨md, o', hlin'⟩ := hbal1 O oA' oG hoA' hadj
  letI := md
  have hpsi' : TraceFormTwistIso D'.toPre o' w := hbal2 O o' oA' oG hlin' hadj w ν hw hν hν1 hev hprim
  obtain ⟨Φ, xe, hΦ, hov, hto, hcB, hxs, hxc, hwΛ⟩ :=
    GlobalTheory.T.polarisedDegenerationData_iso_of_mumfordBundle_iso R hR D A G hG U O o oA oG hlin D' A' U' o' oA' hlin' hlam
  obtain ⟨hD, hxe, heΦ⟩ := GlobalTheory.T.primitive_degeneration_data_iso_of_polarised_iso R hR D D' O o o' w hpsi hpsi' Φ xe hΦ ⟨hcB, hxs, hxc⟩ hwΛ
  obtain ⟨ψ, bc, φ, hψ, hbc, hcomp, hpu, -⟩ := GlobalTheory.unif_determined_by_data_normal R hR.1 D A G hG U D' A' G hG U' hD
  obtain ⟨hov', hto'⟩ := GlobalTheory.T.uniformisationPullbackAlongId_lies_over_dataIso R hR D A G hG U D' A' U' hD ψ.hom bc Φ.hom hψ hcomp heΦ hpu
  rw [hxe] at hto'
  have h1 : ψ.hom = 𝟙 G := GlobalTheory.T.uniformisedGroupHom_ext_of_induced_maps R hR D A G hG U D' A' U' ψ.hom (𝟙 G) Φ.hom xe.symm hψ inferInstance hov' hov hto' hto
  obtain ⟨wL, hwL, -⟩ := hpu.lg
  have hc : bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = 𝟙 G.left := by
    rw [hcomp, h1]; rfl
  have e1 : LBIso U'.LG.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)))) := ⟨wL, hwL⟩
  rw [hc, hLG] at e1
  have hL := U.LG.isLB
  have hPL := P.L.isLB
  have hN : (cubeLB G ![𝟙 G, oG.act w] U.LG.L).IsLB := GlobalTheory.LamCalc.cubeLB_isLB hL _
  have hL1 : (U.LG.L.pull (𝟙 G.left)).IsLB := pull_isLB hL _
  have e0 : LBIso U.LG.L (U.LG.L.pull (𝟙 G.left)) := (GlobalTheory.DescendedPrincipal.lbIso_pull_id hL).symm
  exact LBIso.trans hL hPL hN (LBIso.trans hL hL1 hPL e0 e1.symm) hP

end GlobalTheory.Mum

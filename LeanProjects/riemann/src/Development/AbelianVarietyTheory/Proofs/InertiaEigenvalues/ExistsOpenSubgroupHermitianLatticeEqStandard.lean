import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoSmulZeroOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRatConstMul
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfIsVacO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CartanInverseThetaIdentity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OpenSubgroupPreservesLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatAtTrivAtOfSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LatOpen.exists_open_hLat_std : ∀ (D : D7) (V : HSp D), Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∃ J : Subgroup (Bridge.Gf V), IsOpen (J : Set (Bridge.Gf V)) ∧ ∀ x ∈ J, Bridge.hLat V x = Formalism.L2.Pj.stdLat D.host.E V.rank := by
  intro D V h1
  refine ⟨(GlobalTheory.Member.PrincLevel.levelGroup V 1).map (finHom V).rangeRestrict,
    GlobalTheory.SmoothVac.isOpen_map_levelGroup V one_pos, ?_⟩
  rintro x ⟨k, hk, rfl⟩
  rw [← h1]
  have hk' := GlobalTheory.Member.PrincLevel.finCong_inv hk.2
  have hm := GlobalTheory.Member.PrincLevel.finCong_map hk.2
  have hm' := GlobalTheory.Member.PrincLevel.finCong_map hk'
  have hL := GlobalTheory.StdFrameCong.pj_latHat_eq V
  have e1 : ((((finHom V).rangeRestrict k)⁻¹ : Bridge.Gf V) :
      GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) = finHom V k⁻¹ := by
    rw [← map_inv]; rfl
  have e0 : (((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) = 1 := by
    rw [inv_one]; rfl
  unfold Bridge.hLat
  refine congrArg (Submodule.span _) (Set.ext fun v => ?_)
  show _ ∈ latHat D.host.F D.host.E (L0c D V) ↔ _ ∈ latHat D.host.F D.host.E (L0c D V)
  rw [e1, e0, Units.val_one, Matrix.one_mulVec, ← hL]
  constructor
  · intro h
    have := hm _ h
    have ekk : (finHom V k).1 * (finHom V k⁻¹).1 = 1 := by
      rw [← Units.val_mul, ← map_mul (finHom V) k k⁻¹, mul_inv_cancel k, map_one, Units.val_one]
    rwa [Matrix.mulVec_mulVec, ekk, Matrix.one_mulVec] at this
  · exact hm' _

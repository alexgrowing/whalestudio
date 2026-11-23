import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairTranslate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedP
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Placed
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SdYFrames
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CommonLineStatement

set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.CentralUnitGen
end GlobalTheory.CentralUnitGen
namespace GlobalTheory.CentralUnitGen
end GlobalTheory.CentralUnitGen
namespace GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem centralRatio_unit_gen_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a = z * _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, PP.under (𝓞 D.host.F) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v z ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (D.sp.Y 0).gram ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v := by
  intro D L hT Gi Gl Kc Yd cX ex W hP hr u u' f f' B B' hPl hPl' a₀ a a₀' a' hA hA' z hzf hzc k hk he v hv hTu hTu'
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hfr := (_root_.GlobalTheory.Fam.sdY_frames_alt W hP 0 hm).2
  have hkS : Formalism.IndefR.Lev.finE (Yc D 0) k ∈ Formalism.L2.DIV.St ((_root_.GlobalTheory.Fam.pk_z W).βY 0) :=
    Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hk.2)
  have hkv := (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D (Yc D 0) _ ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) hfr k).1 hkS v
  have hkv' := Subgroup.inv_mem _ hkv
  obtain ⟨c, hc⟩ := GlobalTheory.T.center_localUnitaryGroup_finitePlace_scalar D (D.sp.Y 0) v _ (GlobalTheory.CentralUnitGen.proj_mem_center _ _ v hzc)
  obtain ⟨c', hc'⟩ := GlobalTheory.T.center_localUnitaryGroup_finitePlace_scalar D (D.sp.Y 0) v _ (GlobalTheory.CentralUnitGen.proj_mem_center _ _ v (Subgroup.inv_mem _ hzc))
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.T.placed_bessel_pair_lattice_alt W hP hr u u' f f' B B' hPl hPl' a₀ a a₀' a' hA hA' v hv hTu hTu'
  have h2 : (c' * c) • (1 : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)) = 1 := by
    have h := congrArg (fun g => (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v g)).1) (inv_mul_cancel z)
    simp only [map_mul, map_one, Units.val_mul, Units.val_one] at h
    rw [hc, hc', Matrix.smul_mul, Matrix.one_mul, smul_smul] at h
    exact h
  have h1 := congrArg (fun g => (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v g)).1) he
  simp only [map_mul, Units.val_mul] at h1
  rw [hc] at h1
  have hkk : (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v k)).1 *
      (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v k)⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  refine GlobalTheory.AdelicU.mem_stabLoc.2 ?_
  rw [hc]
  exact GlobalTheory.CentralUnitGen.scalar_keeps _ w _ _ _ _ c c' h1 h2 hkk (GlobalTheory.AdelicU.mem_stabLoc.1 hkv)
    (GlobalTheory.AdelicU.mem_stabLoc.1 hkv') hw
end GlobalTheory.MiTop
end
end

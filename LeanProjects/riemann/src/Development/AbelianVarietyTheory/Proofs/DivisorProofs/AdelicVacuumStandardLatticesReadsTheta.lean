import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuumEntireFactorIsThetaMovedLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.VacRead

theorem vacuum_reads_theta : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
  D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 → ∀ v : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (stdL D S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) v →
  ∃ G ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d), G ≠ 0 ∧ Reads ψ θ hS hT ⊤ δ 1 G v := by
  intro D ψ θ S T a d hS hT δ hcc hSet v hv
  subst hS hT
  have hδ : δ ≠ 0 := GlobalTheory.NormExact.delta_ne_zero hSet.crv
  have h1 : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) D.host.E), M = 1 →
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) ((1 : GL (Fin k) D.host.E) : Matrix (Fin k) (Fin k) D.host.E) * M *
        ((1 : GL (Fin k) D.host.E) : Matrix (Fin k) (Fin k) D.host.E) = 1 := by
    intro k M hM
    subst hM
    simp [Formalism.UG.cT]
  obtain ⟨Φ, hΦd, hΦ⟩ := GlobalTheory.FockPos.vacuum_real_entire ψ θ S T 1 1 _ _ (h1 _ hSet.gS) (h1 _ hSet.gT) v hv
  have hinV : ∀ {k : ℕ} (L : Submodule (𝓞 D.host.E) (Fin k → D.host.E)),
      GlobalTheory.MovedDict.inV (D := D) 1 L = (L : Set (Fin k → D.host.E)) := by
    intro k L
    simp [GlobalTheory.MovedDict.inV]
  have hv' := hv
  rw [← hinV (stdL D S.rank), ← hinV (stdL D T.rank)] at hv'
  have hC : Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ := by rw [hcc]; exact hSet.crv
  have hTh := GlobalTheory.ThetaLawMoved.theta_of_vacuum_moved ψ θ S T 1 1 (h1 _ hSet.gS) (h1 _ hSet.gT) δ hC hδ
    (stdL D S.rank) (stdL D T.rank) (GlobalTheory.MovedVacuum.sd_stdL D _) (GlobalTheory.MovedVacuum.sd_stdL D _) v hv' Φ hΦd hΦ
  rw [hcc] at hTh
  refine ⟨fun Y => Φ (δ⁻¹ • Y), hTh, ?_, ?_⟩
  · intro hG
    have h0 : v = 0 := GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real hv.2.theta (fun w hw => by
      rw [hΦ w hw]
      have e := congrFun hG (δ • GlobalTheory.FockPos.zCo θ 1 1 w)
      simp only [smul_smul, inv_mul_cancel₀ hδ, one_smul, Pi.zero_apply] at e
      rw [e, mul_zero])
    obtain ⟨⟨p, hp⟩, hq⟩ := hv.2.norm
    have e := hq p hp
    rw [h0] at e
    simp [nrm2] at e
  · rw [GlobalTheory.NormExact.reads_iff hSet.crv hSet.scale]
    refine ⟨hv.2.theta, fun w hw => ?_⟩
    rw [hΦ w hw]
    congr 2
    funext τ i j
    simp [smul_eq_mul, map_one, mul_one, inv_mul_cancel_left₀ hδ]

end GlobalTheory.VacRead

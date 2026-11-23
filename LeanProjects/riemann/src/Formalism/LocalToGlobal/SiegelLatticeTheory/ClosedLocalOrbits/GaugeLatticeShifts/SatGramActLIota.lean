import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActLStmt
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LeviColsPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FormHermitianPositive

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.NormCut Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.Pf.SatGramActL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem satGramActLIota_kB_good {D : D7} {X : HidaSetting D} {w : D.what₂.Word}
    {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X w rs) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (γ : Gam X w) (hk : kB c Λ γ ∈ X.B.I.Kset) : Good X (kB c Λ γ) := by
  have e : kB c Λ γ = ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w)⁻¹ *
      (((iotaF X w γ * c.h (c.base Λ) : Hfin X w) : X.B.I.Gf) * X.xu w) := by
    simp only [kB, Subgroup.coe_mul, mul_assoc]
  rw [e] at hk ⊢
  refine colGood X w _ _ hk ?_
  have h2 := K_inv X.B.I hk
  rwa [mul_inv_rev, inv_inv] at h2

theorem levi_kB_mul_kBB_of_good {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V) (γ : Gam X u) (hk : kB (Y.cs u) Λ γ ∈ X.B.I.Kset)
    (x : X.B.I.GA) (hG : Good X (kBB Y u u' Λ Λ' x)) :
    levi Y.TR (kB (Y.cs u) Λ γ * kBB Y u u' Λ Λ' x) = levi Y.TR (kB (Y.cs u) Λ γ) * levi Y.TR (kBB Y u u' Λ Λ' x) :=
  levi_mul Y.TR (satGramActLIota_kB_good (Y.cs u) Λ γ hk) hG

theorem iotaLeft_holds : IotaLeft := by
  intro D X Y u u' t γ hk
  exact levi_kB_mul_kBB_of_good Y u u' t.lam t.lam' γ hk t.rep.1.1
    (Formalism.L2.SG.Closed.AdmPar_holds (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') t)

end Formalism.L2.SG.Pf.SatGramActL

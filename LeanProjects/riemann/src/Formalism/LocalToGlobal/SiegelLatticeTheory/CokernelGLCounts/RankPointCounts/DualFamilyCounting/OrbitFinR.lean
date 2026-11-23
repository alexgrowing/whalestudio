import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaCOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MemPerpMapFlag
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittExistsHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrbitFiniteOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.TransMemUnipotentIntegral
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFRepFinal

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def CntIsoInv : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : MatZ D),
    cntE T' (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) Z = cntE T' F0 Λ Z

theorem orbitFiniteR_of (hI : CntIsoInv) : OrbitFiniteR := by
  intro D δ M hA L u u' hT F0 what₂ hR Z Λ hΛ
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  obtain ⟨β, hβ, he, hz⟩ := Formalism.L2.SG.Pf.WittFlags.flag_witt hT0 rfl F0 (Formalism.MainNotions.S.Inh.tie_flag0 D u)
  have hR' := Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D β hβ F0 what₂ hR
  have hF1e : (Formalism.L2.SG.Saturated.mapFlag β hβ F0).e = D.sp.hypE := by
    funext a
    show β (F0.e a) = _
    rw [he a]
    rfl
  have hF1z : (Formalism.L2.SG.Saturated.mapFlag β hβ F0).z = D.zmOf u := by
    show β F0.z = _
    rw [hz]
    rfl
  have hRO : RowsOf u (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (what₂.image (Formalism.HermitianLatticesTheory.gmap β)) :=
    ⟨hF1e, hF1z, hR', ⟨_, Finset.mem_image_of_mem _ hΛ⟩⟩
  have h := PI.UnitaryGroupMassFormula.CntFormula.orbitFinite_of PI.UnitaryGroupMassFormula.CntFormula.unipotent_integral_isGroup PI.UnitaryGroupMassFormula.CntFormula.orbit_representatives
    D δ M hA L u u' hT _ _ hRO Z (Formalism.HermitianLatticesTheory.gmap β Λ) (Finset.mem_image_of_mem _ hΛ)
  rwa [hI D β hβ (Tn u') F0 Λ Z] at h

end Formalism.L2.SG.Pf.Cnt

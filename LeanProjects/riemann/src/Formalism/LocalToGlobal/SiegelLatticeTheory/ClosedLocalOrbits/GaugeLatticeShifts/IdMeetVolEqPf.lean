import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiTrivOut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPfLam
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

theorem mem_gcS {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) (s : X.B.I.Ginf) :
    s ∈ GcS X u hK c ↔ ∃ γ : X.B.I.GA, γ ∈ X.B.I.GFset ∧ γ.1 = s ∧ γ.1 ∈ X.NinfU u ∧ γ.2 ∈ X.NfinU u ∧
      c⁻¹ * γ.2 * c ∈ X.K2 := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨hG, hP⟩ := Subgroup.mem_inf.1 hγ
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hP
    obtain ⟨hN, hk⟩ := Subgroup.mem_inf.1 h2
    obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.1 hk
    refine ⟨γ, hG, rfl, h1, hN, ?_⟩
    have : γ.2 = c * k * c⁻¹ := by rw [← hke]; rfl
    rw [this]
    have : c⁻¹ * (c * k * c⁻¹) * c = k := by group
    rw [this]; exact hk
  · rintro ⟨γ, hG, rfl, h1, hN, hk⟩
    refine ⟨γ, Subgroup.mem_inf.2 ⟨hG, Subgroup.mem_prod.2 ⟨h1, Subgroup.mem_inf.2 ⟨hN, ?_⟩⟩⟩, rfl⟩
    refine Subgroup.mem_map.2 ⟨c⁻¹ * γ.2 * c, hk, ?_⟩
    show c * (c⁻¹ * γ.2 * c) * c⁻¹ = γ.2
    group

theorem noinfEqC_holds : NOinfEqC := by
  intro D X u hK
  ext s
  rw [SetLike.mem_coe, mem_gcS]
  constructor
  · rintro ⟨γ, hG, h1, hN, hF, hk⟩
    exact ⟨γ, hG, h1, hN, hF, hk⟩
  · rintro ⟨γ, hG, h1, hN, hF, hk⟩
    exact ⟨γ, hG, h1, hN, hF, hk⟩

theorem nocolEqC_holds : NOcolEqC := by
  intro D X Y u ρ
  ext s
  rw [SetLike.mem_coe, mem_gcS]
  constructor
  · rintro ⟨x, n, hx, rfl, hn⟩
    exact ⟨x, ratLink_mem X hx, rfl, nLamNinf_holds D X u _ x n hx hn, nLamNfin_holds D X u _ x n hx hn,
      (nilradical_conj_level' D X Y u ρ x n hn hx).1⟩
  · rintro ⟨γ, hG, rfl, hN, hF, hk⟩
    exact Formalism.L2.SG.Pf.SlabCoverPf.nilradical_rational_lattice D X Y u ρ γ (Formalism.L2.SG.Closed.level_subgroup_properties X) hG hN hF hk

theorem gcCountC_holds : GcCountC := by
  intro D X u hK c
  have hR : (RcS X u hK c : Set X.B.I.GA).Countable :=
    (Set.countable_coe_iff.1 (Formalism.MainNotions.LeviCoordinates.rr_GF_countable X.B.I)).mono (fun _ h => (Subgroup.mem_inf.1 h).1)
  have : (GcS X u hK c : Set X.B.I.Ginf).Countable := by
    unfold GcS
    rw [Subgroup.coe_map]
    exact hR.image _
  exact this.to_subtype

theorem conjUC_holds : ConjUC := by
  intro D X u hK g c
  ext x
  simp only [UcS, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hN, k, hk, hke⟩
    refine ⟨(g : X.B.I.Gf)⁻¹ * x * (g : X.B.I.Gf), ⟨?_, k, hk, ?_⟩, ?_⟩
    · have := (nfinConj_holds X u g⁻¹ x hN).1
      simp only [InvMemClass.coe_inv, inv_inv] at this
      exact this
    · rw [← hke]; group
    · group
  · rintro ⟨y, ⟨hN, k, hk, hke⟩, rfl⟩
    refine ⟨(nfinConj_holds X u g y hN).1, k, hk, ?_⟩
    rw [← hke]; group

end Formalism.L2.SG.Pf.IdMeet

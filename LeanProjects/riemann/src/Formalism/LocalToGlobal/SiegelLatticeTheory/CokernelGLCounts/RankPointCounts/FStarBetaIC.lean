import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIB

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BetaI

theorem xi_inv_last (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (i : Fin D.R.rS) :
    (admXi D Λ F F')⁻¹ (Fin.last D.R.rS) i.castSucc = 0 := by
  obtain ⟨h1, h2⟩ := admissibility_witness_unitriangular Λ F F'
  have hbt : (admXi D Λ F F').BlockTriangular id := fun i j hij => h1 i j hij
  have hdet : (admXi D Λ F F').det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hbt]; simp [h2]
  haveI : Invertible (admXi D Λ F F') := Matrix.invertibleOfIsUnitDet _ (by rw [hdet]; exact isUnit_one)
  exact Matrix.blockTriangular_inv_of_blockTriangular hbt (Fin.castSucc_lt_last i)

theorem frameAct_mem {T' : D.host.E} (G : LFlag (VS D) D.R.rS T')
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) (i : Fin D.R.rS)
    (h : ξ (Fin.last D.R.rS) i.castSucc = 0) : frameAct (frame G) ξ i.castSucc ∈ Xsp G := by
  show ∑ a, ((ξ a i.castSucc : 𝓞 D.host.E) : D.host.E) • frame G a ∈ Xsp G
  rw [Fin.sum_univ_castSucc, h]
  refine add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_) (by simp)
  rw [frame_csG]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem tf' (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (b : Fin (D.R.rS + 1)) :
    (tLoc Zd p γ).f' b = (TermLoc.sgnP' D p b * frFac Zd.δ p b) •
      baseChange₂ D p (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹ b) := rfl

theorem bcP_perp_f' (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) {m : (VS D).V}
    (hm : m ∈ orth (VS D) (Xsp (repF γ))) :
    baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f') := by
  show ∀ w ∈ (locH Zd p).X (tLoc Zd p γ).f', (locH Zd p).h (baseChange₂ D p m) w = 0
  intro w hw
  rw [h_eq]
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    simp only
    rw [tf', LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange,
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hm _
        (frameAct_mem _ _ i (xi_inv_last γ.lam (lf D F0) (repF γ) i)), map_zero, mul_zero]
  | zero => exact LocFacts.localForm_zero_right Zd p _
  | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
  | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]

end BetaI

variable (u u' F0 what₂)

def PinB : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∀ (p : PlF D) (m : (VS D).V) (hm : baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
        (hm₂ : baseChange₂ D p (β₀ m) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂))),
        m ∈ orth (VS D) (Xsp (repF γ)) →
        φ' p ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, hm⟩) =
          (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m), hm₂⟩

variable {u u' F0 what₂}

theorem lsetB_of (hP : PinB Zd u u' F0 what₂) : LsetB Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hiso hfr hW hO p m hm hmo
  have hloc := hB.2.2.2.1.2 p
  have hL' := hloc.2.2.2.1
  have hmp := bcP_perp_f' Zd p γ hmo
  have hXmap := BwdBetaCut.Xsp_of_frame β₀ _ _ hfr
  have hmo₂ : β₀ m ∈ orth (VS D) (Xsp (liftF F'₂)) := by
    rw [← hXmap, Formalism.L2.SG.Pf.orth_map_sat β₀ hiso]
    exact Submodule.mem_map_of_mem hmo
  have hmp₂ := baseChangeAt_perp' Zd p F'₂ hmo₂
  have hin : (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, hmp⟩ ∈
      (locH Zd p).Lset (tLoc Zd p γ).abelian₂ (tLoc Zd p γ).f' := ⟨⟨_, hmp⟩, baseChange_mem_localLattice Zd hm p, rfl⟩
  obtain ⟨x, hxΛ, hxe⟩ := hL'.subset ⟨_, hin, rfl⟩
  rw [hP γ Z F'₂ φ φ' Λ₂ hB β₀ hiso hfr hW hO p m hmp hmp₂ hmo] at hxe
  refine ⟨(x : Vp D p), hxΛ, ?_⟩
  have := (Submodule.Quotient.eq _).1 hxe.symm
  simpa using this

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

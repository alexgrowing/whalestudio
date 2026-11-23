import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameActOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsometryFixFlagAnisotropicVectorOfFixFrame

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdCut

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u') (F0) in

def GenXiRev : Prop :=
  ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (p : PlF D),
    IsRowLat D F0 Λ → AdmWit Λ (gS D) (lf D F0) F' 1 → IsLift Λ F' →
    (locH Zd p).IsGeneric ⟨lattice₂ D Zd.M p Λ, (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).f, locF' Zd p F',
      (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).T, (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).T'⟩ →
    (locH Zd p).IsGeneric (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u'))

theorem rowLat_of_move (hC : CtxP u u' F0 what₂) (γ : TermDef.Term D u u' F0 what₂) {Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0)
    (himg : (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)) : IsRowLat D F0 Λ₂ := by
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hg : Formalism.HermitianLatticesTheory.gmap n Λ₂ = γ.lam := gmap_eq_of_image himg
  have hni : n⁻¹ ∈ Formalism.L2.SG.Pf.Cnt.StabilizerQuotient.G0 F0 := by
    refine ⟨(Formalism.HermitianLatticesTheory.isom _).inv_mem hn.1, fun a => ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_) a
    · have h := hn.2.2.2.2
      simp only [FlagG.fvec, Fin.snoc_last]
      show n.symm _ = _
      rw [LinearEquiv.symm_apply_eq, h]
    · have h := hn.2.2.2.1 i
      simp only [FlagG.fvec, Fin.snoc_castSucc]
      show n.symm _ = _
      rw [LinearEquiv.symm_apply_eq, h]
  have h2 := Formalism.L2.SG.Pf.Cnt.StabilizerQuotient.rowLat_gmap ⟨n⁻¹, hni⟩ hrow
  have e : Formalism.HermitianLatticesTheory.gmap (n⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) γ.lam = Λ₂ := by
    rw [← hg, ← Formalism.L2.SG.Pf.gmap_mul_sat, inv_mul_cancel, Formalism.L2.SG.Pf.gmap_one_sat]
  rw [← e]; exact h2

variable {Zd}

theorem btGen_of (hOK : BtOK Zd u u' F0 what₂) (hGX : GenXiRev Zd u' F0) : BtGen Zd u u' F0 what₂ := by
  intro hC γ Z F'₂ φ φ' Λ₂ hs
  have hLift := btLift_holds Zd hC γ Z F'₂ φ φ' Λ₂ hs
  have hAdm := btAdm Zd hC γ Z F'₂ φ φ' Λ₂ hs
  have hG := btG_holds Zd hC γ Z F'₂ φ φ' Λ₂ hs
  have hOKv := hOK hC γ Z F'₂ φ φ' Λ₂ hs
  obtain ⟨_, _, ⟨hlat, hloc⟩, ⟨n, hn, himg⟩⟩ := hs
  have hR := rowLat_of_move hC γ hn himg
  have hPD : PD D Λ₂ (lf D F0) u' (liftF F'₂) := ⟨hLift, ⟨1, hAdm⟩, hOKv⟩
  refine (Formalism.L2.SG.Pf.frameGenLoc_holds D Zd F0 Λ₂ (liftF F'₂) hR hPD
    (Formalism.L2.SG.Pf.m_plus_independent _ _ _ _) hG).2 fun p => ?_
  exact hGX Λ₂ (liftF F'₂) p hR hAdm hLift (hloc p).1

theorem bwdTerm'_of' (hOK : BtOK Zd u u' F0 what₂) (hGX : GenXiRev Zd u' F0) : BwdTerm' Zd u u' F0 what₂ :=
  bwdTerm'_of Zd (btLift_holds Zd) (btAdm Zd) (btG_holds Zd) hOK (btGen_of hOK hGX)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

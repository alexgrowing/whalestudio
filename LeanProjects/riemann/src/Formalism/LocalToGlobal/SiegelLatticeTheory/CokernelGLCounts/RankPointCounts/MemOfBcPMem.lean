import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BwdPairOfTermBeta
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarUniq
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocEqOfLocFEq

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdCut

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def BtSit (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) : Prop :=
  Ctx γ Z ∧ StarHyp Zd γ Z F'₂ φ φ' ∧ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ' ∧
    ∃ n ∈ unipotentFrameFixers F0, (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)

variable (u u' F0 what₂)

def BtStep (P : Submodule (𝓞 D.host.E) (VS D).V → LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) → Prop) : Prop :=
  CtxP u u' F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BtSit Zd γ Z F'₂ φ φ' Λ₂ → P Λ₂ (liftF F'₂)

def BtLift : Prop := BtStep Zd u u' F0 what₂ fun Λ₂ F' => IsLift Λ₂ F'

def BtAdm : Prop := BtStep Zd u u' F0 what₂ fun Λ₂ F' => AdmWit Λ₂ (gS D) (lf D F0) F' 1

def BtG : Prop := BtStep Zd u u' F0 what₂ fun _ F' => Gval (lf D F0) F' ≠ 0

def BtOK : Prop := BtStep Zd u u' F0 what₂ fun Λ₂ F' => FrameOK D Λ₂ F'

def BtGen : Prop := BtStep Zd u u' F0 what₂ fun Λ₂ F' => IsGeneric Λ₂ (gS D) (lf D F0) F'

variable {u u' F0 what₂}

theorem bwdTerm'_of (h1 : BtLift Zd u u' F0 what₂) (h2 : BtAdm Zd u u' F0 what₂) (h3 : BtG Zd u u' F0 what₂)
    (h4 : BtOK Zd u u' F0 what₂) (h5 : BtGen Zd u u' F0 what₂) : BwdTerm' Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ hn
  have hs : BtSit Zd γ Z F'₂ φ φ' Λ₂ := ⟨hZ, hS, hΛ₂, hn⟩
  exact ⟨⟨h1 hC γ Z F'₂ φ φ' Λ₂ hs, ⟨1, h2 hC γ Z F'₂ φ φ' Λ₂ hs⟩, h3 hC γ Z F'₂ φ φ' Λ₂ hs⟩,
    h2 hC γ Z F'₂ φ φ' Λ₂ hs, h5 hC γ Z F'₂ φ φ' Λ₂ hs, h4 hC γ Z F'₂ φ φ' Λ₂ hs⟩

theorem btG_holds : BtG Zd u u' F0 what₂ := by
  intro _ γ Z F'₂ φ φ' Λ₂ hs
  obtain ⟨⟨w, _, w', hGw', _, hZw'⟩, hS, _, _⟩ := hs
  have h1 : Gval (lf D F0) (liftF F'₂) =
      Formalism.L2.SG.CntLocal.GZ (((Tu D u : ℕ) : D.host.E)) (((Tu D u' : ℕ) : D.host.E)) Z := by
    rw [← hS.1]; rfl
  rw [h1, Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.Uniq.gz_atMat hZw' (Tu D u) (Tu D u')]
  exact hGw'

theorem sgnP'_last (p : PlF D) : sgnP' D p (Fin.last D.R.rS) = 1 := by
  unfold sgnP'
  split
  · unfold TermLoc.sgnP; split
    · simp
    · rfl
  · simp

theorem frFac_last (p : PlF D) : frFac Zd.δ p (Fin.last D.R.rS) = 1 := by
  unfold frFac; simp

theorem locF'_last (p : PlF D) {T' : D.host.E} (F' : LFlag (VS D) D.R.rS T') :
    locF' Zd p F' (Fin.last D.R.rS) = baseChange₂ D p F'.fl.z := by
  unfold locF'
  rw [sgnP'_last, frFac_last, one_mul, one_smul]
  congr 1
  simp [frame, FlagG.fvec]

theorem mem_of_baseChange_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ) {x : (VS D).V}
    (h : ∀ p, baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ) : x ∈ Λ := by
  refine PI.UnitaryGroupMassFormula.UJClassMass.interLocF (F := D.host.F) Λ hΛ x fun v => ?_
  haveI := v.isPrime
  have h2 := (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd v hΛ x).1 (h v)
  exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF v.asIdeal Λ x).1 h2

theorem btLift_holds : BtLift Zd u u' F0 what₂ := by
  intro _ γ Z F'₂ φ φ' Λ₂ hs
  obtain ⟨_, _, ⟨hlat, hloc⟩, _⟩ := hs
  refine ⟨mem_of_baseChange_mem Zd hlat fun p => ?_, rfl⟩
  have hfr := (hloc p).1.1.2.2.1
  have h1 : locF' Zd p F'₂ (Fin.last D.R.rS) ∈ lattice₂ D Zd.M p Λ₂ := hfr.1.1 (Fin.last D.R.rS)
  rwa [locF'_last] at h1

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

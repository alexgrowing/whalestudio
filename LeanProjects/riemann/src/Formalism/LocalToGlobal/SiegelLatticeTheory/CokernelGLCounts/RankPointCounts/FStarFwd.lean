import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnipotentFrameFixers

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : Formalism.BasicNotions.D7}

def OmCls {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F'₂ F' : LFlag (VS D) D.R.rS T') : Prop :=
  ∀ c : Fin (D.R.rS + 1) → D.host.E, (∀ a, (VS D).hT (F0.e a) (∑ b, c b • frame F'₂ b) = 0) →
    ∑ b, c b • (frame F' b - frame F'₂ b) ∈ Xsp (lf D F0)

variable (D)

def NMove : Prop :=
  ∀ {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F'₂ F' : LFlag (VS D) D.R.rS T'),
    ZhatL (lf D F0) F'₂ = ZhatL (lf D F0) F' → Gval (lf D F0) F' ≠ 0 → OmCls F0 F'₂ F' →
      ∃ n ∈ unipotentFrameFixers F0, Moves n F'₂ F'

end Defs

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def OmPart : Prop :=
  IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' → ∀ F', IsPartner γ Z F' → OmCls F0 F'₂ F'

def LocIn : Prop :=
  IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' → ∀ F', IsPartner γ Z F' → ∀ n ∈ unipotentFrameFixers F0, Moves n F'₂ F' →
        ∀ p, lattice₂ D Zd.M p (Formalism.HermitianLatticesTheory.gmap n.symm γ.lam) ∈
          locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p)

variable {u u' F0 what₂}

theorem fwdCut_image_gmap_symm (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (n : (VS D).V → (VS D).V) '' (Formalism.HermitianLatticesTheory.gmap n.symm Λ : Set (VS D).V) = (Λ : Set (VS D).V) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.map_coe, Set.mem_image, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    SetLike.mem_coe]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨n.symm x, ⟨x, hx, rfl⟩, by simp⟩

theorem fwdCut_gval_congr {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F₁ F₂ : LFlag (VS D) D.R.rS T')
    (h : ZhatL F F₁ = ZhatL F F₂) : Gval F F₁ = Gval F F₂ := by
  simp only [Gval, Formalism.MainNotions.S.Gflag, Formalism.MainNotions.S.Dl] at h ⊢
  rw [show Formalism.MainNotions.S.Zhat F.fl F₁.fl = Formalism.MainNotions.S.Zhat F.fl F₂.fl from h]

theorem fwdC_of (hrows : IsRowReps D F0 what₂) (h1 : NMove D) (h2 : OmPart Zd u u' F0 what₂)
    (h3 : LocIn Zd u u' F0 what₂) : FwdC Zd u u' F0 what₂ := by
  intro γ Z hC F'₂ φ φ' hS F' hP
  have hEZ := hP.1
  have hZ' : ZhatL (lf D F0) F' = Z := hEZ.2.2.2.2
  have hG : Gval (lf D F0) F' ≠ 0 := hEZ.1.2.2
  obtain ⟨n, hn, hm⟩ := h1 F0 F'₂ F' (hS.1.trans hZ'.symm) hG (h2 hrows γ Z hC F'₂ φ φ' hS F' hP)
  refine ⟨Formalism.HermitianLatticesTheory.gmap n.symm γ.lam, ⟨?_, h3 hrows γ Z hC F'₂ φ φ' hS F' hP n hn hm⟩, n, hn, hm,
    fwdCut_image_gmap_symm n γ.lam⟩
  exact Formalism.HermitianLatticesTheory.isomAct_lattice n.symm γ.lam (hrows.1 γ.lam γ.mem).1.1

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlLineHolds

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SRat {D : D7} {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V) :=
  {s | s ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j) ∧ s F.fl.z - F.fl.z ∈ Xsp F}

def NmlPtDC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ γ : PN.Pts D.host.E D.R.rS, 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∀ t1 t2 : TauC Y u u', Gt t1 ≠ 0 → Gt t2 ≠ 0 → ptPN t1 = γ → ptPN t2 = γ →
          (Y.tO u u').rowOf t1 = (Y.tO u u').rowOf t2 →
          ∃ σ ∈ SRat (lf D (X.Fu u)), ∃ s' ∈ SRat (lf D (X.Fu u')), t2.lin = σ * t1.lin * s'

def UnitaryNormalVectorCount : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
        ∀ t0 t1 t2 : TauC Y u u', Gt t0 ≠ 0 → Gt t1 ≠ 0 → Gt t2 ≠ 0 →
          RelC Y u u' t0 t1 → RelC Y u u' t0 t2 → t1.G = t0.G → t2.G = t0.G →
          (∃ σ ∈ SRat (lf D (X.Fu u)), ∃ s' ∈ SRat (lf D (X.Fu u')), t2.lin = σ * t1.lin * s') →
          coefA Y u u' t0 t1 = coefA Y u u' t0 t2 → coefA' Y u u' t0 t1 = coefA' Y u u' t0 t2 →
          nmlOf Y u u' t1 = nmlOf Y u u' t2

theorem nmlSep_of (hP : NmlPtDC) (hG : UnitaryNormalVectorCount) : NmlSep := by
  intro Cg cb Cw cT CT C0
  obtain ⟨A1, B1, h1⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨A2, B2, h2⟩ := hG Cg cb Cw cT CT C0
  refine ⟨max A1 A2, max B1 B2, fun C' Cl hC hl D large₂ X Y u u' hctx γ hγ t0 t1 t2 g0 g1 g2 p0 p1 p2 r1 r2 ca ca' => ?_⟩
  have hdc := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hl) D large₂ X Y u u' hctx γ hγ t1 t2 g1 g2 p1 p2
    (r1.1.trans r2.1.symm)
  have e0 := gval_occ (t := t0) (hG := p0 ▸ hγ)
  have e1 := gval_occ (t := t1) (hG := p1 ▸ hγ)
  have e2 := gval_occ (t := t2) (hG := p2 ▸ hγ)
  have hG1 : t1.G = t0.G := by
    rw [Formalism.L2.SG.Pf.SatGram.gterm_G (Y := Y) (t := t1), Formalism.L2.SG.Pf.SatGram.gterm_G (Y := Y) (t := t0)]
    rw [e1, e0, p1, p0]
  have hG2 : t2.G = t0.G := by
    rw [Formalism.L2.SG.Pf.SatGram.gterm_G (Y := Y) (t := t2), Formalism.L2.SG.Pf.SatGram.gterm_G (Y := Y) (t := t0)]
    rw [e2, e0, p2, p0]
  exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hl) D large₂ X Y u u' hctx t0 t1 t2 g0 g1 g2 r1 r2
    hG1 hG2 hdc ca ca'

end Formalism.L2.SG.NGCut.NormalVectorPairings

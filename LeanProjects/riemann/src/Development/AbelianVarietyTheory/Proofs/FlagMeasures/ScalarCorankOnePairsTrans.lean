import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarEquivalenceGeneral.ScalarFactorEqOneOfLe
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClass
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalTrans

open Module

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem isScalar_trans {Λ : Submodule (𝓞 E) S.V} {r k : ℕ} {T T' : E} {F : LFlag S r T}
    {F' F'' F''' : LFlag S r T'} {β γ : S.V ≃ₗ[E] S.V}
    (hΛ : Submodule.IsLattice E Λ) (hdim : finrank E S.V = k + 2 * r + 1)
    (hF : IsLift Λ F) (hL' : IsLift Λ F') (hG' : Gval F F' ≠ 0) (hL'' : IsLift Λ F'')
    (hG'' : Gval F F'' ≠ 0) (hi : β ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hX : ∀ j, (Xflag F' j).map (β : S.V →ₗ[E] S.V) = Xflag F'' j) (hz : β F'.fl.z = F''.fl.z)
    (hs1 : s0 Λ F F' F'' β k = 1) (hS1 : IsScalar Λ F F' F'' β) (hS2 : IsScalar Λ F F'' F''' γ) :
    IsScalar Λ F F' F''' (β.trans γ) := by
  have n' := _root_.PI.UnitaryGroupMassFormula.ScalEquivGen.ndOfQ hΛ hF hL' hG'
  have n'' := _root_.PI.UnitaryGroupMassFormula.ScalEquivGen.ndOfQ hΛ hF hL'' hG''
  have hTh1'' := _root_.PI.UnitaryGroupMassFormula.ScalEquivGen.thEq''Q hΛ hdim n' n'' hs1
  intro y1 hy1 y3 hy3 y1' hy1' y3' hy3' h13 h31 al al'
  have hy1b : y1 ∈ orth S (Xplus F) := hy1.2
  have hy1'b : y1' ∈ orth S (Xplus F') := hy1'.2
  have hy2 : y1 ∈ Ylift Λ F F'' :=
    Submodule.mem_inf.mpr ⟨_root_.PI.UnitaryGroupMassFormula.ScalEquivGen.yliftMemQ hTh1'' hy1, hy1b⟩
  have hy2' : β y1' ∈ Ylift' Λ F F'' :=
    Submodule.mem_inf.mpr ⟨_root_.PI.UnitaryGroupMassFormula.ScalEquivGen.ylift'MemQ hi hX hTh1'' hy1',
      _root_.PI.UnitaryGroupMassFormula.ScalEquivGen.mapOrthXplusQ hi hX hz hy1'b⟩
  have a := hS1 y1 hy1 y1 hy2 y1' hy1' (β y1') hy2' (by simp) (by simp) al al'
  have b := hS2 y1 hy2 y3 hy3 (β y1') hy2' y3' hy3' h13 h31 al al'
  exact a.trans b

end Gen

theorem scalar_pair_trans : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∀ t t' t'' : TauC Y u u', t.G ≠ 0 → t'.G ≠ 0 → t''.G ≠ 0 →
    (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t'' = 1 →
    (Y.tO u u').scal t' t'' → (Y.tO u u').s0 t t'' = 1 ∧ (Y.tO u u').scal t t'' := by
  intro D X Y u u' t t' t'' hG hG' hG'' h1 hsc1 h2 hsc2
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : ∀ s : TauC Y u u', s.G ≠ 0 → Gval (lf D (X.Fu u)) s.frame ≠ 0 := fun s hs h =>
    hs ((Formalism.L2.SG.Pf.SatGram.gterm_G Y s).trans h)
  have hlat : Submodule.IsLattice D.host.E t.lam := ((Y.rowsOK u).1 t.lam t.mem).2.1.1
  have hLF : IsLift t.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : ∀ s : TauC Y u u', IsLift s.lam s.frame := fun s => s.rep.2.2.2.2.1
  obtain ⟨⟨hl1, hl1'⟩, hs1, hS1⟩ := (show scalT t t' from hsc1)
  obtain ⟨⟨hl2, hl2'⟩, hs2, hS2⟩ := (show scalT t' t'' from hsc2)
  rw [← hl1] at hs2 hS2
  have hL' : IsLift t.lam t'.frame := by rw [hl1]; exact hLt t'
  have hL'' : IsLift t.lam t''.frame := by rw [hl1, hl2]; exact hLt t''
  have hth1 := (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hlat _ t.frame t'.frame _ hLF (hLt t)
    (hGv t hG)).1 hs1
  have hth2 := (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hlat _ t'.frame t''.frame _ hLF hL'
    (hGv t' hG')).1 hs2
  have htr := Formalism.L2.SG.NGCut.CorankRelation.Th_trans t.lam _ t.frame t'.frame t''.frame (t'.lin * t.lin⁻¹)
    (t''.lin * t'.lin⁻¹) (fun x hx => (Formalism.L2.SG.NGCut.CorankRelation.frame_mem_iff t' t'' x).1 hx) hth1 hth2
  have hmul : (t''.lin * t'.lin⁻¹) * (t'.lin * t.lin⁻¹) = t''.lin * t.lin⁻¹ := by group
  rw [hmul] at htr
  have hs3 : Lat.s0 t.lam (lf D (X.Fu u)) t.frame t''.frame (t''.lin * t.lin⁻¹) D.R.k = 1 :=
    (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hlat _ t.frame t''.frame _ hLF (hLt t) (hGv t hG)).2 htr

  have hi1 := t.rep.2.2.1
  have hi2 := t'.rep.2.2.1
  have hiβ : t'.lin * t.lin⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hi2 ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hi1)
  have hX : ∀ j, (Xflag t.frame j).map ((t'.lin * t.lin⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
      (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag t'.frame j := by
    intro j
    unfold GTerm.frame
    rw [Formalism.L2.SG.Pf.MainEqClass.xflag_mapLF' t.lin hi1, Formalism.L2.SG.Pf.MainEqClass.xflag_mapLF' t'.lin hi2,
      ← Submodule.map_comp]
    congr 1
    ext x
    simp
  have hz : (t'.lin * t.lin⁻¹) t.frame.fl.z = t'.frame.fl.z := by
    unfold GTerm.frame
    rw [Formalism.L2.SG.Pf.MainEqClass.z_mapLF' t.lin hi1, Formalism.L2.SG.Pf.MainEqClass.z_mapLF' t'.lin hi2]
    simp
  have hsc3 := isScalar_trans (β := t'.lin * t.lin⁻¹) (γ := t''.lin * t'.lin⁻¹) hlat hdim hLF (hLt t) (hGv t hG) hL'
    (hGv t' hG') hiβ hX hz hs1 hS1 hS2
  have e3 : (t'.lin * t.lin⁻¹).trans (t''.lin * t'.lin⁻¹) = t''.lin * t.lin⁻¹ := hmul
  rw [e3] at hsc3
  have hl : t.lam = t''.lam ∧ t.lam' = t''.lam' := ⟨hl1.trans hl2, hl1'.trans hl2'⟩
  refine ⟨?_, ?_⟩
  · show s0T t t'' = 1
    unfold s0T
    rw [if_pos hl]
    exact hs3
  · show scalT t t''
    exact ⟨hl, hs3, hsc3⟩

end GlobalTheory.ScalTrans

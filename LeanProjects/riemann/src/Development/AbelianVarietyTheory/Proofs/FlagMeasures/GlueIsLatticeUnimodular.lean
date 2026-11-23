import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitRowLatticeMiddleIffGluedLattice
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.Glue

open GlobalTheory.LoopC.RowGlue

theorem glue_isLattice_unimodular : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D), GlobalTheory.TypeAsm.Std D large₂ → ∀ L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X), Submodule.IsLattice D.host.E L → Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L → Submodule.IsLattice D.host.E (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) ∧ Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) := by
  intro D large₂ X _ L hL hU
  have H : IsHypFrame (VS D).hT X.eX X.fY := ⟨(VS D).herm, X.ee, X.ff, X.ef⟩
  have h0 : ∀ a, aaD D a ≠ 0 := fun a => zpow_ne_zero _ (ddS_ne_zero D)
  have hs : ∀ a, StarStable (aaD D a) := fun a => (ddS_stable D).zpow (ddS_ne_zero D) _
  have hmid : ∀ w ∈ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)),
      Mid (VS D).hT X.eX X.fY w := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  refine ⟨H.isLattice (A := fun a => aaD D a) (B := fun a => (aaD D a)⁻¹) h0 (fun a => inv_ne_zero (h0 a))
    (hL.fg.map _) ?_, (H.unimodular_iff (A := fun a => aaD D a) (B := fun a => (aaD D a)⁻¹) hmid
      (fun a => inv_ne_zero (h0 a)) (fun a => (hs a).inv (h0 a)) (fun a => (inv_inv _).symm)).2 ?_⟩
  · intro w hw
    have h1 : (⟨w, hw⟩ : GlobalTheory.RowsOrb.Wb X) ∈ Submodule.span D.host.E (L : Set (GlobalTheory.RowsOrb.Wb X)) := by
      rw [hL.span_eq_top]; trivial
    have h2 := Submodule.mem_map_of_mem (f := (GlobalTheory.RowsOrb.Wb X).subtype) h1
    rw [Submodule.map_span] at h2
    exact h2
  · intro w hw
    have key : (⟨w, hw⟩ : GlobalTheory.RowsOrb.Wb X) ∈ Formalism.HermitianLatticesTheory.dual (GlobalTheory.RowsOrb.hb X) L ↔
        (⟨w, hw⟩ : GlobalTheory.RowsOrb.Wb X) ∈ L := by
      rw [show Formalism.HermitianLatticesTheory.dual (GlobalTheory.RowsOrb.hb X) L = L from hU]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at key ⊢
    constructor
    · intro h
      exact ⟨⟨w, hw⟩, key.1 fun y hy => h y ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨w', hw', e⟩ _ ⟨y, hy, rfl⟩
      have e' : (⟨w, hw⟩ : GlobalTheory.RowsOrb.Wb X) = w' := Subtype.ext e.symm
      exact key.2 (e' ▸ hw') y hy

end GlobalTheory.RowsOrb.Glue

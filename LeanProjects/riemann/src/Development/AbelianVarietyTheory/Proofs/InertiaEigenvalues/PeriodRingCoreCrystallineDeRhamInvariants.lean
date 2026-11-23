import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem Fits.invB {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) : C.InvB := by
  intro K b hb
  set b' : P.R.B := T.eB.symm b with hb'
  have hfix : ∀ g : ↥(GK K), (P.PD K).actB g b' = b' := by
    intro g
    rw [P.PD_actB]
    apply T.eB.injective
    rw [T.actB, hb', RingEquiv.apply_symm_apply]
    exact hb g g.2
  obtain ⟨c, hc⟩ := (P.PD K).invB b' hfix
  refine ⟨IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) c, (inf_le_left : K0 K ≤ K.1) c.2, ?_⟩
  rw [← hF.u]
  have : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) c) = b' := hc
  rw [this, hb', RingEquiv.apply_symm_apply]

theorem Fits.invdR {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) : C.InvdR := by
  intro K b hb
  set b' : P.R.BdR := T.eD.symm b with hb'
  have hfix : ∀ g : ↥(GK K), (P.PD K).actdR g b' = b' := by
    intro g
    rw [P.PD_actdR]
    apply T.eD.injective
    rw [T.actD, hb', RingEquiv.apply_symm_apply]
    exact hb g g.2
  obtain ⟨c, hc⟩ := (P.PD K).invdR b' hfix
  refine ⟨(c : Om l), c.2, ?_⟩
  rw [← hF.o]
  have : algebraMap (Om l) P.R.BdR (c : Om l) = b' := hc
  rw [this, hb', RingEquiv.apply_symm_apply]

theorem fits_inv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (C : Core l), Fits T C → C.InvB ∧ C.InvdR :=
  fun _ _ _ _ _ _ hF => ⟨hF.invB, hF.invdR⟩

end GlobalTheory.MemLoc

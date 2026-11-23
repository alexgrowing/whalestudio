import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrEqvEquivalence
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolPos

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
variable {D : D7} {X : HidaSetting D}

def frCls {Y : Full X} {u : D.what₂.Word} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (t : GTu Y u) :
    Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS) :=
  {G | GlobalTheory.DegAsm.FrEqv (F0 X u) Λ (Ft t) G}

def clsOm (Y : Full X) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (b : Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS)) : ℝ :=
  if h : ∃ t : GTu Y u, t.lam = Λ ∧ frCls Λ t = b then omT h.choose else 0

theorem frCls_eq_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E) {Y : Full X} {u : D.what₂.Word}
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (t t' : GTu Y u) :
    frCls Λ t = frCls Λ t' ↔ GlobalTheory.DegAsm.FrEqv (F0 X u) Λ (Ft t) (Ft t') := by
  have hE := (GlobalTheory.DegAsm.frEqv_invariants D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) (dI D) Λ).1
  constructor
  · intro h
    have : Ft t' ∈ frCls Λ t := by rw [h]; exact hE.refl _
    exact this
  · intro h
    ext G
    exact ⟨fun hG => hE.trans (hE.symm h) hG, fun hG => hE.trans h hG⟩

theorem clsOm_nonneg (Y : Full X) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E) (b : Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS)) : 0 ≤ clsOm Y u Λ b := by
  unfold clsOm
  split_ifs with h
  · exact ((GlobalTheory.DegAsm.WeightInf.main D.host.E (VS D).V (HV D) hK D.R.rS).2 _ _ _ _).1
  · exact le_rfl

theorem clsOm_frCls (hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E) {Y : Full X} {u : D.what₂.Word}
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (t : GTu Y u) (ht : t.lam = Λ) : clsOm Y u Λ (frCls Λ t) = omT t := by
  have hex : ∃ s : GTu Y u, s.lam = Λ ∧ frCls Λ s = frCls Λ t := ⟨t, ht, rfl⟩
  unfold clsOm
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  have hq := (frCls_eq_iff hK Λ _ _).1 h2
  have := ((GlobalTheory.DegAsm.frEqv_invariants D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) (dI D) Λ).2 _ _ hq).1
  unfold omT
  rw [h1, ht]
  exact this
end

end GlobalTheory.TypeAsm.PerRow

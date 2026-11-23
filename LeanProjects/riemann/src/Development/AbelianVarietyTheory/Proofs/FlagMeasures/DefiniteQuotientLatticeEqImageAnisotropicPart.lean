import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb

theorem lat0_eq_img_latIn_Ub (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (W : Submodule D.host.E (VS D).V)
    (e : GlobalTheory.RowsOrb.Ub X u ≃ₗ[D.host.E] W)
    (he : ∀ x : GlobalTheory.RowsOrb.Ub X u, ((e x : W) : (VS D).V) - ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ (GlobalTheory.TypeAsm.F0 X u).X)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    GlobalTheory.DegAsm.lat0 (GlobalTheory.TypeAsm.F0 X u) W.subtype Λ
      = GlobalTheory.Mass.Transp.img e (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ)) := by
  ext w
  rw [GlobalTheory.Mass.Transp.mem_img]
  have hd : ((e (e.symm w) : W) : (VS D).V) - (((e.symm w : GlobalTheory.RowsOrb.Ub X u) : GlobalTheory.RowsOrb.Wb X) : (VS D).V)
      ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X :=
    (le_sup_right : GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X ≤ _) (he (e.symm w))
  rw [LinearEquiv.apply_symm_apply] at hd
  have h1 : w ∈ GlobalTheory.DegAsm.lat0 (GlobalTheory.TypeAsm.F0 X u) W.subtype Λ ↔
      (w : (VS D).V) ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := Iff.rfl
  have h2 : e.symm w ∈ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ↔
      (((e.symm w : GlobalTheory.RowsOrb.Ub X u) : GlobalTheory.RowsOrb.Wb X) : (VS D).V)
        ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := Iff.rfl
  rw [h1, h2]
  constructor
  · intro h
    simpa using Submodule.sub_mem _ h hd
  · intro h
    simpa using Submodule.add_mem _ hd h

end GlobalTheory.RowsOrb

import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationDeterminesCharUnramifiedSplitPStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

namespace GlobalTheory.LastStep

theorem chars_unram : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (t : Tup c), t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) → ∀ (χz χS' χT : (AE D)ˣ →* Circle), IsWeilDatumO c.ψ _ _ χS' (χT * χz⁻¹) (t.kom (j + 1)) → IsWeilDatumO c.ψ _ _ χS' χT (t.omT j h) → ∀ x, x ∈ v.tP → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS' x ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT x := by
  intro D c v k _ _ _ _ ι o hS j h t hU hK χz χS' χT h1 h2 x hx
  obtain ⟨i, rfl⟩ := (hS.pre.tP x).1 hx
  have hpos : ∀ n, 0 < (c.X n).rank := fun n => by
    apply Nat.pos_of_ne_zero
    intro h0
    have P := o.Q n i
    revert P
    rw [h0]
    intro P
    exact P.fn_ne (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])
  have hV : 0 < (c.V (j + 1)).rank := by
    have := (c.jac j 0 h).d.rank_add
    have := hpos (j + 1)
    omega
  obtain ⟨χS₃, χT₃, hW₃, hu₃⟩ := hK (j + 1) (by omega)
  obtain ⟨χS₂, χT₂, hW₂, hu₂⟩ := hU.top j h
  refine ⟨?_, ?_⟩
  · exact (GlobalTheory.T.weilRepresentation_determines_charUnramified_splitPlace D k (o.p i) c.ψ _ _ χS₃ χT₃ χS' (χT * χz⁻¹) (t.kom (j + 1)) hW₃ h1).2 (hpos _) (hu₃ _ ((hS.pre.tP _).2 ⟨i, rfl⟩)).1
  · exact (GlobalTheory.T.weilRepresentation_determines_charUnramified_splitPlace D k (o.p i) c.ψ _ _ χS₂ χT₂ χS' χT (t.omT j h) hW₂ h2).1 hV (hu₂ _ ((hS.pre.tP _).2 ⟨i, rfl⟩)).2

end GlobalTheory.LastStep

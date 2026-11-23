import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

def SeedW (K : Ctx) (P : Pre) (f : Fr P) (F F₀ : IntermediateField ℚ ℂ) (px : PreX P) (S : Set ℕ) (L : IntermediateField ℚ ℂ) :
    Prop :=
  ∃ (B₀ : Base) (f₀ : Fr B₀.toPre) (T₀ : TwDat B₀) (w₀ : ColW B₀ f₀ T₀) (Z₀ : w₀.Lt) (hX₀ : B₀.fields.Ok) (Wt₀ : Set B₀.places.Pl)
    (z₀ : Dat (w₀.st Z₀) w₀.I hX₀ T₀ Wt₀), B₀.toPre = P ∧ HEq f₀ f ∧ B₀.KsC = F ∧ B₀.fixedCoefficientFieldInComplex = F₀ ∧ HEq w₀.px px ∧
      Pinned K B₀ f₀ T₀ w₀ ∧ GrpTrue Z₀.N f₀ ∧ GrpAt (w₀.st Z₀) w₀.I ∧ Fine z₀ ∧ HoldsL z₀.R z₀.F ∧
      (∀ v ∈ z₀.W1 (fun _ _ => 0), B₀.places.resChar v ∈ S) ∧ B₀.LLC ≤ L

def SeedBd : Prop :=
  EvG fun K => ∀ (P : Pre) (f : Fr P) (F F₀ : IntermediateField ℚ ℂ), ∃ (S : Finset ℕ) (S₂ : Finset ℂ),
    (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧ ∀ px : PreX P, SeedW K P f F F₀ px Set.univ ⊤ →
      SeedW K P f F F₀ px (S : Set ℕ) (IntermediateField.adjoin ℚ (S₂ : Set ℂ))

theorem SeedW.mono {K : Ctx} {P : Pre} {f : Fr P} {F F₀ : IntermediateField ℚ ℂ} {px : PreX P} {S S' : Set ℕ}
    {L L' : IntermediateField ℚ ℂ} (h : SeedW K P f F F₀ px S L) (hS : S ⊆ S') (hL : L ≤ L') : SeedW K P f F F₀ px S' L' := by
  obtain ⟨B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  exact ⟨B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, fun v hv => hS (a11 v hv), a12.trans hL⟩

theorem enl_of_fields {B₀ B : Base} (hP : B₀.toPre = B.toPre) (hKs : B₀.KsC = B.KsC) (hL0 : B₀.fixedCoefficientFieldInComplex = B.fixedCoefficientFieldInComplex)
    (hLL : B₀.LLC ≤ B.LLC) : Enl B₀ B := by
  refine ⟨hP.symm, ?_, ?_, ?_⟩
  · have := congrArg (fun F : IntermediateField ℚ ℂ => (F : Set ℂ)) hKs
    simp only [Base.KsC, IntermediateField.coe_map] at this
    exact this.symm
  · have := congrArg (fun F : IntermediateField ℚ ℂ => (F : Set ℂ)) hL0
    simp only [Base.fixedCoefficientFieldInComplex, IntermediateField.coe_map] at this
    exact this.symm
  · rintro _ ⟨x, rfl⟩
    exact (B.mem_LLC).1 (hLL ((B₀.mem_LLC).2 ⟨x, rfl⟩))

end GlobalTheory.Mem.R3.Rw

end

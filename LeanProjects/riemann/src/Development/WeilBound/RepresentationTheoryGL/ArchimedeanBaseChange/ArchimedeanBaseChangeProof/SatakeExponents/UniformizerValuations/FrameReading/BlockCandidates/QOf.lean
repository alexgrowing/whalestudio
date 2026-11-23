import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.CandOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.SqNe

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.BcB.F.BC

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
  {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T) (i : F₀.C.ι)
  {χ : Rd.ChAlg (fun x => F.g x i) (X F i) →⋆ₐ[ℂ] ℂ}

def Q : Prop := ∃ (i : F₀.C.ι) (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i)) (Pb : Pre E (n - F₀.C.a i))
  (D : Pre E n) (A : Type) (G : A × F.κ → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ),
  F₀.Cand F.d i s₁ s₂ Pa Pb D ∧ (∀ j, G j ∈ pairSpace s₁.space s₂.space) ∧
  (∀ j, OfLev F₀.Sec (F.d.lev (F₀.C.a i)) (F.d.lev₂ (F₀.C.a i)) (G j)) ∧
  (convF (F.B i).ν (F.ψ i (F.d.betaL _ (F₀.C.le i))))^[F.m] G ≠ 0 ∧
  (∀ τ lam, HasWeightAt π τ lam → ∑ k, D.m k τ = infOfWeight lam) ∧
  (∀ᶠ w : Pl E in cofinite, IsSplitAt w → D.SplitAt π w)

set_option maxHeartbeats 1000000 in
theorem q_of (hE : GlobalTheory.BCT.Unr E) (hn : 1 ≤ n) (hπ : IsAutRepU π) (h : F.Struct)
    (hχ : Chi (fun x => F.g x i) (X F i) (fun x => (F.ug x).p F.fam F.i₀) χ) (h2 : LimAt) (h3 : Ident) (h4 : PowNe)
    (h5 : PreOfTree) (h6 : JoinEx) (h7 : FG.LevRead) (h8 : FG.FRGood) (h9 : FG.FRWeight) : Q F := by
  obtain ⟨O⟩ := h2 hR E n hn π S T F₀ F h i χ hχ
  obtain ⟨ia, ib⟩ := h3 hR E n π S T F₀ F i χ hχ O
  obtain ⟨Pa, Pb, D, hC⟩ := cand_of F i O ia ib h5 h6
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := fun w hw => F.levOff.1 (Finset.mem_coe.2 (Finset.mem_union_left _ hw))
  have hl := fun j => (h7 E n F₀.Sec F.d (F₀.C.a i) (F₀.C.le i) F₀.hSec F.ok hP).2.2 _ _ _ (O.type j)
  have e := h4 E (F.B i) (F.β i) (F.m - 1) _ O.F (h.βok i).ψ (fun j => (hl j).1) (sq_ne F i _ rfl hχ O)
  rw [Nat.sub_add_cancel F.m_pos] at e
  exact ⟨i, O.s₁, O.s₂, Pa, Pb, D, _, O.F, hC, O.mem, hl, e, h9 hR E hE n hn π hπ S F₀ F.d i _ _ _ _ _ hC,
    h8 hR E hE n π hπ S T F₀ F i _ _ Pa Pb D hC.ctx _ O.F O.ne O.mem hl (eig_h F i _ rfl hχ O)⟩

end PositivityTheory.Rg.BcB.F.BC

end

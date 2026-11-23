import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PowNeOf

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

set_option maxHeartbeats 1000000 in
theorem cand_of (O : BO F i χ) (ia : ∀ τ, mOf O.χa τ = mOf (F₀.A i).χa τ) (ib : ∀ τ, mOf O.χb τ = mOf (F₀.A i).χb τ)
    (h5 : PreOfTree) (h6 : JoinEx) : ∃ Pa Pb D, F₀.Cand F.d i O.s₁ O.s₂ Pa Pb D := by
  obtain ⟨Pa, ta⟩ := h5 E _ O.s₁ O.good₁ O.untw₁ fun τ => ⟨_, O.inf₁ τ⟩
  obtain ⟨Pb, tb⟩ := h5 E _ O.s₂ O.good₂ O.untw₂ fun τ => ⟨_, O.inf₂ τ⟩
  obtain ⟨D, hJ⟩ := h6 E n _ _ F₀.μ F₀.e Pa Pb F₀.hμ (Nat.add_sub_of_le (F₀.C.le i))
  obtain ⟨j, hj⟩ := Function.ne_iff.1 O.ne
  refine ⟨Pa, Pb, D, ⟨O.good₁, O.good₂, O.untw₁, O.untw₂, ta, tb, hJ⟩, O.leaves₁, O.leaves₂, fun τ => ?_, fun τ => ?_,
    O.F j, O.mem j, hj, O.type j⟩
  · have := O.inf₁ τ
    rw [ia τ] at this
    exact this
  · have := O.inf₂ τ
    rw [ib τ] at this
    exact this

end PositivityTheory.Rg.BcB.F.BC

end

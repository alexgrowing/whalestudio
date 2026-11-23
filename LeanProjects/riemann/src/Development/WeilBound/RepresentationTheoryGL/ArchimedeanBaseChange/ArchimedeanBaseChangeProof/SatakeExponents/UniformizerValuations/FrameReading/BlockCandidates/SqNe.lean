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
theorem sq_ne (c : F.Γ → ℂ) (hc : c (.inl ()) = 1) (hχ : Chi (fun x => F.g x i) (X F i) c χ) (O : BO F i χ) :
    convF (F.B i).ν ((F.β i).sq (F.m - 1)).ψ O.F ≠ 0 := by
  have e := O.eigX
  intro h0
  rw [h0] at e
  refine smul_ne_zero (div_ne_zero hχ.2.2 (pow_ne_zero _ ?_)) O.ne e.symm
  exact ((hχ.2.1 (.inl ())).trans hc).trans_ne one_ne_zero

set_option maxHeartbeats 1000000 in
theorem eig_h (c : F.Γ → ℂ) (hc : c (.inl ()) = 1) (hχ : Chi (fun x => F.g x i) (X F i) c χ) (O : BO F i χ)
    (x : {w : Pl E // w ∈ F₀.Sec ∧ F.d.Good w} × ℕ × Bool) :
    convF (F.B i).ν (F.ψ i (F.d.hL _ (F₀.C.le i) x.1.1 x.2.1 x.2.2)) O.F = c (.inr (.inr x)) • O.F := by
  have e := O.eigFin (.inr (.inr x)) (F.ptL i (F.d.hL _ (F₀.C.le i) x.1.1 x.2.1 x.2.2)) rfl ⟨rfl, rfl, rfl, rfl, rfl⟩
  rw [hχ.2.1 (.inr (.inr x)), hχ.2.1 (.inl ()), hc, div_one] at e
  exact e

end PositivityTheory.Rg.BcB.F.BC

end

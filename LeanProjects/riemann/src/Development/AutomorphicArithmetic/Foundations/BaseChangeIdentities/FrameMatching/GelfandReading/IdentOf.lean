import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.GelfandReading.InfMatchOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PowNeOf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF PositivityTheory.Rg.BcB.F.borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.BaseChangeIdentities.GelfandReading

set_option maxHeartbeats 2000000 in
theorem ident_of (hD : DerVal) (hI : InfMatch) : BC.Ident := by
  intro hR E _ _ _ n π S T F₀ F i χ hχ O
  have e0 : (F.t₀ i).val O.χa O.χb = 1 := (O.eigArch (.inl ()) (F.t₀ i) rfl rfl).symm.trans (hχ.2.1 (.inl ()))
  have e1 : ∀ v s m side, (F.tD i v s m side).val O.χa O.χb = F.dval (i, v, s, m, side) := fun v s m side =>
    (O.eigArch (.inr (.inl (i, v, s, m, side))) (F.tD i v s m side) (if_pos rfl) rfl).symm.trans
      (hχ.2.1 (.inr (.inl (i, v, s, m, side))))
  have key := fun v s m => hD E _ _ _ _ _ _ _ _ (F₀.A i) F.κ (F.ψ i (F.d.eL _)) (F.ψ i (F.d.eL _))
    (PositivityTheory.Rg.BcB.F.sizeOf (F.ψ i (F.d.eL _))) (PositivityTheory.Rg.BcB.F.sizeOf (F.ψ i (F.d.eL _))) v s m O.χa O.χb
  refine ⟨fun τ => congrFun (hI E _ O.χa (F₀.A i).χa fun v s m _ _ => ?_) τ,
    fun τ => congrFun (hI E _ O.χb (F₀.A i).χb fun v s m _ _ => ?_) τ⟩
  · have h1 := e1 v s m false
    have h2 := (key v s m).1
    have h3 : F.tD i v s m false = (F₀.A i).pt (fun v' => if v' = v then [(s, m)] else []) (fun _ => []) (F.ψ i (F.d.eL _))
        (PositivityTheory.Rg.BcB.F.sizeOf (F.ψ i (F.d.eL _))) := by
      unfold RunFrame.tD
      congr 1 <;> funext v' <;> simp
    rw [h3] at h1
    have h4 := h2.symm.trans h1
    erw [e0] at h4
    simpa [RunFrame.dval, zVal] using h4
  · have h1 := e1 v s m true
    have h2 := (key v s m).2
    have h3 : F.tD i v s m true = (F₀.A i).pt (fun _ => []) (fun v' => if v' = v then [(s, m)] else []) (F.ψ i (F.d.eL _))
        (PositivityTheory.Rg.BcB.F.sizeOf (F.ψ i (F.d.eL _))) := by
      unfold RunFrame.tD
      congr 1 <;> funext v' <;> simp
    rw [h3] at h1
    have h4 := h2.symm.trans h1
    erw [e0] at h4
    simpa [RunFrame.dval, zVal] using h4

end UpperTheory.BaseChangeIdentities.GelfandReading

end

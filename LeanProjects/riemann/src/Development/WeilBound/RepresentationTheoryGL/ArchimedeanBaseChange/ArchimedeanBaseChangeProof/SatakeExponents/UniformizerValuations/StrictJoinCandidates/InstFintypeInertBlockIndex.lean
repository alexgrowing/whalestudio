import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.CompFixSAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.MemULOfSplit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocOk

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

open PositivityTheory.Rg.BcB.F

section

variable {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
  {π : Submodule ℂ (UA E n → ℂ)} {S : Finset (Pl E)}

abbrev inertBlockIndex (F₀ : Frame0 hR π S) : Type :=
  Σ i : F₀.C.ι, Σ s : {s : Finset (Fin (n / 2)) // LocData.admitted n (F₀.C.a i) s},
    {ex : Fin (F₀.C.a i) ⊕ Fin (n - F₀.C.a i) ≃ Fin n //
      (∀ j, ex (.inl j) = (symIdx n (F₀.C.a i % 2 = 1) s.1).orderEmbOfFin s.2.2.1 j) ∧
        ∀ j, ex (.inr j) = (symIdx n ((n - F₀.C.a i) % 2 = 1) s.1ᶜ).orderEmbOfFin s.2.2.2 j}

instance instFintypeInertBlockIndex (F₀ : Frame0 hR π S) : Fintype (inertBlockIndex F₀) := by
  haveI := F₀.C.ft
  unfold inertBlockIndex
  infer_instance

end

end PositivityTheory.Rg.BcB.F.FX

end

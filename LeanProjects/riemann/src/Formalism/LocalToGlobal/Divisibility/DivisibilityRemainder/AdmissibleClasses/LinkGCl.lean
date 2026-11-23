import Formalism.LocalToGlobal.ClassOfRecordOfChoice

noncomputable section

namespace Formalism.L2.DIV.LinkGCl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.L2.Top3

variable {eps : ℝ}

theorem gTiedF_of_sel (Fm : FamP eps) (s : Formalism.L2.TSelF Fm) : Formalism.L2.G.GroupCompatibilityFamily Fm :=
  Formalism.L2.gTiedF_of_C2S Fm (tied_families_of_choice s)

theorem admissible_tops_of_class {𝒜 : FamClass} {C0 : ℝ} (Fm : FamP eps) (hc : D3 C0 𝒜 Fm) : Formalism.MainNotions.G.Adm2F Fm :=
  admissible_tops_mertens Fm (topsF_of_chosenE Fm hc.2.1.choose_spec)

theorem linkG_closed (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) : Closed (D3 3 𝒜) fun Fm _ => LinkG Fm :=
  Formalism.L2.G.linkG_concrete5 (D3 3 𝒜)
    (Closed.of_class fun Fm _ hc => gTiedF_of_sel Fm (sel Fm (d3_a hc)))
    (Closed.of_class fun Fm _ hc => admissible_tops_of_class Fm hc)

theorem linkG_frame (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) :
    Closed (D3 3 𝒜) fun Fm _ => ∀ _ : D3 3 𝒜 Fm, Formalism.MainNotions.TuSize Fm → Formalism.MainNotions.DGamSize Fm → LinkG Fm := by
  obtain ⟨ε1, hε, H⟩ := linkG_closed 𝒜 sel
  refine ⟨ε1, hε, fun eps he hle => ?_⟩
  obtain ⟨K, hK⟩ := H eps he hle
  refine ⟨K, fun Fm CH hc => ?_⟩
  have h1 := hK Fm CH hc
  intro hl
  beta_reduce
  intro _ _ _
  exact h1 hl

end Formalism.L2.DIV.LinkGCl

end

import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ExistsIsCGBases

noncomputable section

namespace Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.KAat

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ}
  {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p} {S : StepIn M i hi G} {e : D.what₂.LL →+* G.Kf}

open Classical in

theorem finClasses_of (H : ∀ β, S.Core e β) (X : ChX S) : G.FinClasses := by
  intro a
  refine ⟨((Finset.univ : Finset (C.cls i)).filter fun c => ∃ L, G.P.IsLatTup L ∧ clsOf H a L = c).attach.image
    (fun c => ((Finset.mem_filter.1 c.2).2).choose), ?_, ?_⟩
  · intro L hL
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hL
    exact ((Finset.mem_filter.1 c.2).2).choose_spec.1
  · intro L hL
    have hc : clsOf H a L ∈ (Finset.univ : Finset (C.cls i)).filter fun c => ∃ L, G.P.IsLatTup L ∧ clsOf H a L = c :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, L, hL, rfl⟩
    refine ⟨_, Finset.mem_image.2 ⟨⟨clsOf H a L, hc⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    have spec := ((Finset.mem_filter.1 hc).2).choose_spec
    obtain ⟨_, γ, hγ⟩ := (clsOf_iff H X a a _ L spec.1 hL).1 spec.2
    exact ⟨γ, hγ⟩

end Formalism.MainNotions.G.ChF

end

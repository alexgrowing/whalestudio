import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ReadLimit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F

namespace PositivityTheory.Rg.BcB.F.F0

def xΩ₁ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] :=
  (hR E).choose_spec.choose_spec.choose
def xΩ₂ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] :=
  (hR E).choose_spec.choose_spec.choose_spec.choose

def WEx : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (μ : HChar E)
  (e : InfinitePlace E → ℤ) (lam : InfinitePlace E → DomWeight n) (C : Chain μ e lam)
  (A : ∀ i : C.ι, Arch E (C.a i) (n - C.a i) (C.l₁ i) (C.l₂ i) (C.μG (C.a i)) (C.μG (n - C.a i)) (C.νC (C.a i))
    (C.νC (n - C.a i))),
  ∃ W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ), (∀ N, FiniteDimensional ℂ (W N)) ∧
    ∀ (i : C.ι) (s₁ : Tr E (C.a i)) (s₂ : Tr E (n - C.a i)) Pa Pb (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
    s₁.AllLeaves (fun M V => M = 0 ∨ ∃ K', ∃ W' ∈ xΩ₁ hR E _ _ (A i).Ma (A i).Mb M, HasType K' W' V) →
    s₂.AllLeaves (fun M V => M = 0 ∨ ∃ K', ∃ W' ∈ xΩ₂ hR E _ _ (A i).Ma (A i).Mb M, HasType K' W' V) →
    ∀ j, HasKType (W (D.N j)) (D.V j)

theorem allLeaves_mono {E : Type} [Field E] [NumberField E] [IsCMField E]
    {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (h : ∀ M V, P M V → Q M V) :
    ∀ {N : ℕ} (t : Tr E N), t.AllLeaves P → t.AllLeaves Q
  | _, .leaf V _, hp => h _ V hp
  | _, .node t₁ t₂, hp => ⟨allLeaves_mono h t₁ hp.1, allLeaves_mono h t₂ hp.2⟩

theorem wEx_of (hJ : JoinType) : WEx := by
  intro hR E _ _ _ n μ e lam C A
  let Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)) := fun M =>
    ⋃ i : C.ι, (xΩ₁ hR E _ _ (A i).Ma (A i).Mb M ∪ xΩ₂ hR E _ _ (A i).Ma (A i).Mb M)
  have hx := (hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
  have hK : KTypes E Ω := by
    intro M
    refine ⟨Set.finite_iUnion fun i =>
      ((hx _ _ (A i).Ma (A i).Mb).2.2.1 M).1.union ((hx _ _ (A i).Ma (A i).Mb).2.2.2.1 M).1, ?_⟩
    intro W' hW'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hW'
    rcases hi with h | h
    · exact ((hx _ _ (A i).Ma (A i).Mb).2.2.1 M).2 W' h
    · exact ((hx _ _ (A i).Ma (A i).Mb).2.2.2.1 M).2 W' h
  obtain ⟨W, hW, hj⟩ := hJ E n μ Ω hK
  refine ⟨W, hW, fun i s₁ s₂ Pa Pb D hc h₁ h₂ =>
    hj (C.a i) (n - C.a i) (Nat.add_sub_of_le (C.le i)) s₁ s₂ Pa Pb D hc ?_ ?_⟩
  · exact allLeaves_mono (fun M V hv => hv.elim Or.inl fun ⟨K', W', hW', ht⟩ =>
      Or.inr ⟨K', W', Set.mem_iUnion.2 ⟨i, Or.inl hW'⟩, ht⟩) s₁ h₁
  · exact allLeaves_mono (fun M V hv => hv.elim Or.inl fun ⟨K', W', hW', ht⟩ =>
      Or.inr ⟨K', W', Set.mem_iUnion.2 ⟨i, Or.inr hW'⟩, ht⟩) s₂ h₂

end PositivityTheory.Rg.BcB.F.F0

end

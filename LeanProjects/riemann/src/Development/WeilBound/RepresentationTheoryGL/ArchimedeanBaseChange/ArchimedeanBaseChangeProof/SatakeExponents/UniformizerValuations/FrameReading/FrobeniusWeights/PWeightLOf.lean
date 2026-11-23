import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.WeightLOf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.FG

theorem mOf_infOf_embedding {E : Type} [Field E] [NumberField E] {n : ℕ} (l : InfinitePlace E → DomWeight n)
    (v : InfinitePlace E) :
    mOf (fun v => PositivityTheory.RgBcC.infOf (l v).w) v.embedding = infOfWeight (l v) := by
  unfold mOf infOfWeight PositivityTheory.RgBcC.infOf
  simp only [InfinitePlace.mk_embedding, decide_true, if_true, one_mul]
  congr 1
  funext k
  rw [add_sub_assoc]

theorem space_ne_bot_of_pair {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
    {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)} (h : ∃ G ∈ pairSpace U₁ U₂, G ≠ 0) :
    U₁ ≠ ⊥ ∧ U₂ ≠ ⊥ := by
  obtain ⟨G, hG, hG0⟩ := h
  constructor
  · rintro rfl
    apply hG0
    have : pairSpace (⊥ : Submodule ℂ (Sm E a)) U₂ = ⊥ := by
      unfold pairSpace
      rw [Submodule.span_eq_bot]
      rintro F ⟨φ₁, hφ₁, φ₂, -, rfl⟩
      rw [Submodule.mem_bot] at hφ₁
      subst hφ₁
      funext x
      simp
    rw [this, Submodule.mem_bot] at hG
    exact hG
  · rintro rfl
    apply hG0
    have : pairSpace U₁ (⊥ : Submodule ℂ (Sm E b)) = ⊥ := by
      unfold pairSpace
      rw [Submodule.span_eq_bot]
      rintro F ⟨φ₁, -, φ₂, hφ₂, rfl⟩
      rw [Submodule.mem_bot] at hφ₂
      subst hφ₂
      funext x
      simp
    rw [this, Submodule.mem_bot] at hG
    exact hG

theorem weightLOf_holds : WeightLOf := by
  intro hIT hReg hJI hTI hWJ E _ _ _ hU n hn π hπ μ e hμ lam hw a b l₁ l₂ hsum s₁ s₂ Pa Pb D hC h₁ h₂ hex τ lam' hτ
  obtain ⟨hne₁, hne₂⟩ := space_ne_bot_of_pair hex
  rw [hJI E n a b (μ ^ b) (μ ^ a) Pa Pb D hC.join τ,
    hTI hIT E a s₁ Pa τ _ hC.g₁ hC.u₁ hC.t₁ hne₁ (h₁ τ),
    hTI hIT E b s₂ Pb τ _ hC.g₂ hC.u₂ hC.t₂ hne₂ (h₂ τ)]
  refine hWJ E hU n a b μ e π lam (mOf fun v => PositivityTheory.RgBcC.infOf (l₁ v).w)
    (mOf fun v => PositivityTheory.RgBcC.infOf (l₂ v).w) hn hμ hπ hw (hReg E a l₁).1 (hReg E b l₂).1 ?_ τ lam' hτ
  intro v
  rw [mOf_infOf_embedding, mOf_infOf_embedding]
  exact hsum v

end PositivityTheory.Rg.BcB.F.FG

end

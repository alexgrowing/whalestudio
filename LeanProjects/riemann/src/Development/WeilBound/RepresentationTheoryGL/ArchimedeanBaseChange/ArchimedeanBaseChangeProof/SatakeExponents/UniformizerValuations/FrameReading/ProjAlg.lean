import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupExOf

noncomputable section

namespace PositivityTheory.Rg.BcB.F.Rd

variable {ι : Type} {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type}

def blockEvaluation (s : ι) : Prod' H d →⋆ₐ[ℂ] (H s →L[ℂ] H s) where
  toFun a := a.1 s
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

theorem projAdjoin (gen : Γ → Prod' H d) (s : ι) (X : H s →L[ℂ] H s) :
    StarAlgebra.adjoin ℂ (Set.range (fun a : StarAlgebra.adjoin ℂ (Set.range gen) => (a : Prod' H d).1 s) ∪ {X}) =
      StarAlgebra.adjoin ℂ (Set.range (fun x => (gen x).1 s) ∪ {X}) := by
  apply le_antisymm
  · apply StarAlgebra.adjoin_le
    rintro y (⟨a, rfl⟩ | hy)
    · have hmem : blockEvaluation (H := H) (d := d) s (a : Prod' H d) ∈
          StarSubalgebra.map (blockEvaluation (H := H) (d := d) s) (StarAlgebra.adjoin ℂ (Set.range gen)) :=
        StarSubalgebra.mem_map.2 ⟨a, a.2, rfl⟩
      rw [StarAlgHom.map_adjoin] at hmem
      have hle : StarAlgebra.adjoin ℂ (⇑(blockEvaluation (H := H) (d := d) s) '' Set.range gen) ≤
          StarAlgebra.adjoin ℂ (Set.range (fun x => (gen x).1 s) ∪ {X}) := by
        apply StarAlgebra.adjoin_mono
        rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
        exact Or.inl ⟨x, rfl⟩
      exact hle hmem
    · exact StarAlgebra.subset_adjoin ℂ _ (Or.inr hy)
  · apply StarAlgebra.adjoin_mono
    rintro y (⟨x, rfl⟩ | hy)
    · exact Or.inl ⟨⟨gen x, StarAlgebra.subset_adjoin ℂ _ ⟨x, rfl⟩⟩, rfl⟩
    · exact Or.inr hy

end PositivityTheory.Rg.BcB.F.Rd

end

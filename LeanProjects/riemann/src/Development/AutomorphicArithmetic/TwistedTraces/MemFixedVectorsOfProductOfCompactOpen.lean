import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

private theorem prod_keep {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Y : Submodule ℂ H) :
    ∀ l : List (H →L[ℂ] H), (∀ a ∈ l, ∀ v ∈ Y, a v ∈ Y) → ∀ v, (v ∈ Y ∨ ∃ a ∈ l, ∀ v, a v ∈ Y) → l.prod v ∈ Y
  | [], _, v, h => by simpa using h
  | a :: l, hl, v, h => by
    rw [List.prod_cons]
    show a (l.prod v) ∈ Y
    have ih := prod_keep Y l (fun b hb => hl b (List.mem_cons_of_mem _ hb)) v
    rcases h with h | ⟨b, hb, h⟩
    · exact hl a List.mem_cons_self _ (ih (Or.inl h))
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact h _
      · exact hl a List.mem_cons_self _ (ih (Or.inr ⟨b, hb, h⟩))

theorem UpperTheory.mem_fixedVectors_of_product_of_compactOpen :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : ∀ i, UnitaryRep (G i) H) (Z : Submodule ℂ H) (L : ∀ i, Subgroup (G i)) (T : Fin r → H →L[ℂ] H), (∀ i v, T i v ∈ fixU (π i) (L i)) → (∀ i, ∀ v ∈ Z, T i v ∈ Z) → (∀ i j, i ≠ j → ∀ h v, T i (π j h v) = π j h (T i v)) → ∀ v ∈ Z, (List.ofFn T).prod v ∈ (Z ⊓ ⨅ i, fixU (π i) (L i)) := by
  intro r G _ _ _ _ _ _ H _ _ _ π Z L T h1 h2 h3 v hv
  have k1 : ∀ i j, ∀ v ∈ fixU (π j) (L j), T i v ∈ fixU (π j) (L j) := fun i j v hv u hu => by
    by_cases e : i = j
    · subst e; exact h1 i v u hu
    · rw [← h3 i j e, hv u hu]
  refine Submodule.mem_inf.2 ⟨?_, Submodule.mem_iInf _ |>.2 fun j => ?_⟩
  · exact prod_keep Z _ (fun a ha => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha; exact h2 i) v (Or.inl hv)
  · exact prod_keep _ _ (fun a ha => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha; exact k1 i j) v
      (Or.inr ⟨T j, List.mem_ofFn.2 ⟨j, rfl⟩, h1 j⟩)

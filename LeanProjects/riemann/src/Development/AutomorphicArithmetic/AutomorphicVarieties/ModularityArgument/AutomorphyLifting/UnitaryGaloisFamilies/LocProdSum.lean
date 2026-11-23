import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TotalReciprocity

open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem locProd_sum {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {ε : EpsFamily A} (L : LawsV a ha ε rc) :
    ∀ {c n : ℕ} {N : Fin c → ℕ} (hn : ∑ i, N i = n) (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
      (τ : SmIrr (GL (Fin n) (w.adicCompletion E))), Nonempty (τ.ρ.Equiv (locProd hn w σ)) →
      rc (cl τ) = sumList (List.ofFn fun i => rc (cl (σ i))) := by
  intro c
  induction c with
  | zero =>
    intro n N hn σ τ e
    obtain rfl : n = 0 := by simpa using hn.symm
    obtain ⟨e⟩ := e
    obtain ⟨φ⟩ := SupportRing.nonempty_equiv_unit (k := w.adicCompletion E) (stdBlocks N hn) fun i => (σ i).ρ
    have h1 := L.det 0 1 isSmoothChar_one
    simp only [List.range_zero, List.map_nil] at h1
    rw [List.ofFn_zero]
    refine (congrArg rc (IrrGL.of_eq_of.2 ⟨e.trans φ⟩)).trans h1
  | succ s ih =>
    intro n N hn σ τ e
    obtain rfl : n = N 0 + ∑ i : Fin s, N i.succ := hn.symm.trans (Fin.sum_univ_succ N)
    obtain ⟨e⟩ := e
    obtain ⟨E₁⟩ := MultiIrr.nonempty_prod₂_equiv_multiProd_succ (k := w.adicCompletion E) N hn fun i => (σ i).ρ
    have hs : IsSmooth (multiProd (stdBlocks (fun i : Fin s => N i.succ) rfl) fun i : Fin s => (σ i.succ).ρ) :=
      isSmooth_parInd _ _
    have hi := GlobalTheory.T.isIrreducible_second_factor_of_irreducible_product _ _ _ _ _ _ (σ 0).ρ _ τ.ρ (σ 0).smooth (σ 0).irred hs τ.irred ⟨e.trans E₁.symm⟩
    let σ' : SmIrr (GL (Fin (∑ i : Fin s, N i.succ)) (w.adicCompletion E)) := ⟨_, _, hs, hi⟩
    have h1 := L.prod (N 0) _ (ParLaws.toRep (σ 0)) (ParLaws.toRep σ') (ParLaws.toRep τ) ⟨e.trans E₁.symm⟩
    have h2 := ih (N := fun i : Fin s => N i.succ) rfl (fun i => σ i.succ) σ' ⟨.refl _⟩
    rw [List.ofFn_succ]
    exact h1.trans (congrArg _ h2)

theorem UpperTheory.V.Z.Win.Gu.prodT :
    HypothesesH → ExtraV → ProdT := by
  intro _ X E Ω _ _ _ _ _ n c N hn w σ _ τ e A h rc hrc
  obtain ⟨a, ha, ε, L⟩ := X E Ω A w h rc hrc
  exact locProd_sum L hn σ τ e

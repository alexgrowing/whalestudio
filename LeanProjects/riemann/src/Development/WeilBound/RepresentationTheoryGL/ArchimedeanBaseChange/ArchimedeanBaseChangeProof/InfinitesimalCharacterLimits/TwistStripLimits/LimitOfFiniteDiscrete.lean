import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.CaseB

noncomputable section

open NumberField MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem caseB (hTB : TwBound) (hNE : NodeEmb) (hG : Graft) (hTS : TwShift) (hTr : TrStable) {N : ℕ}
    {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)}
    {Ω Ωb : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))} {Θ Θb : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))}
    (hΩb : KTypes E Ωb) (hΘb : Levels E Θb)
    (hBTK : ∀ (r s : ℕ) (h : r + s = N) (V : Submodule ℂ (Sm E (r + s))) (V₁ : Submodule ℂ (Sm E r))
      (V₂ : Submodule ℂ (Sm E s)) (z₁ z₂ : ℂ), IsDiscrete V → IsDiscrete V₁ → IsDiscrete V₂ →
      HasType (h ▸ K) (h ▸ W) V → Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂)) →
      (∃ K' ∈ Θb r, ∃ W' ∈ Ωb r, HasType K' W' V₁) ∧ (∃ K' ∈ Θb s, ∃ W' ∈ Ωb s, HasType K' W' V₂))
    (hIH : ∀ M < N, ∀ W' ∈ Ωb M, ∀ K' ∈ Θb M, Seq M W' K' Ω Θ)
    {R : ℝ} (hRep : RepAll E) {V : ℕ → Submodule ℂ (Sm E N)}
    (hVd : ∀ k, IsDiscrete (V k)) (hVt : ∀ k, HasType K W (V k)) (hVb : ∀ k, InfBdd R (V k))
    (hsmall : ∀ ε > 0, ∀ᶠ k in atTop, ¬ Gap ε (V k)) : Concl Ω Θ V := by
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.1 (hsmall 1 one_pos)
  refine concl_subseq (ψ := fun k => k + k₁) (fun a b h => by simpa using h) ?_
  refine caseB' hTB hNE hG hTS hTr hΩb hΘb hBTK hIH hRep (fun k => hVd _) (fun k => hVt _) (fun k => hVb _)
    (fun k => ?_) (fun ε hε => (tendsto_add_atTop_nat k₁).eventually (hsmall ε hε))
  by_contra hcon
  apply hk₁ (k + k₁) (Nat.le_add_left _ _)
  intro r hr hrN c hc
  exact (hcon ⟨r, hr, hrN, c, hc⟩).elim

variable (E) in

def Q (N : ℕ) : Prop :=
  ∀ W : Submodule ℂ (Kinf E N → ℂ), FiniteDimensional ℂ W →
  ∃ Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)), KTypes E Ω ∧
  ∀ K : Subgroup (GL (Fin N) (Af E)), IsOpen (K : Set (GL (Fin N) (Af E))) →
  ∃ Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))), Levels E Θ ∧ Seq N W K Ω Θ

theorem q_all (hFD : FinDisc) (hBT : BlockTypes) (hTB : TwBound) (hNE : NodeEmb) (hG : Graft) (hTS : TwShift)
    (hTr : TrStable) (N : ℕ) : Q E N := by
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro W hW
  obtain ⟨Ωb, hΩb, hBT'⟩ := hBT E N W hW
  have hI1 : ∀ (M' : ℕ) (W' : Submodule ℂ (Kinf E M' → ℂ)), ∃ Ω' : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)),
      M' < N → FiniteDimensional ℂ W' → KTypes E Ω' ∧ ∀ K' : Subgroup (GL (Fin M') (Af E)),
        IsOpen (K' : Set (GL (Fin M') (Af E))) → ∃ Θ' : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))),
          Levels E Θ' ∧ Seq M' W' K' Ω' Θ' := by
    intro M' W'
    by_cases h : M' < N ∧ FiniteDimensional ℂ W'
    · obtain ⟨Ω', h1, h2⟩ := IH M' h.1 W' h.2
      exact ⟨Ω', fun _ _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => ∅, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose ΩI hΩI using hI1
  refine ⟨fun M => {W' | ∃ h : N = M, W' = h ▸ W} ∪ ⋃ M' ∈ Set.Iio N, ⋃ W' ∈ Ωb M', ΩI M' W' M,
    fun M => ⟨?_, ?_⟩, fun K hK => ?_⟩
  · refine Set.Finite.union ?_ ((Set.finite_Iio N).biUnion fun M' hM' => (hΩb M').1.biUnion fun W' hW' =>
      ((hΩI M' W' hM' ((hΩb M').2 W' hW')).1 M).1)
    refine Set.Subsingleton.finite ?_
    rintro _ ⟨h₁, rfl⟩ _ ⟨h₂, rfl⟩
    rfl
  · rintro W' (⟨h, rfl⟩ | hW')
    · subst h
      exact hW
    · simp only [Set.mem_iUnion] at hW'
      obtain ⟨M', hM', W'', hW'', hmem⟩ := hW'
      exact ((hΩI M' W'' hM' ((hΩb M').2 W'' hW'')).1 M).2 W' hmem
  obtain ⟨Θb, hΘb, hBTK⟩ := hBT' K hK
  have hI2 : ∀ (M' : ℕ) (W' : Submodule ℂ (Kinf E M' → ℂ)) (K' : Subgroup (GL (Fin M') (Af E))),
      ∃ Θ' : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))), M' < N → FiniteDimensional ℂ W' →
        IsOpen (K' : Set (GL (Fin M') (Af E))) → Levels E Θ' ∧ Seq M' W' K' (ΩI M' W') Θ' := by
    intro M' W' K'
    by_cases h : M' < N ∧ FiniteDimensional ℂ W' ∧ IsOpen (K' : Set (GL (Fin M') (Af E)))
    · obtain ⟨Θ', h1, h2⟩ := (hΩI M' W' h.1 h.2.1).2 K' h.2.2
      exact ⟨Θ', fun _ _ _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => ∅, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose ΘI hΘI using hI2
  refine ⟨fun M => {K' | ∃ h : N = M, K' = h ▸ K} ∪ ⋃ M' ∈ Set.Iio N, ⋃ W' ∈ Ωb M', ⋃ K' ∈ Θb M', ΘI M' W' K' M,
    fun M => ⟨?_, ?_⟩, ?_⟩
  · refine Set.Finite.union ?_ ((Set.finite_Iio N).biUnion fun M' hM' => (hΩb M').1.biUnion fun W' hW' =>
      (hΘb M').1.biUnion fun K' hK' => ((hΘI M' W' K' hM' ((hΩb M').2 W' hW') ((hΘb M').2 K' hK')).1 M).1)
    refine Set.Subsingleton.finite ?_
    rintro _ ⟨h₁, rfl⟩ _ ⟨h₂, rfl⟩
    rfl
  · rintro K' (⟨h, rfl⟩ | hK')
    · subst h
      exact hK
    · simp only [Set.mem_iUnion] at hK'
      obtain ⟨M', hM', W'', hW'', K'', hK'', hmem⟩ := hK'
      exact ((hΘI M' W'' K'' hM' ((hΩb M').2 W'' hW'') ((hΘb M').2 K'' hK'')).1 M).2 K' hmem
  intro R hN hRep V hVd hVt hVb
  by_cases hA : ∃ ε > 0, ∃ᶠ k in atTop, Gap ε (V k)
  · obtain ⟨ε, hε, hfr⟩ := hA
    exact caseA hFD hN hK hW (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) hRep hVd hVt hVb hε hfr
  · have hB : ∀ ε > 0, ∀ᶠ k in atTop, ¬ Gap ε (V k) := fun ε hε =>
      Filter.not_frequently.1 fun h => hA ⟨ε, hε, h⟩
    refine caseB hTB hNE hG hTS hTr hΩb hΘb hBTK ?_ hRep hVd hVt hVb hB
    intro M' hM' W' hW' K' hK'
    refine seq_mono (hΘI M' W' K' hM' ((hΩb M').2 W' hW') ((hΘb M').2 K' hK')).2 (fun M x hx => ?_)
      (fun M x hx => ?_)
    · refine Or.inr ?_
      simp only [Set.mem_iUnion]
      exact ⟨M', hM', W', hW', hx⟩
    · refine Or.inr ?_
      simp only [Set.mem_iUnion]
      exact ⟨M', hM', W', hW', K', hK', hx⟩

theorem limit_of_finite_discrete (hFD : FinDisc) (hBT : BlockTypes) (hTB : TwBound) (hNE : NodeEmb) (hG : Graft) (hTS : TwShift)
    (hTr : TrStable) : Lim5 := by
  intro E _ _ _ N W hW
  obtain ⟨Ω, hΩ, h⟩ := q_all hFD hBT hTB hNE hG hTS hTr N W hW
  refine ⟨Ω, hΩ, fun K hK => ?_⟩
  obtain ⟨Θ, hΘ, hS⟩ := h K hK
  refine ⟨Θ, hΘ, ?_⟩
  intro _ _ μ _ R hN hRep V hVd hVt hVb
  obtain ⟨φ, t, t₀, hφ, hp₀, hz₀, hp, hs, hl, htw, he⟩ := hS R hN hRep V hVd hVt hVb
  exact ⟨φ, t, t₀, hφ, good_of_pos hp₀ hz₀, fun k => disc_of_pos (hp k), hs,
    allLeaves_and (allLeaves_pos hp₀) hl, htw, he⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

end

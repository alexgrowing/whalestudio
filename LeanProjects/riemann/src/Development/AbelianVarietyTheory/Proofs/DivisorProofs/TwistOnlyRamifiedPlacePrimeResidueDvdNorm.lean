import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.SqTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem card_quot_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    Nat.card (𝓞 D.host.E ⧸ P'.asIdeal) = Nat.card (𝓞 D.host.E ⧸ P.asIdeal) := by
  let σ : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv (starRingAut : D.host.E ≃+* D.host.E)
  have hle : P.asIdeal.map σ ≤ P'.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    obtain ⟨c', h1, h2⟩ := h c hc
    have e : σ c = c' := RingOfIntegers.ext h2.symm
    show σ c ∈ P'.asIdeal
    rw [e]; exact h1
  have hmax : (P.asIdeal.map σ).IsMaximal := Ideal.map_isMaximal_of_equiv σ (hp := P.isMaximal)
  have e : P'.asIdeal = P.asIdeal.map σ := (hmax.eq_of_le P'.isPrime.ne_top hle).symm
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal P'.asIdeal σ e).toEquiv).symm

theorem twist_ram_prime_dvd_Qn : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ → ∀ (i j : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)), ¬ (Lc.xiH t).UnrAt w → (nuH G μ₀ i j).UnrAt w → ∃ q : ℕ, q.Prime ∧ Nat.card (𝓞 D.host.E ⧸ w.asIdeal) = q ∧ q ∣ GlobalTheory.SqTop.Qn G t ∧ ∃ w' ∈ GlobalTheory.FunObj.locPl G t, Ideal.absNorm w'.asIdeal = q := by
  classical
  intro D T Lc sc G μ₀ hL i j t w hxi hnu

  have hS0 : w.under (𝓞 D.host.F) ∉ G.pl.S0 := by
    intro hS
    have hv := (Model.isValChar_nu hL G i j (s := 0) (Nat.zero_le _)).1
    have hE := hv.2.2.2 (w.under (𝓞 D.host.F)) w rfl
    have hexp := (hE.2 (Finset.notMem_empty _) 0).1 ((Formalism.L2.Host.HChar.unrAt_iff _ _).1 hnu)
    rw [Model.expIn_condF, if_pos hS, condExp] at hexp
    split_ifs at hexp <;> omega

  obtain ⟨PP, hPP, hw⟩ : ∃ PP ∈ Lc.Q t, w = PP ∨ Formalism.IndefR.Lev.IsConjPl PP w := by
    rcases (hL.Q_ram t w).1 hxi with h | ⟨PP, h, hc⟩
    · exact ⟨w, h, Or.inl rfl⟩
    · exact ⟨PP, h, Or.inr hc⟩
  have hunder : PP.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := by
    rcases hw with rfl | hc
    · rfl
    · exact GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc
  have hW0 : PP ∉ G.pl.W0 := by
    intro h
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
    apply hS0
    rw [← hunder, G.pl.under_w hv]
    exact hv
  have hloc : PP ∈ GlobalTheory.FunObj.locPl G t := Finset.mem_union_right _ hPP
  have htw : PP ∈ twPl G t := Finset.mem_filter.2 ⟨hloc, hW0⟩
  obtain ⟨⟨q, hq, hcard, -, -⟩, -⟩ := hL.Q_pl t PP hPP
  have hnorm : Ideal.absNorm PP.asIdeal = q := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hcard]
  refine ⟨q, hq, ?_, ?_, PP, hloc, hnorm⟩
  · rcases hw with rfl | hc
    · exact hcard
    · rw [card_quot_of_isConjPl hc]; exact hcard
  · rw [← hnorm]
    exact Finset.dvd_prod_of_mem _ htw

end GlobalTheory.SqTop

import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotDvdDiscrIffRamificationIdx
open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.BadPlaceExp

theorem under_eq_of_isConjPl {D : D7} {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl w w') :
    w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) := by
  have le : (w.under (𝓞 D.host.F)).asIdeal ≤ (w'.under (𝓞 D.host.F)).asIdeal := by
    intro c hc
    obtain ⟨c', h1, h2⟩ := h _ hc
    have hs : star ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) =
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) := by
      letI := D.host.isCMField_hostE
      exact IsCMField.complexConj_apply_eq_self D.host.E (c : D.host.F)
    have : c' = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c := RingOfIntegers.ext (h2.trans hs)
    show algebraMap _ _ c ∈ w'.asIdeal
    rwa [← this]
  exact HeightOneSpectrum.ext ((w.under (𝓞 D.host.F)).isMaximal.eq_of_le (w'.under (𝓞 D.host.F)).isPrime.ne_top le)

theorem main : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ → IsBaseCond (condF G.pl) → ∀ (i j : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)), ¬ (Lc.xiH t).UnrAt w → ¬ (nuH G μ₀ i j).UnrAt w → ∃ q : ℕ, q.Prime ∧ Nat.card (𝓞 D.host.E ⧸ w.asIdeal) = q ∧ (q : 𝓞 D.host.E) ∉ w.asIdeal ^ 2 ∧ ExpAt (nuH G μ₀ i j) w 2 := by
  intro D T Lc sc G μ₀ hL hB i j t w hx hn
  have hm := Lc.C.isMu0 j
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have e : nuH G μ₀ i j = Lc.C.mu0 j / G.ch.chiH (D.R.m - i) := by
    rw [nuH, hL.xi_base, mul_one]
  have hE : ExpAt (nuH G μ₀ i j) w (expIn (condF G.pl) (w.under (𝓞 D.host.F))) := by
    rw [e]
    refine Model.expAt_div G a1 a2 hm.tame (fun Q hQ => hm.unr Q fun k hk => hQ ((S1_mem_OmF D).2 ?_)) w
    have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ Q.asIdeal
      rw [map_natCast]; exact hk
    fin_cases k
    · exact Or.inl this
    · exact Or.inr (Or.inl this)
  have hS0 : w.under (𝓞 D.host.F) ∈ G.pl.S0 := by
    by_contra h
    rw [Model.expIn_condF, if_neg h] at hE
    exact hn ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 ((hE 0).2 le_rfl))
  have hv0 : w.under (𝓞 D.host.F) ≠ G.pl.v0 := by
    rcases (hL.Q_ram t w).1 hx with h | ⟨PP', hP', hc⟩
    · exact G.pl.levelPlace_ne_basePlace t w h
    · rw [← under_eq_of_isConjPl hc]; exact G.pl.levelPlace_ne_basePlace t PP' hP'
  have hc2 : condExp G.pl (w.under (𝓞 D.host.F)) = 2 := by rw [condExp, if_neg hv0]
  have h2 : expIn (condF G.pl) (w.under (𝓞 D.host.F)) = 2 := by
    rw [Model.expIn_condF, if_pos hS0, hc2]
  rw [h2] at hE
  have hdvd : (w.under (𝓞 D.host.F)).asIdeal ∣ condF G.pl :=
    (dvd_pow_self _ (by rw [hc2]; norm_num)).trans (Finset.dvd_prod_of_mem _ hS0)
  obtain ⟨-, -, hb⟩ := hB
  obtain ⟨-, -, l, hl, -, hlv, hdisc, hnorm⟩ := hb _ hdvd
  have hlw : (l : 𝓞 D.host.E) ∈ w.asIdeal := by
    have : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (l : 𝓞 D.host.F) ∈ w.asIdeal := hlv
    rwa [map_natCast] at this
  refine ⟨l, hl, ?_, ?_, hE⟩
  · rw [← hnorm w hlw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · exact GlobalTheory.Mem.RaySplit.not_mem_sq hl hlw
      ((GlobalTheory.Mem.RaySplit.not_dvd_discr_iff_ramificationIdx D.host.E hl).1 hdisc _ w.isPrime hlw)

end GlobalTheory.BadPlaceExp

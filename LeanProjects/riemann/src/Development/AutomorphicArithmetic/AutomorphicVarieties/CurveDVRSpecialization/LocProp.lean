import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree

open UpperTheory.V.Pr in
private theorem UpperTheory.V.Pr.exists_prime_qdim {R : Type} [CommRing R] (J : Ideal R) (n : ℕ)
    (h : (n : WithBot ℕ∞) ≤ qdim J) :
    ∃ I : PrimeSpectrum R, J ≤ I.asIdeal ∧ (n : WithBot ℕ∞) ≤ qdim I.asIdeal := by
  rw [qdim, ringKrullDim_quotient] at h
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp h
  refine ⟨(l 0).1, fun y hy => (l 0).2 hy, ?_⟩
  rw [qdim, ringKrullDim_quotient]
  apply Order.le_krullDim_iff.mpr
  refine ⟨{ length := l.length, toFun := fun i => ⟨(l i).1, ?_⟩, step := fun i => ?_ }, hl⟩
  · rw [PrimeSpectrum.mem_zeroLocus]
    exact (show (l 0).1.asIdeal ≤ (l i).1.asIdeal from l.monotone (Fin.zero_le i))
  · exact l.step i

theorem UpperTheory.V.Pr.locProp :
    UpperTheory.V.Pr.LocProp := by
  intro R _ _ L hL I hIg hIti hIbig P hPti hPmin
  have hW : ∀ p ∈ L.Nice, (∃ P ≤ p, P ∈ L.TI ∧ P ∈ L.Good) →
      ∀ P' ≤ p, P' ∈ L.TI → P' ∈ L.Good := by
    intro p hp hS
    rcases hL.nice_type p hp with hpt | hpt
    · obtain ⟨Q, hQp, _, hQg⟩ := hS
      have hpg := hL.good_up Q p hQp hQg
      intro P' hP' _
      exact hL.p1 p hp hpt hpg P' hP'
    · exact hL.p23 p hp hpt p Relation.ReflTransGen.refl hS
  let Inv : PrimeSpectrum R → Prop := fun Q =>
    (Q ∈ L.TI → Q ∈ L.Good) ∧ ((Q ∈ L.TI ∧ Q ∈ L.Good) ∨
      (Q ∈ L.Thick ∧ ∃ p0 ∈ L.Nice, p0 ∈ L.TE ∧ (∃ P ≤ p0, P ∈ L.TI ∧ P ∈ L.Good) ∧
        ∃ p ∈ L.Nice, p ∈ L.TE ∧ Q ≤ p ∧ Relation.ReflTransGen L.Link p0 p))
  have K : ∀ Q, L.Comp Q → Inv Q → ∀ M : PrimeSpectrum R, Q ≤ M →
      (L.D1 : WithBot ℕ∞) ≤ qdim M.asIdeal →
      ∃ p ∈ L.Nice, M ≤ p ∧ ∀ P' ≤ p, P' ∈ L.TI → P' ∈ L.Good := by
    intro Q hQc hQ M hQM hM
    rcases hQ.2 with ⟨hti, hg⟩ | ⟨hth, p0, hp0n, hp0e, hS, p, hpn, hpe, hQp, hrt⟩
    · have hMg := hL.good_up Q M hQM hg
      obtain ⟨p, hpn, hMp⟩ := hL.nice_good M hMg hM
      exact ⟨p, hpn, hMp, hW p hpn ⟨Q, le_trans hQM hMp, hti, hg⟩⟩
    · obtain ⟨p', hp'n, hp'e, hMp'⟩ := hL.nice_thick Q hth hQc M hQM hM
      exact ⟨p', hp'n, hMp', hL.p23 p0 hp0n hp0e p'
        (hrt.tail ⟨hpn, hpe, hp'n, hp'e, Q, hth, hQc, hQp, le_trans hQM hMp'⟩) hS⟩
  have step : ∀ Q Q', L.Adj Q Q' → Inv Q → Inv Q' := by
    intro Q Q' hadj hQ
    obtain ⟨hQc, hQ'c, hbig⟩ := hadj
    obtain ⟨M, hJM, hM⟩ := UpperTheory.V.Pr.exists_prime_qdim _ _ hbig
    have hQM : Q ≤ M := show Q.asIdeal ≤ M.asIdeal from le_trans le_sup_left hJM
    have hQ'M : Q' ≤ M := show Q'.asIdeal ≤ M.asIdeal from le_trans le_sup_right hJM
    obtain ⟨p, hpn, hMp, hWp⟩ := K Q hQc hQ M hQM hM
    by_cases hQ'ti : Q' ∈ L.TI
    · have hg := hWp Q' (le_trans hQ'M hMp) hQ'ti
      exact ⟨fun _ => hg, Or.inl ⟨hQ'ti, hg⟩⟩
    · have hth : Q' ∈ L.Thick := (hL.dich Q' hQ'c).resolve_left hQ'ti
      refine ⟨fun h => absurd h hQ'ti, Or.inr ⟨hth, ?_⟩⟩
      obtain ⟨p', hp'n, hp'e, hMp'⟩ := hL.nice_thick Q' hth hQ'c M hQ'M hM
      rcases hQ.2 with ⟨hti, hg⟩ | ⟨hQth, p0, hp0n, hp0e, hS, p1, hp1n, hp1e, hQp1, hrt⟩
      · exact ⟨p', hp'n, hp'e, ⟨Q, le_trans hQM hMp', hti, hg⟩, p', hp'n, hp'e,
          le_trans hQ'M hMp', Relation.ReflTransGen.refl⟩
      · exact ⟨p0, hp0n, hp0e, hS, p', hp'n, hp'e, le_trans hQ'M hMp',
          hrt.tail ⟨hp1n, hp1e, hp'n, hp'e, Q, hQth, hQc, hQp1, le_trans hQM hMp'⟩⟩
  obtain ⟨q, hq, hqI⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := I.asIdeal) bot_le
  let P0 : PrimeSpectrum R := ⟨q, hq.1.1⟩
  have hP0I : P0 ≤ I := show q ≤ I.asIdeal from hqI
  have hP0ti : P0 ∈ L.TI := hL.ti_down P0 I hP0I hIti
  have hP0c : L.Comp P0 := hL.comp P0 hP0ti hq
  obtain ⟨p, hpn, hIp⟩ := hL.nice_good I hIg hIbig
  have hP0g := hW p hpn ⟨I, hIp, hIti, hIg⟩ P0 (le_trans hP0I hIp) hP0ti
  have hP0 : Inv P0 := ⟨fun _ => hP0g, Or.inl ⟨hP0ti, hP0g⟩⟩
  have hall : ∀ Q, Relation.ReflTransGen L.Adj P0 Q → Inv Q := by
    intro Q hch
    induction hch with
    | refl => exact hP0
    | tail _ hadj ih => exact step _ _ hadj ih
  exact (hall P (hL.chain P0 P hP0c (hL.comp P hPti hPmin))).1 hPti

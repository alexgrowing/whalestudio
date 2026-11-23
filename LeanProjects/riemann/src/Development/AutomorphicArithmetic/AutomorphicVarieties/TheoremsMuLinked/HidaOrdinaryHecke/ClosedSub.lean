import Mathlib

open IsLocalRing

theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.closedSub :
    ∀ {O T : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] [CommRing T] [IsLocalRing T] [Algebra O T] (I : Ideal T) [Module.Finite O (T ⧸ I)] (S : Subalgebra O T) (t : T), (∀ N : ℕ, ∃ s ∈ S, t - s ∈ maximalIdeal T ^ N) → ∃ s ∈ S, t - s ∈ I := by
  intro O T _ _ _ _ _ _ I _ S t ht
  let q : T →ₐ[O] T ⧸ I := Ideal.Quotient.mkₐ O I
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective O I
  haveI : IsNoetherian O (T ⧸ I) := inferInstance
  haveI : IsNoetherianRing (T ⧸ I) := isNoetherian_of_tower O inferInstance
  haveI : Algebra.IsIntegral O (T ⧸ I) := inferInstance
  set K : Ideal (T ⧸ I) := (maximalIdeal T).map q with hK
  set J : Ideal (T ⧸ I) := (maximalIdeal O).map (algebraMap O (T ⧸ I)) with hJ
  have hKJ : K ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨hJP, hPp⟩ := hP
    have hc : (P.comap (algebraMap O (T ⧸ I))).IsMaximal := by
      have h1 : maximalIdeal O ≤ P.comap (algebraMap O (T ⧸ I)) := Ideal.map_le_iff_le_comap.mp hJP
      have h2 : (P.comap (algebraMap O (T ⧸ I))).IsPrime := Ideal.comap_isPrime _ _
      rw [← (maximalIdeal.isMaximal O).eq_of_le h2.ne_top h1]
      exact maximalIdeal.isMaximal O
    haveI := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P hc
    have h3 : (P.comap q).IsMaximal := Ideal.comap_isMaximal_of_surjective q hq
    have h4 : P.comap q = maximalIdeal T := IsLocalRing.eq_maximalIdeal h3
    rw [hK, Ideal.map_le_iff_le_comap, h4]
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hKJ (IsNoetherian.noetherian K)
  let Sb : Submodule O (T ⧸ I) := (Subalgebra.toSubmodule S).map q.toLinearMap
  have hmem : ∀ k : ℕ, Sb.mkQ (q t) ∈ ((maximalIdeal O) ^ k • ⊤ : Submodule O ((T ⧸ I) ⧸ Sb)) := by
    intro k
    obtain ⟨s, hs, hts⟩ := ht (n * k)
    have h1 : q (t - s) ∈ K ^ (n * k) := by
      rw [hK, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hts
    have h2 : q (t - s) ∈ J ^ k := by
      rw [pow_mul] at h1
      first
        | exact Ideal.pow_right_mono hn k h1
        | exact pow_le_pow_left' hn k h1
    have h3 : q (t - s) ∈ ((maximalIdeal O) ^ k • ⊤ : Submodule O (T ⧸ I)) := by
      rw [Ideal.smul_top_eq_map, Ideal.map_pow]
      exact h2
    have h4 : Sb.mkQ (q t) = Sb.mkQ (q (t - s)) := by
      rw [map_sub, map_sub, eq_comm, sub_eq_self]
      exact (Submodule.Quotient.mk_eq_zero Sb).mpr ⟨s, hs, rfl⟩
    have h5 := Submodule.mem_map_of_mem (f := Sb.mkQ) h3
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h5
    rw [h4]
    exact h5
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := O) (M := (T ⧸ I) ⧸ Sb)
    (maximalIdeal O) (maximalIdeal.isMaximal O).ne_top
  have h0 : Sb.mkQ (q t) = 0 := by
    have hi : Sb.mkQ (q t) ∈ (⨅ i : ℕ, (maximalIdeal O) ^ i • ⊤ : Submodule O ((T ⧸ I) ⧸ Sb)) :=
      Submodule.mem_iInf _ |>.mpr hmem
    rw [hbot] at hi
    exact hi
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨s, hs, hsq⟩ := h0
  refine ⟨s, hs, ?_⟩
  exact Ideal.Quotient.eq.mp hsq.symm

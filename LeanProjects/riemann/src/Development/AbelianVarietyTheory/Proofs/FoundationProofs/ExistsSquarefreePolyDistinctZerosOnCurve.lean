import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducedFibresAlmostAllStatement

open Polynomial

namespace GlobalTheory.SquarefreeFibre

theorem algebraMap_norm_mem_span {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] (g : S) :
    algebraMap R S (Algebra.norm R g) ∈ Ideal.span {g} := by
  set p := LinearMap.charpoly (Algebra.lmul R S g) with hp
  have h1 : aeval g p = 0 := by
    have h2 := congrArg (fun φ : Module.End R S => φ 1) (LinearMap.aeval_self_charpoly (Algebra.lmul R S g))
    rw [← hp, Polynomial.aeval_algHom_apply (Algebra.lmul R S) g p] at h2
    simpa using h2
  have h3 : algebraMap R S (p.coeff 0) = -(g * aeval g p.divX) := by
    have h4 := X_mul_divX_add p
    rw [← h4] at h1
    simp only [map_add, map_mul, aeval_X, aeval_C] at h1
    linear_combination h1
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff, map_mul, ← hp, h3]
  exact Ideal.mul_mem_left _ _ ((Ideal.span {g}).neg_mem
    (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g)))

theorem main : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (g : A) (s : ℕ), g ≠ 0 → ∃ (q : k[X]) (r : ℕ) (Q : Fin r → Ideal A), q.Monic ∧ q.natDegree = s ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, g ∉ Q i) ∧ Ideal.span {algebraMap k[X] A q} = ∏ i, Q i := by
  intro k A _ _ _ _ _ _ _ _ _ _ g s hg
  classical
  obtain ⟨δ, hδ0, hδ⟩ := GlobalTheory.T.exists_nonzero_sub_C_not_mem_sq_maximal k A
  set u := algebraMap k[X] A with hu
  set N := Algebra.norm k[X] g with hNdef
  have hN : N ≠ 0 := Algebra.norm_ne_zero_iff.mpr hg
  have hinj : Function.Injective u := FaithfulSMul.algebraMap_injective k[X] A
  have huC : ∀ c : k, u (C c) = algebraMap k A c := by
    intro c
    rw [IsScalarTower.algebraMap_apply k k[X] A c, Polynomial.algebraMap_eq]

  have hCnot : ∀ (P : Ideal A), P.IsPrime → ∀ c : k, c ≠ 0 → u (C c) ∉ P := by
    intro P hP c hc hmem
    rw [huC] at hmem
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit hc).map (algebraMap k A)))

  have hgnot : ∀ (P : Ideal A), P.IsPrime → ∀ α : k, N.eval α ≠ 0 → u (X - C α) ∈ P → g ∉ P := by
    intro P hP α hα hX hgP
    have hNP : u N ∈ P := (Ideal.span_singleton_le_iff_mem P).mpr hgP (algebraMap_norm_mem_span g)
    have hdec := modByMonic_add_div N (X - C α)
    rw [modByMonic_X_sub_C_eq_C_eval] at hdec
    have h5 : C (N.eval α) = N - (X - C α) * (N /ₘ (X - C α)) := eq_sub_of_add_eq hdec
    have : u (C (N.eval α)) = u N - u (X - C α) * u (N /ₘ (X - C α)) := by
      rw [h5, map_sub, map_mul]
    exact hCnot P hP _ hα (this ▸ P.sub_mem hNP (P.mul_mem_right _ hX))

  have hδN : δ * N ≠ 0 := mul_ne_zero hδ0 hN
  have hfin : {a : k | (δ * N).eval a = 0}.Finite :=
    ((δ * N).roots.toFinset.finite_toSet).subset (fun a ha => by
      simp only [Set.mem_setOf_eq] at ha
      simp [Polynomial.mem_roots hδN, ha])
  have hinf : {a : k | (δ * N).eval a ≠ 0}.Infinite := by
    have := hfin.infinite_compl
    simpa [Set.compl_setOf] using this
  obtain ⟨F, hFS, hFcard⟩ := hinf.exists_subset_card_eq s
  have hF : ∀ a ∈ F, δ.eval a ≠ 0 ∧ N.eval a ≠ 0 := by
    intro a ha
    have := hFS ha
    simp only [Set.mem_setOf_eq, eval_mul] at this
    exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  set q : k[X] := ∏ a ∈ F, (X - C a) with hq
  have hqm : q.Monic := monic_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  have hqdeg : q.natDegree = s := by
    rw [hq, natDegree_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)]
    simp [hFcard]

  have hone : ∀ (P : Ideal A), P.IsPrime → u q ∈ P → ∃ a ∈ F, u (X - C a) ∈ P := by
    intro P hP hqP
    rw [hq, map_prod] at hqP
    exact Ideal.IsPrime.prod_mem_iff.mp hqP
  have huniq : ∀ (P : Ideal A), P.IsPrime → ∀ a b : k, u (X - C a) ∈ P → u (X - C b) ∈ P → a = b := by
    intro P hP a b ha hb
    by_contra hab
    have : u (C (b - a)) = u (X - C a) - u (X - C b) := by
      rw [← map_sub]; congr 1; simp [C_sub]
    exact hCnot P hP (b - a) (sub_ne_zero.mpr (Ne.symm hab)) (this ▸ P.sub_mem ha hb)
  have hnotsq : ∀ (P : Ideal A), P.IsMaximal → u q ∉ P ^ 2 := by
    intro P hPm hq2
    have hP : P.IsPrime := hPm.isPrime
    obtain ⟨a, haF, haP⟩ := hone P hP (Ideal.pow_le_self two_ne_zero hq2)
    have hsplit : q = (∏ b ∈ F.erase a, (X - C b)) * (X - C a) := by
      rw [hq, mul_comm, Finset.mul_prod_erase F (fun b => X - C b) haF]
    rw [hsplit, map_mul] at hq2
    rcases Ideal.IsPrime.mul_mem_pow P hq2 with hrest | hX2
    · rw [map_prod] at hrest
      obtain ⟨b, hbF, hbP⟩ := Ideal.IsPrime.prod_mem_iff.mp hrest
      exact (Finset.ne_of_mem_erase hbF) (huniq P hP b a hbP haP)
    · exact hδ a (hF a haF).1 P hPm hX2

  set I : Ideal A := Ideal.span {u q} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact fun h => hqm.ne_zero (hinj (h.trans (map_zero u).symm))
  have hsq : Squarefree I := by
    intro J hJ
    by_contra hJu
    have hJtop : J ≠ ⊤ := fun h => hJu (Ideal.isUnit_iff.mpr h)
    obtain ⟨P, hPm, hJP⟩ := Ideal.exists_le_maximal J hJtop
    have hle : I ≤ P ^ 2 := (Ideal.le_of_dvd hJ).trans (by rw [pow_two]; exact Ideal.mul_mono hJP hJP)
    exact hnotsq P hPm (hle (Ideal.mem_span_singleton_self _))
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hsq
  set M := UniqueFactorizationMonoid.normalizedFactors I with hM
  have hmem : ∀ P ∈ M, P.IsMaximal ∧ g ∉ P := by
    intro P hPM
    have hPp : P.IsPrime := Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor P hPM)
    have hPne : P ≠ ⊥ := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hPM
    refine ⟨hPp.isMaximal hPne, ?_⟩
    have hqP : u q ∈ P := Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hPM)
      (Ideal.mem_span_singleton_self _)
    obtain ⟨a, haF, haP⟩ := hone P hPp hqP
    exact hgnot P hPp a (hF a haF).2 haP
  let e := M.toFinset.equivFin
  refine ⟨q, M.toFinset.card, fun i => (e.symm i : Ideal A), hqm, hqdeg, ?_, ?_, ?_, ?_⟩
  · intro i; exact (hmem _ (Multiset.mem_toFinset.mp (e.symm i).2)).1
  · intro i j h; exact e.symm.injective (Subtype.ext h)
  · intro i; exact (hmem _ (Multiset.mem_toFinset.mp (e.symm i).2)).2
  · rw [Fintype.prod_equiv e.symm (fun i => (e.symm i : Ideal A)) (fun x => (x : Ideal A)) (fun _ => rfl),
      Finset.prod_coe_sort M.toFinset (fun x => x), Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      hnodup.dedup, Multiset.map_id', hM, ← hI]
    exact (Ideal.prod_normalizedFactors_eq_self hI0).symm

end GlobalTheory.SquarefreeFibre

import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.RingKrullDimQuotientOfMemAssociatedPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem UpperTheory.V.AlgebraTools.Conn.exists_system_of_parameters {A : Type} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (J : Ideal A) (hle : J ≤ maximalIdeal A) :
    ∃ ys : List A, (∀ y ∈ ys, y ∈ maximalIdeal A) ∧
      (ys.length : WithBot ℕ∞) = ringKrullDim (A ⧸ J) ∧
      ∀ P : Ideal A, P.IsPrime → J ≤ P → (∀ y ∈ ys, y ∈ P) → P = maximalIdeal A := by
  have hne : J ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ hle))
  haveI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hne
  haveI : IsLocalRing (A ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  set π := Ideal.Quotient.mk J with hπ
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  haveI : IsLocalHom π := IsLocalHom.of_surjective π hsurj
  obtain ⟨s, hs, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal (A ⧸ J))
  obtain ⟨g, hg⟩ := hsurj.hasRightInverse
  refine ⟨s.toList.map g, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have h1 : π (g z) ∈ maximalIdeal (A ⧸ J) := by
      rw [hg]
      exact hs.1.2 (Ideal.subset_span (Finset.mem_toList.1 hz))
    rw [mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
    exact fun h => h1 (h.map π)
  · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hcard]
    simp
  · intro P hP hJP hy
    have hker : RingHom.ker π ≤ P := by rw [hπ, Ideal.mk_ker]; exact hJP
    have hP' : (P.map π).IsPrime := Ideal.map_isPrime_of_surjective hsurj hker
    have hs' : Ideal.span (s : Set (A ⧸ J)) ≤ P.map π := by
      rw [Ideal.span_le]
      intro z hz
      rw [← hg z]
      exact Ideal.mem_map_of_mem π (hy _ (List.mem_map.2 ⟨z, Finset.mem_toList.2 hz, rfl⟩))
    have hm : maximalIdeal (A ⧸ J) ≤ P.map π :=
      hs.2 ⟨hP', hs'⟩ (le_maximalIdeal hP'.ne_top)
    refine le_antisymm (le_maximalIdeal hP.ne_top) fun a ha => ?_
    have h1 : π a ∈ P.map π := hm (map_nonunit π a ha)
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective π hsurj, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.2 hker] at h1
    exact h1

private theorem UpperTheory.V.AlgebraTools.Conn.weakly_regular_mem_of_mul {A : Type} [CommRing A] (l w : List A) (a : A)
    (h : RingTheory.Sequence.IsWeaklyRegular A (l ++ a :: w)) (x : A)
    (hx : a * x ∈ Ideal.ofList l) : x ∈ Ideal.ofList l := by
  have h1 := h.regular_mod_prev l.length (by simp)
  simp only [List.getElem_append_right, le_refl, Nat.sub_self,
    List.getElem_cons_zero] at h1
  rw [List.take_left' rfl] at h1
  have e : (Ideal.ofList l • (⊤ : Submodule A A)) = Ideal.ofList l := by
    rw [smul_eq_mul, Ideal.mul_top]
  have h2 : (Submodule.Quotient.mk x : A ⧸ (Ideal.ofList l • (⊤ : Submodule A A))) = 0 := by
    apply h1
    show a • _ = a • _
    rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, e]
    exact hx
  rwa [Submodule.Quotient.mk_eq_zero, e] at h2

theorem UpperTheory.V.AlgebraTools.Conn.reg2 :
    ∀ {A : Type} [CommRing A] [IsLocalRing A], ReciprocityTheory.CA.IsCM A → ∀ xs : List A, (∀ x ∈ xs, x ∈ maximalIdeal A) →
      ringKrullDim (A ⧸ Ideal.ofList xs) + xs.length = ringKrullDim A → 2 ≤ ringKrullDim (A ⧸ Ideal.ofList xs) →
      ∃ u ∈ maximalIdeal A, ∃ v ∈ maximalIdeal A, ∀ m K : ℕ,
        Reg2 (Ideal.ofList (xs.map (· ^ (m + 1)))) (u ^ K) (v ^ K) := by
  intro A _ _ hA xs hxs hdim h2
  haveI := hA.1
  obtain ⟨ys, hys, hlen, hP⟩ := exists_system_of_parameters (Ideal.ofList xs) (Ideal.span_le.2 hxs)
  rw [← hlen] at hdim h2
  have h2' : 2 ≤ ys.length := by exact_mod_cast h2
  obtain ⟨u, v, w, rfl⟩ : ∃ u v w, ys = u :: v :: w := by
    match ys, h2' with
    | u :: v :: w, _ => exact ⟨u, v, w, rfl⟩
  have hu := hys u (by simp)
  have hv := hys v (by simp)
  refine ⟨u, hu, v, hv, fun m K => ?_⟩
  rcases K with _ | K
  · simpa using isWeaklyRegularPairMod_one_left _ _
  set l := xs.map (· ^ (m + 1)) with hl
  have hreg : RingTheory.Sequence.IsRegular A (l ++ u ^ (K + 1) :: v ^ (K + 1) :: w) := by
    refine hA.isRegular_of_isArtinianRing_quotient _ ?_ ?_ ?_
    · intro r hr
      simp only [hl, List.mem_append, List.mem_map, List.mem_cons] at hr
      rcases hr with ⟨x, hx, rfl⟩ | rfl | rfl | hr
      · exact Ideal.pow_mem_of_mem _ (hxs x hx) _ (Nat.succ_pos _)
      · exact Ideal.pow_mem_of_mem _ hu _ (Nat.succ_pos _)
      · exact Ideal.pow_mem_of_mem _ hv _ (Nat.succ_pos _)
      · exact hys r (by simp [hr])
    · rw [← hdim]
      simp only [hl, List.length_append, List.length_map, List.length_cons]
      push_cast
      rw [add_comm]
    · set I := Ideal.ofList (l ++ u ^ (K + 1) :: v ^ (K + 1) :: w) with hI
      have : Ring.KrullDimLE 0 (A ⧸ I) := by
        rw [Ring.krullDimLE_zero_iff]
        intro Q hQ
        have hp : (Q.comap (Ideal.Quotient.mk I)).IsPrime := Ideal.comap_isPrime _ _
        have hmem : ∀ r ∈ l ++ u ^ (K + 1) :: v ^ (K + 1) :: w,
            r ∈ Q.comap (Ideal.Quotient.mk I) := by
          intro r hr
          have : r ∈ I := Ideal.subset_span hr
          rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 this]
          exact Q.zero_mem
        have := hP _ hp (Ideal.span_le.2 fun x hx => hp.mem_of_pow_mem (m + 1)
          (hmem _ (List.mem_append_left _ (List.mem_map.2 ⟨x, hx, rfl⟩)))) (by
            intro y hy
            simp only [List.mem_cons] at hy
            rcases hy with rfl | rfl | hy
            · exact hp.mem_of_pow_mem (K + 1) (hmem _ (by simp))
            · exact hp.mem_of_pow_mem (K + 1) (hmem _ (by simp))
            · exact hmem _ (by simp [hy]))
        have hmax : (Q.comap (Ideal.Quotient.mk I)).IsMaximal := this ▸ maximalIdeal.isMaximal A
        rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective Q]
        refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
          hmax).resolve_left ?_
        rw [Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective Q]
        exact hQ.ne_top
      exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  refine ⟨weakly_regular_mem_of_mul l _ _ hreg.toIsWeaklyRegular, fun a ha => ?_⟩
  have e : Ideal.ofList (l ++ [u ^ (K + 1)]) = Ideal.ofList l ⊔ Ideal.span {u ^ (K + 1)} := by
    rw [Ideal.ofList_append, Ideal.ofList_singleton]
  rw [← e] at ha ⊢
  exact weakly_regular_mem_of_mul _ w _ (by simpa using hreg.toIsWeaklyRegular) a ha

import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.RingKrullDimQuotientOfMemAssociatedPrimes

namespace ReciprocityTheory.CA

open IsLocalRing RingTheory.Sequence

variable {R : Type*} [CommRing R] [IsLocalRing R]

private theorem height_le_length_of_mem_minimalPrimes [IsNoetherianRing R] (rs : List R) {p : Ideal R}
    (hp : p ∈ (Ideal.ofList rs).minimalPrimes) : p.height ≤ (rs.length : ℕ∞) := by
  classical
  have h1 := Ideal.height_le_spanRank_toENat_of_mem_minimal_primes _ p hp
  have hcard : Cardinal.mk {x | x ∈ rs} ≤ rs.length := by
    have : {x | x ∈ rs} = (rs.toFinset : Set R) := by ext; simp
    rw [this]
    calc Cardinal.mk (rs.toFinset : Set R) = (rs.toFinset.card : Cardinal) := Cardinal.mk_coe_finset
      _ ≤ rs.length := by exact_mod_cast List.toFinset_card_le rs
  have h2 : (Ideal.ofList rs).spanRank ≤ rs.length := by
    unfold Ideal.ofList
    exact (Submodule.spanRank_span_le_card _).trans hcard
  refine h1.trans ?_
  simpa using OrderHomClass.mono Cardinal.toENat h2

theorem grade_step_exists (h : IsCM R) {I : Ideal R} (hI : I ≠ ⊤) {r : ℕ}
    (hr : (r : ℕ∞) ≤ I.height) (rs : List R) (hlen : rs.length < r) (hrsI : ∀ x ∈ rs, x ∈ I)
    (reg : IsRegular R rs) :
    ∃ x ∈ I, IsSMulRegular (R ⧸ (Ideal.ofList rs • ⊤ : Submodule R R)) x := by
  haveI : IsNoetherianRing R := h.1
  have hIm : I ≤ maximalIdeal R := le_maximalIdeal hI
  have hCM := (isCM_iff_isCMMod.mp h).quotient_ofList (fun x hx => hIm (hrsI x hx)) reg
  have hJ : (Ideal.ofList rs • (⊤ : Submodule R R) : Ideal R) = Ideal.ofList rs := Ideal.mul_top _
  have hass : associatedPrimes R (R ⧸ (Ideal.ofList rs • ⊤ : Submodule R R)) =
      (Ideal.ofList rs).minimalPrimes := by
    rw [hCM.associatedPrimes_eq_minimalPrimes, Ideal.annihilator_quotient, hJ]
  have hfin := associatedPrimes.finite R (R ⧸ (Ideal.ofList rs • ⊤ : Submodule R R))
  have hnot : ¬ ((I : Set R) ⊆ ⋃ p ∈ (hfin.toFinset : Set (Ideal R)), (p : Set R)) := by
    intro hsub
    obtain ⟨p, hp, hIp⟩ := (Ideal.subset_union_prime (f := id) ⊥ ⊥
      (fun i hi _ _ => by
        rw [Set.Finite.mem_toFinset] at hi
        exact (IsAssociatedPrime.isPrime hi))).mp hsub
    rw [Set.Finite.mem_toFinset, hass] at hp
    have h1 := height_le_length_of_mem_minimalPrimes rs hp
    have h2 : I.height ≤ p.height := Ideal.height_mono hIp
    have h3 : (rs.length : ℕ∞) < r := by exact_mod_cast hlen
    exact absurd (hr.trans (h2.trans h1)) (not_le.mpr h3)
  obtain ⟨x, hxI, hx⟩ := Set.not_subset.mp hnot
  refine ⟨x, hxI, ?_⟩
  have hx' : x ∉ ⋃ p ∈ associatedPrimes R (R ⧸ (Ideal.ofList rs • ⊤ : Submodule R R)), (p : Set R) := by
    simpa using hx
  rw [biUnion_associatedPrimes_eq_compl_regular] at hx'
  simpa using hx'

private theorem isRegular_of_isWeaklyRegular_of_mem_ne_top {I : Ideal R} (hI : I ≠ ⊤) (rs : List R)
    (hrsI : ∀ x ∈ rs, x ∈ I) (w : IsWeaklyRegular R rs) : IsRegular R rs := by
  refine ⟨w, ?_⟩
  intro heq
  apply hI
  rw [eq_top_iff]
  have h1 : (Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs := Ideal.mul_top _
  have h2 : Ideal.ofList rs ≤ I := Ideal.span_le.mpr (fun y hy => hrsI y hy)
  calc (⊤ : Ideal R) = (Ideal.ofList rs • (⊤ : Submodule R R)) := heq
    _ = Ideal.ofList rs := h1
    _ ≤ I := h2

theorem IsCM.exists_isRegular_of_le_height (h : IsCM R) {I : Ideal R} (hI : I ≠ ⊤) {r : ℕ}
    (hr : (r : ℕ∞) ≤ I.height) :
    ∃ rs : List R, rs.length = r ∧ (∀ x ∈ rs, x ∈ I) ∧ IsRegular R rs := by
  induction r with
  | zero =>
    exact ⟨[], rfl, by simp, isRegular_of_isWeaklyRegular_of_mem_ne_top hI [] (by simp) (by simp)⟩
  | succ n ih =>
    obtain ⟨rs, hlen, hrsI, reg⟩ := ih ((Nat.cast_le.mpr (Nat.le_succ n)).trans hr)
    obtain ⟨x, hxI, hx⟩ := grade_step_exists h hI hr rs (by omega) hrsI reg
    have hall : ∀ y ∈ rs ++ [x], y ∈ I := by
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hrsI y hy
      · rw [List.mem_singleton.mp hy]; exact hxI
    refine ⟨rs ++ [x], by simp [hlen], hall, isRegular_of_isWeaklyRegular_of_mem_ne_top hI _ hall ?_⟩
    exact (isWeaklyRegular_append_iff R rs [x]).mpr
      ⟨reg.1, (isWeaklyRegular_singleton_iff _ x).mpr hx⟩

end ReciprocityTheory.CA

import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.IsLiftMap

set_option linter.overlappingInstances false

noncomputable section

open UpperTheory.V.Alg UpperTheory.V.Fr

namespace UpperTheory.V.J

section Grading

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {K : Type} [CommRing K]

private theorem mon_mul {ρ : NRep F n K} {a b : K} {i j : ℤ} (ha : a ∈ ρ.mon i) (hb : b ∈ ρ.mon j) :
    a * b ∈ ρ.mon (i + j) := by
  obtain ⟨L1, h1, rfl⟩ := ha
  obtain ⟨L2, h2, rfl⟩ := hb
  refine ⟨L1 ++ L2, ?_, ?_⟩
  · rw [List.map_append, List.sum_append, h1, h2]
  · rw [List.map_append, List.prod_append]

private theorem mon_entry (ρ : NRep F n K) (g : F.G0) (i j : Fin n) : ρ.r g i j ∈ ρ.mon (w n i - w n j) :=
  ⟨[(g, i, j)], by simp, by simp⟩

private theorem w_lower : ∀ i j : Fin 3, j < i → w 3 i - w 3 j = -1 ∨ w 3 i - w 3 j = -2 := by
  decide

private theorem w_upper : ∀ i j : Fin 3, i < j → w 3 i - w 3 j = 1 ∨ w 3 i - w 3 j = 2 := by
  decide

private theorem w_odd : ∀ i j : Fin 3, Odd (w 3 i - w 3 j) → w 3 i - w 3 j = 1 ∨ w 3 i - w 3 j = -1 := by
  decide

private theorem exists_mon (ρ : NRep F 3 K) (P : Ideal K) [hP : P.IsPrime] (h : ρ.TI P) :
    (∃ p ∈ ρ.mon 1, p ∉ P) ∧ ∃ q ∈ ρ.mon (-1), q ∉ P := by
  obtain ⟨⟨hP', hM'⟩, hee⟩ := h
  have ex : ∀ {S : Set K}, ¬ Ideal.span S ≤ P → ∃ s ∈ S, s ∉ P := by
    intro S hS
    by_contra hc
    push_neg at hc
    exact hS (Ideal.span_le.mpr hc)
  have hmul : ∀ {a b : K}, a ∉ P → b ∉ P → a * b ∉ P := fun ha hb hm =>
    (hP.mem_or_mem hm).elim ha hb
  obtain ⟨_, ⟨g1, i1, j1, hj1, rfl⟩, hy⟩ := ex (S := {x | ∃ g i, ∃ j < i, x = ρ.r g i j}) hP'
  obtain ⟨_, ⟨g2, i2, j2, hj2, rfl⟩, hz⟩ := ex (S := {x | ∃ g i j, i < j ∧ x = ρ.r g i j}) hM'
  obtain ⟨_, ⟨g3, i3, j3, hodd, rfl⟩, hx⟩ :=
    ex (S := {x | ∃ g i j, Odd (w 3 i - w 3 j) ∧ x = ρ.r g i j}) (hee rfl)
  have my := mon_entry ρ g1 i1 j1
  have mz := mon_entry ρ g2 i2 j2
  have mx := mon_entry ρ g3 i3 j3
  rcases w_odd i3 j3 hodd with hx1 | hx1
  · rw [hx1] at mx
    refine ⟨⟨_, mx, hx⟩, ?_⟩
    rcases w_lower i1 j1 hj1 with hy1 | hy1
    · rw [hy1] at my
      exact ⟨_, my, hy⟩
    · rw [hy1] at my
      have m := mon_mul my mx
      norm_num at m
      exact ⟨_, m, hmul hy hx⟩
  · rw [hx1] at mx
    refine ⟨?_, ⟨_, mx, hx⟩⟩
    rcases w_upper i2 j2 hj2 with hz1 | hz1
    · rw [hz1] at mz
      exact ⟨_, mz, hz⟩
    · rw [hz1] at mz
      have m := mon_mul mz mx
      norm_num at m
      exact ⟨_, m, hmul hz hx⟩

end Grading

private theorem cancel {O : Type} [CommRing O] [IsDomain O] {a b : O} (ha : a ≠ 0) (h : a * b = 0) : b = 0 :=
  (mul_eq_zero.mp h).resolve_left ha

section Der

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fr.IsCoef l O]
  {F : Fr.Frame l (IsLocalRing.ResidueField O)} {S : Fr.Space O F 3} {ξ : S.R →ₐ[O] O}

private theorem der_zero {p q : S.R} (hp : p ∈ S.ρ.mon 1) (hq : q ∈ S.ρ.mon (-1)) (hξp : ξ p ≠ 0) (hξq : ξ q ≠ 0)
    {E : S.R →ₗ[O] O} (hE : E ∈ PtDer ξ O) (hB : ∀ a ∈ S.B, E a = 0) (hEp : E p = 0) : E = 0 := by
  have hder : ∀ f g : S.R, E (f * g) = ξ f • E g + ξ g • E f := hE
  have canc : ∀ {x y : S.R}, ξ y ≠ 0 → E y = 0 → E (x * y) = 0 → E x = 0 := by
    intro x y hy hEy hxy
    rw [hder, hEy, smul_zero, zero_add, smul_eq_mul] at hxy
    exact cancel hy hxy
  have mB0 : ∀ {x : S.R}, x ∈ S.ρ.mon 0 → E x = 0 := fun hx => hB _ (S.mon_mem hx)
  have hEq : E q = 0 := canc hξp hEp (mB0 (by
    have m := mon_mul hq hp
    norm_num at m
    exact m))
  have e1 : ∀ {x : S.R}, x ∈ S.ρ.mon 1 → E x = 0 := fun hx => canc hξq hEq (mB0 (by
    have m := mon_mul hx hq
    norm_num at m
    exact m))
  have em1 : ∀ {x : S.R}, x ∈ S.ρ.mon (-1) → E x = 0 := fun hx => canc hξp hEp (mB0 (by
    have m := mon_mul hx hp
    norm_num at m
    exact m))
  have e2 : ∀ {x : S.R}, x ∈ S.ρ.mon 2 → E x = 0 := fun hx => canc hξq hEq (e1 (by
    have m := mon_mul hx hq
    norm_num at m
    exact m))
  have em2 : ∀ {x : S.R}, x ∈ S.ρ.mon (-2) → E x = 0 := fun hx => canc hξp hEp (em1 (by
    have m := mon_mul hx hp
    norm_num at m
    exact m))
  have hrange : ∀ i j : Fin 3, w 3 i - w 3 j = -2 ∨ w 3 i - w 3 j = -1 ∨ w 3 i - w 3 j = 0 ∨
      w 3 i - w 3 j = 1 ∨ w 3 i - w 3 j = 2 := by
    decide
  refine det l O F 3 S ξ E hE (fun g i j => ?_) (fun v i g => hB _ (S.ψ_mem v i g))
  have m := mon_entry S.ρ g i j
  rcases hrange i j with h | h | h | h | h <;> rw [h] at m
  · exact em2 m
  · exact em1 m
  · exact mB0 m
  · exact e1 m
  · exact e2 m

end Der

theorem tor : Tor := by
  intro l _ O _ _ _ _ F S ξ hTI D hD D' hD' hB hB' hli
  haveI : Nontrivial O := IsDomain.toNontrivial
  haveI : (RingHom.ker ξ).IsPrime := RingHom.ker_isPrime ξ
  obtain ⟨⟨p, hp, hpP⟩, ⟨q, hq, hqP⟩⟩ := exists_mon S.ρ (RingHom.ker ξ) hTI
  have hξp : ξ p ≠ 0 := fun h => hpP (RingHom.mem_ker.mpr h)
  have hξq : ξ q ≠ 0 := fun h => hqP (RingHom.mem_ker.mpr h)
  have hE : (D' p) • D + (-(D p)) • D' ∈ PtDer ξ O :=
    (PtDer ξ O).add_mem ((PtDer ξ O).smul_mem _ hD) ((PtDer ξ O).smul_mem _ hD')
  have hEB : ∀ a ∈ S.B, ((D' p) • D + (-(D p)) • D') a = 0 := by
    intro a ha
    simp [hB a ha, hB' a ha]
  have hEp : ((D' p) • D + (-(D p)) • D') p = 0 := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hE0 := der_zero hp hq hξp hξq hE hEB hEp
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp hli _ _ hE0
  have hDp : D p = 0 := neg_eq_zero.mp h2
  have hD0 : D = 0 := der_zero hp hq hξp hξq hD hB hDp
  exact hli.ne_zero 0 hD0

end UpperTheory.V.J

end

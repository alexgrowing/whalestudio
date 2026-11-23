import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EisGEqZeroOfInfinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaNormUnimodularLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.Mem.Per
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.Per.ConjCM

open GlobalTheory.ConjPoint

theorem transfer {L L' : PeriodPair} (σ : ℂ ≃+* ℂ)
    (hj : σ (1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) = 1728 * L'.g₂ ^ 3 / (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2))
    {α : ℂ} (hα : ∀ l ∈ L.lattice, α * l ∈ L.lattice) {t : ℂ} (h2 : 2 * t ∈ L.lattice)
    (ha : α * t ∉ L.lattice) (hb : (1 - α) * t ∉ L.lattice) :
    (∀ l ∈ L'.lattice, σ α * l ∈ L'.lattice) ∧
      ∃ t', 2 * t' ∈ L'.lattice ∧ σ α * t' ∉ L'.lattice ∧ (1 - σ α) * t' ∉ L'.lattice := by
  have h0 := GlobalTheory.g₂_cube_sub_g₃_sq_ne_zero L
  have h0' := GlobalTheory.g₂_cube_sub_g₃_sq_ne_zero L'
  have hσ0 : σ L.g₂ ^ 3 - 27 * σ L.g₃ ^ 2 ≠ 0 := by
    have := (map_ne_zero σ).2 h0
    simpa [map_ofNat] using this
  obtain ⟨M, m₂, m₃⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_invariants hσ0
  simp only [map_div₀, map_mul, map_sub, map_pow, map_ofNat] at hj
  rw [div_eq_div_iff hσ0 h0'] at hj
  obtain ⟨c, hc⟩ := GlobalTheory.exists_isHomothetic_of_j_eq (L := M) (L' := L')
    (by rw [m₂, m₃]; linear_combination hj / 1728)
  have hc0 := hc.ne_zero
  obtain ⟨s, -, hs⟩ := exists_conjEquiv m₂ m₃
  obtain ⟨u, hu⟩ := GlobalTheory.latticePoint_surjective M (s (GlobalTheory.latticePoint L t))
  have hu' : IsConj L M σ t u := (hs _ _).2 hu.symm
  have hβ : ∀ l ∈ L.lattice, (1 - α) * l ∈ L.lattice := fun l hl => by
    rw [sub_mul, one_mul]; exact sub_mem hl (hα l hl)
  refine ⟨fun l hl => ?_, c * u, ?_, ?_, ?_⟩
  · have h1 : c⁻¹ * l ∈ M.lattice := (hc _).1 (by simpa [hc0] using hl)
    have h3 := IsConj.mul m₂ m₃ hα (t := 0) (t' := c⁻¹ * l) (.inl ⟨zero_mem _, h1⟩)
    rcases h3 with h | h
    · have := (hc _).2 h.2
      rwa [show c * (σ α * (c⁻¹ * l)) = σ α * l by field_simp] at this
    · exact absurd (by simp) h.1
  · have := (hc _).2 ((hu'.nsmul_mem_iff m₂ m₃ 2).1 (by exact_mod_cast h2))
    rwa [show c * (((2 : ℕ) : ℂ) * u) = 2 * (c * u) by push_cast; ring] at this
  · rw [mul_left_comm, hc]
    exact ((IsConj.mul m₂ m₃ hα hu').resolve_left fun h => ha h.1).2.1
  · rw [mul_left_comm, hc]
    have := ((IsConj.mul m₂ m₃ hβ hu').resolve_left fun h => hb h.1).2.1
    rwa [map_sub, map_one] at this

variable {R : Ranks} (H : Host R)

theorem mem_baseLat (w : ℂ) :
    w ∈ baseLat H ↔ ∃ c ∈ H.ccK, w = H.φ₀ (((c : H.K) : H.E)) := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, H.ccK.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', H.ccK.add_mem hc hc', by simp⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, H.ccK.neg_mem hc, by simp⟩
  · exact fun hw => AddSubgroup.subset_closure hw

theorem exists_periodPair_baseLat : ∃ L : PeriodPair, ∀ z, z ∈ baseLat H ↔ z ∈ L.lattice := by
  have hr : Module.finrank ℚ H.K = 2 :=
    Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos (H.sqd_sq)
  have hd : NumberField.discr H.K = -(H.d : ℤ) :=
    GlobalTheory.discr_eq_neg_of_sq_eq hr H.hyp.2.1.squarefree
      (by have := H.hyp.2.2.2.1; omega)
      (Formalism.FrobeniusOrbits.SplitK.bK_sq (H.sqd_sq))
  let σ : H.K →+* ℂ := H.φ₀.comp H.K.val.toRingHom
  let I : (Ideal (𝓞 H.K))⁰ := ⟨H.ccK, mem_nonZeroDivisors_of_ne_zero H.ccK_ne_bot⟩
  obtain ⟨L, hL⟩ := GlobalTheory.QuadraticZeta.exists_periodPair hr hd σ (FractionalIdeal.mk0 H.K I)
  refine ⟨L, fun z => ?_⟩
  rw [mem_baseLat, ← SetLike.mem_coe (p := L.lattice), hL]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(c : H.K), FractionalIdeal.mem_coeIdeal_of_mem _ hc, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact ⟨c, hc, rfl⟩

theorem exists_int_root : ∃ a : 𝓞 H.K, (2 * H.φ₀ (((a : H.K) : H.E)) - 1) ^ 2 = -(H.d : ℂ) := by
  have hsq := H.sqd_sq
  let b : H.K := ⟨H.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hb' : b ^ 2 = -(H.d : H.K) := by
    apply Subtype.ext
    simpa using hsq
  refine ⟨⟨(1 + b) / 2, GlobalTheory.NormSum.isIntegral_half_one_add _ H.hyp.2.2.2.1 b hb'⟩, ?_⟩
  change (2 * H.φ₀ (algebraMap H.K H.E ((1 + b) / 2)) - 1) ^ 2 = _
  have := congrArg (fun x => H.φ₀ (algebraMap H.K H.E x)) hb'
  simp only [map_pow, map_neg, map_natCast] at this
  rw [map_div₀, map_add, map_one, map_ofNat, map_div₀, map_add, map_one, map_ofNat, ← this]
  ring

theorem root_cases {d : ℕ} {α : ℂ} (h : (2 * α - 1) ^ 2 = -(d : ℂ)) :
    (α = (1 + Complex.I * (Real.sqrt d : ℂ)) / 2 ∧ 1 - α = (1 - Complex.I * (Real.sqrt d : ℂ)) / 2) ∨
    (1 - α = (1 + Complex.I * (Real.sqrt d : ℂ)) / 2 ∧ α = (1 - Complex.I * (Real.sqrt d : ℂ)) / 2) := by
  have h1 : (2 * α - 1) ^ 2 = (Complex.I * (Real.sqrt d : ℂ)) ^ 2 := by
    rw [h, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with e | e
  · exact .inl ⟨by linear_combination e / 2, by linear_combination -e / 2⟩
  · exact .inr ⟨by linear_combination -e / 2, by linear_combination e / 2⟩

theorem isHalfPt_baseLat : IsHalfPt H.d (baseLat H) ((Ideal.absNorm H.ccK : ℕ) / 2) := by
  have hN : Odd (Ideal.absNorm H.ccK) := Nat.coprime_two_right.1 (H.ccK_coprime 2 (by simp))
  have hint : ∀ w ∈ baseLat H, IsIntegral ℤ w := fun w hw => by
    obtain ⟨c, -, rfl⟩ := (mem_baseLat H w).1 hw
    have h0 : IsIntegral ℤ (c : H.K) := c.2
    exact h0.map (H.φ₀.comp (algebraMap H.K H.E)).toIntAlgHom
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · refine (mem_baseLat H _).2 ⟨((Ideal.absNorm H.ccK : ℕ) : 𝓞 H.K), Ideal.absNorm_mem _, ?_⟩
    simp
    ring
  · refine GlobalTheory.TwoTorsionPt.not_integral_half hN (hint _ h) ?_
    simp only [map_mul, map_div₀, map_add, map_one, Complex.conj_I, Complex.conj_ofReal,
      map_natCast, map_ofNat]
    ring
  · refine GlobalTheory.TwoTorsionPt.not_integral_half hN (hint _ h) ?_
    simp only [map_mul, map_div₀, map_sub, map_one, Complex.conj_I, Complex.conj_ofReal,
      map_natCast, map_ofNat]
    ring

theorem cm_of_isConjLat {LL : Type} [Field LL] [NumberField LL] {emb s : LL →+* ℂ} {Λ : AddSubgroup ℂ}
    (h : IsConjLat emb s (baseLat H) Λ) :
    (∀ z ∈ Λ, ((1 + Complex.I * (Real.sqrt H.d : ℂ)) / 2) * z ∈ Λ) ∧ ∃ t, IsHalfPt H.d Λ t := by
  obtain ⟨L, hL⟩ := exists_periodPair_baseLat H
  obtain ⟨⟨L', hL'⟩, -⟩ := Model.area_pos_of_isConjLat h
  obtain ⟨-, a, ha, ha'⟩ := h
  haveI : Countable LL := Countable.of_equiv _ (Module.finBasis ℚ LL).equivFun.toEquiv.symm
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq emb s
  obtain ⟨c, hc⟩ := exists_int_root H
  set α := H.φ₀ (((c : H.K) : H.E)) with hα
  have hst : ∀ l ∈ L.lattice, α * l ∈ L.lattice := fun l hl => by
    obtain ⟨e, he, rfl⟩ := (mem_baseLat H l).1 ((hL l).2 hl)
    exact (hL _).1 ((mem_baseLat H _).2 ⟨c * e, H.ccK.mul_mem_left c he, by simp [hα]⟩)
  obtain ⟨p2, pa, pb⟩ := isHalfPt_baseLat H
  rw [hL] at p2 pa pb
  have hj : σ (1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) =
      1728 * L'.g₂ ^ 3 / (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) := by
    unfold jLat TaylorLogMetric.discr at ha ha'
    rw [GlobalTheory.LatticeInvariants.g2_eq hL, GlobalTheory.LatticeInvariants.lattice_invariant_g3_eq hL] at ha
    rw [GlobalTheory.LatticeInvariants.g2_eq hL', GlobalTheory.LatticeInvariants.lattice_invariant_g3_eq hL'] at ha'
    rw [← ha, ← ha', hσ]
  obtain ⟨q, t, q2, qa, qb⟩ := transfer σ hj hst p2
    (by rcases root_cases hc with e | e
        · rw [e.1]; exact pa
        · rw [e.2]; exact pb)
    (by rcases root_cases hc with e | e
        · rw [e.2]; exact pb
        · rw [e.1]; exact pa)
  have hc' : (2 * σ α - 1) ^ 2 = -(H.d : ℂ) := by
    simpa [map_ofNat] using congrArg σ hc
  unfold IsHalfPt
  simp only [hL']
  rcases root_cases hc' with e | e
  · exact ⟨e.1 ▸ q, t, q2, e.1 ▸ qa, e.2 ▸ qb⟩
  · refine ⟨fun z hz => ?_, t, q2, e.1 ▸ qb, e.2 ▸ qa⟩
    rw [← e.1, sub_mul, one_mul]
    exact sub_mem hz (q z hz)

end GlobalTheory.Mem.Per.ConjCM

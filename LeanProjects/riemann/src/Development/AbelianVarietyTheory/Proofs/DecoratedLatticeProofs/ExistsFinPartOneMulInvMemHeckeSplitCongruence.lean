import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HeckeSplitAll.Fin

section General

variable {E : Type} [Field E] [NumberField E]

theorem finite_mem {d : 𝓞 E} (hd : d ≠ 0) : {Q : HeightOneSpectrum (𝓞 E) | d ∈ Q.asIdeal}.Finite := by
  have := Ideal.finite_factors (I := Ideal.span {d}) (by simpa using hd)
  simpa only [Ideal.dvd_span_singleton] using this

theorem exists_avoid (c : 𝓞 E ≃+* 𝓞 E) (hc : ∀ x, c (c x) = x) (δ : 𝓞 E) (hδ : c δ ≠ δ) (M : ℕ) (hM : 0 < M)
    (y₀ : 𝓞 E) : ∃ t : 𝓞 E, y₀ + M * t ≠ 0 ∧ ∀ Q : HeightOneSpectrum (𝓞 E), (∀ x ∈ Q.asIdeal, c x ∈ Q.asIdeal) →
      (M : 𝓞 E) ∉ Q.asIdeal → y₀ + M * t ∉ Q.asIdeal := by
  classical
  have hM' : (M : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : 𝓞 E, y₀ + M * t₀ - c (y₀ + M * t₀) ≠ 0 := by
    by_cases h : c y₀ = y₀
    · refine ⟨δ, fun h2 => hδ (mul_left_cancel₀ hM' ?_)⟩
      rw [map_add, map_mul, map_natCast, h] at h2
      linear_combination -h2
    · exact ⟨0, by simpa [sub_eq_zero] using Ne.symm h⟩
  set y₁ := y₀ + M * t₀ with hy₁
  obtain ⟨u, hu⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := (finite_mem ht₀).toFinset)
    (fun Q => Q.asIdeal) (fun _ => 1) (fun Q _ => Q.prime)
    (fun P _ Q _ h h' => h (HeightOneSpectrum.ext h')) (fun Q => if y₁ ∈ Q.1.asIdeal then 1 else 0)
  have e1 : y₀ + M * (t₀ + u * c u) = y₁ + M * (u * c u) := by rw [hy₁]; ring
  have e2 : y₁ + M * (u * c u) - c (y₁ + M * (u * c u)) = y₁ - c y₁ := by
    rw [map_add, map_mul, map_mul, map_natCast, hc]; ring
  refine ⟨t₀ + u * c u, fun h => ht₀ ?_, fun Q hQ hMQ hy => ?_⟩
  · rw [← e2, ← e1, h, map_zero, sub_zero]
  · rw [e1] at hy
    have hd : y₁ - c y₁ ∈ Q.asIdeal := e2 ▸ sub_mem hy (hQ _ hy)
    have h1 := hu Q ((finite_mem ht₀).mem_toFinset.2 hd)
    rw [pow_one] at h1
    by_cases h : y₁ ∈ Q.asIdeal
    · simp only [h, if_true] at h1
      have h2 : (M : 𝓞 E) * (u * c u) ∈ Q.asIdeal := by simpa using sub_mem hy h
      have h3 : u ∈ Q.asIdeal := by
        rcases Q.isPrime.mem_or_mem ((Q.isPrime.mem_or_mem h2).resolve_left hMQ) with h3 | h3
        · exact h3
        · exact hc u ▸ hQ _ h3
      exact Q.isPrime.one_notMem (by simpa using sub_mem h3 h1)
    · simp only [h, if_false, sub_zero] at h1
      exact h (by simpa using sub_mem hy (Ideal.mul_mem_left _ (M : 𝓞 E) (Ideal.mul_mem_right (c u) _ h1)))

theorem local_close {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {s y n m : K}
    (hs : s ≠ 0) (hm : v m ≤ v s) (hm1 : v m ≤ 1) (hlt : v (n * m) < 1) (hy : v (y - s) ≤ v (n * m * m)) :
    v (s * y⁻¹) = 1 ∧ v (s * y⁻¹ - 1) ≤ v n := by
  have hs' : 0 < v s := zero_lt_iff.2 (v.ne_zero_iff.2 hs)
  have h1 : v (y - s) ≤ v (n * m) * v s := hy.trans (by rw [v.map_mul]; gcongr)
  have h2 : v y = v s := v.map_eq_of_sub_lt (h1.trans_lt (mul_lt_of_lt_one_left hs' hlt))
  have hy0 : y ≠ 0 := v.ne_zero_iff.1 (h2 ▸ hs'.ne')
  refine ⟨by rw [v.map_mul, map_inv₀, h2, mul_inv_cancel₀ hs'.ne'], ?_⟩
  have e : s * y⁻¹ - 1 = -(y - s) * y⁻¹ := by field_simp; ring
  rw [e, v.map_mul, v.map_neg, map_inv₀, h2, mul_inv_le_iff₀ hs']
  refine h1.trans ?_
  rw [v.map_mul]
  gcongr
  exact mul_le_of_le_one_right' hm1

theorem local_unit {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {s y n m : K}
    (hs : v s ≤ 1) (hm : v m ≤ v s) (hm1 : v m ≤ 1) (hn : v n ≤ 1) (hlt : ¬ v (n * m) < 1) (hy : v y = 1) :
    v (s * y⁻¹) = 1 ∧ v (s * y⁻¹ - 1) ≤ v n := by
  rw [not_lt, v.map_mul] at hlt
  have h1 : 1 ≤ v m := hlt.trans (mul_le_of_le_one_left' hn)
  have h2 : 1 ≤ v n := hlt.trans (mul_le_of_le_one_right' hm1)
  have h3 : v (s * y⁻¹) = 1 := by rw [v.map_mul, map_inv₀, hy, inv_one, mul_one]; exact le_antisymm hs (h1.trans hm)
  exact ⟨h3, (v.map_sub_le h3.le v.map_one.le).trans h2⟩

theorem val_int (Q : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) :
    Valued.v (algebraMap E (Q.adicCompletion E) (x : E)) < 1 ↔ x ∈ Q.asIdeal := by
  rw [Formalism.UG.P.levelaf_valued_algebraMap]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) Q x

theorem val_int_le (Q : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) :
    Valued.v (algebraMap E (Q.adicCompletion E) (x : E)) ≤ 1 := by
  rw [Formalism.UG.P.levelaf_valued_algebraMap]
  exact Q.valuation_le_one _

theorem val_nat_le (Q : HeightOneSpectrum (𝓞 E)) (n : ℕ) : Valued.v (n : Q.adicCompletion E) ≤ 1 :=
  natCast_mem (Q.adicCompletionIntegers E) n

theorem exists_den (s : FiniteAdeleRing (𝓞 E) E) :
    ∃ m : ℕ, 0 < m ∧ ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v ((m : Q.adicCompletion E) * s Q) ≤ 1 := by
  obtain ⟨x, a, ha, rfl⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E 1 one_pos).1 s
  obtain ⟨m, hm, hi⟩ := exists_integral_multiples ℤ ℚ (L := E) {x}
  have hi := hi x (Finset.mem_singleton_self x)
  refine ⟨m.natAbs, Int.natAbs_pos.2 hm, fun Q => ?_⟩
  have h1 : IsIntegral ℤ ((m.natAbs : E) * x) := by
    rcases Int.natAbs_eq m with h | h
    · rw [h, zsmul_eq_mul, Int.cast_natCast] at hi; exact hi
    · rw [h, neg_smul, zsmul_eq_mul, Int.cast_natCast] at hi; exact neg_neg ((m.natAbs : E) * x) ▸ hi.neg
  obtain ⟨r, hr⟩ : ∃ r : 𝓞 E, (r : E) = (m.natAbs : E) * x := ⟨⟨_, h1⟩, rfl⟩
  have e : (m.natAbs : Q.adicCompletion E) * (algebraMap E (FiniteAdeleRing (𝓞 E) E) x + 1 • a) Q =
      algebraMap E (Q.adicCompletion E) (r : E) + (m.natAbs : Q.adicCompletion E) * a Q := by
    rw [one_smul, hr]
    change _ * (algebraMap E (Q.adicCompletion E) x + a Q) = algebraMap E (Q.adicCompletion E) ((m.natAbs : E) * x) + _
    rw [map_mul, map_natCast, mul_add]
  rw [e]
  refine Valuation.map_add_le _ ?_ ?_
  · exact val_int_le Q r
  · rw [Valuation.map_mul]; exact mul_le_one' (val_nat_le Q _) (ha Q)

theorem approx_int (c : 𝓞 E ≃+* 𝓞 E) (hc : ∀ x, c (c x) = x) (δ : 𝓞 E) (hδ : c δ ≠ δ) (N : ℕ) (hN : 0 < N)
    (s s' : FiniteAdeleRing (𝓞 E) E) (h : s * s' = 1) (hs : ∀ Q, Valued.v (s Q) ≤ 1) :
    ∃ y : E, y ≠ 0 ∧ ∃ B : Set (HeightOneSpectrum (𝓞 E)), B.Finite ∧
      (∀ Q ∈ B, ¬ ∀ x ∈ Q.asIdeal, c x ∈ Q.asIdeal) ∧
      ∀ Q ∉ B, Valued.v (s Q * (algebraMap E (Q.adicCompletion E) y)⁻¹) = 1 ∧
        Valued.v (s Q * (algebraMap E (Q.adicCompletion E) y)⁻¹ - 1) ≤ Valued.v (N : Q.adicCompletion E) := by
  obtain ⟨m, hm, hm'⟩ := exists_den s'
  have hM : 0 < N * m * m := by positivity
  obtain ⟨y₀, a, ha, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E _ hM).2 s hs
  obtain ⟨t, ht0, ht⟩ := exists_avoid c hc δ hδ _ hM y₀
  refine ⟨((y₀ + (N * m * m : ℕ) * t : 𝓞 E) : E), by exact_mod_cast ht0,
    {Q | y₀ + (N * m * m : ℕ) * t ∈ Q.asIdeal ∧ ((N * m * m : ℕ) : 𝓞 E) ∉ Q.asIdeal},
    (finite_mem ht0).subset fun Q hQ => hQ.1, fun Q hQ h => ht Q h hQ.2 hQ.1, fun Q hQ => ?_⟩
  have h1 : s Q * s' Q = 1 := congrArg (fun z : FiniteAdeleRing (𝓞 E) E => z Q) h
  have hs0 : s Q ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have hms : Valued.v (m : Q.adicCompletion E) ≤ Valued.v (s Q) := by
    have : (m : Q.adicCompletion E) = (m * s' Q) * s Q := by rw [mul_assoc, mul_comm (s' Q), h1, mul_one]
    rw [this, Valuation.map_mul]
    exact mul_le_of_le_one_left' (hm' Q)
  by_cases hlt : Valued.v ((N : Q.adicCompletion E) * m) < 1
  · refine local_close _ hs0 hms (val_nat_le Q m) hlt ?_
    have e1 : s Q = algebraMap E (Q.adicCompletion E) (y₀ : E) + (N * m * m) • a Q := by rw [e]; rfl
    have e2 : algebraMap E (Q.adicCompletion E) ((y₀ + (N * m * m : ℕ) * t : 𝓞 E) : E) - s Q =
        (N : Q.adicCompletion E) * m * m * (algebraMap E (Q.adicCompletion E) (t : E) - a Q) := by
      rw [e1]
      simp only [map_add, map_mul, map_natCast, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [e2, Valuation.map_mul]
    exact mul_le_of_le_one_right' (Valuation.map_sub_le _ (val_int_le Q t) (ha Q))
  · refine local_unit _ (hs Q) hms (val_nat_le Q m) (val_nat_le Q N) hlt ?_
    refine le_antisymm (val_int_le Q _) (not_lt.1 fun h2 => hQ ⟨(val_int Q _).1 h2, fun h3 => hlt ?_⟩)
    have h4 : ((N * m : ℕ) : 𝓞 E) ∈ Q.asIdeal := by
      rw [Nat.cast_mul] at h3
      rcases Q.isPrime.mem_or_mem h3 with h3 | h3
      · exact h3
      · rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h3
    have h5 := (val_int Q _).2 h4
    simpa only [map_mul, map_natCast, Nat.cast_mul] using h5

end General

open GlobalTheory.IdemSupport

variable {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}

theorem ev_sub (a b : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)) : Φ (a - b) Q = Φ a Q - Φ b Q := by
  rw [map_sub]; rfl

theorem ev_one (Q : HeightOneSpectrum (𝓞 D.host.E)) : Φ 1 Q = 1 := by rw [map_one]; rfl

theorem ev_inc (hΦ : Comp D Φ) (y : D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (incA D y) Q = algebraMap D.host.E (Q.adicCompletion D.host.E) y := by rw [hΦ.inc]; rfl

theorem isSplitIdem_of_delta (hΦ : Comp D Φ) {P : HeightOneSpectrum (𝓞 D.host.E)} (hc : cP P ≠ P) {e : AE D}
    (he : IsDelta Φ P e) : IsSplitIdem D e := by
  obtain ⟨ε, hε⟩ := exists_placeIdem (D := D) (P.under (𝓞 D.host.F))
  obtain ⟨h0, h1, h2⟩ := place_comp hΦ hε
  have he' := delta_conj hΦ he
  refine ⟨delta_idem hΦ he, ?_, _, ε, hε, ?_⟩
  · refine hΦ.ext' (by rw [RingHom.map_mul, he.1, zero_mul, RingHom.map_zero]) fun Q => ?_
    rw [ev_mul, ev_zero]
    by_cases hQ : Q = P
    · subst hQ
      rw [he'.2.2 Q (Ne.symm hc), mul_zero]
    · rw [he.2.2 Q hQ, zero_mul]
  · refine hΦ.ext' (by rw [RingHom.map_add, he.1, he'.1, add_zero, h0]) fun Q => ?_
    rw [ev_add]
    by_cases hQ : Q = P
    · subst hQ
      rw [he.2.1, he'.2.2 Q (Ne.symm hc), add_zero, h1 Q rfl]
    · by_cases hQ' : Q = cP P
      · subst hQ'
        rw [he.2.2 _ hQ, he'.2.1, zero_add, h1 _ (under_cP P)]
      · rw [he.2.2 Q hQ, he'.2.2 Q hQ', add_zero, h2 Q fun h => (eq_or_eq_cP h).elim hQ hQ']

def part {A : Type} [CommRing A] {e : A} (he : e * e = e) (x : Aˣ) : Aˣ where
  val := e * x + (1 - e)
  inv := e * (x⁻¹ : Aˣ) + (1 - e)
  val_inv := by linear_combination ((x : A) * (x⁻¹ : Aˣ) - x - (x⁻¹ : Aˣ) + 1) * he + e * x.mul_inv
  inv_val := by linear_combination ((x : A) * (x⁻¹ : Aˣ) - x - (x⁻¹ : Aˣ) + 1) * he + e * x.mul_inv

theorem mul_part_inv {A : Type} [CommRing A] {e : A} (he : e * e = e) (x : Aˣ) :
    ((x * (part he x)⁻¹ : Aˣ) : A) = e + (1 - e) * x := by
  change (x : A) * (e * (x⁻¹ : Aˣ) + (1 - e)) = _
  linear_combination e * x.mul_inv

theorem mem_modSet (hΦ : Comp D Φ) {N : ℕ} (hN : 0 < N) (x : (AE D)ˣ) (h0 : infPart D (x : AE D) = 1)
    (h : ∀ Q, Valued.v (Φ x Q) = 1 ∧ Valued.v (Φ x Q - 1) ≤ Valued.v (N : Q.adicCompletion D.host.E)) :
    x ∈ modSet D N := by
  have hN' : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  refine ⟨h0, ⟨finPart D (((x : AE D) - 1) * incA D (N : D.host.E)⁻¹), (hΦ.int _).2 fun Q => ?_, ?_⟩,
    (hΦ.int _).2 fun Q => ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, ev_mul, ev_sub, ev_one, ev_inc hΦ, map_inv₀, map_natCast,
      Valuation.map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ (h Q).2 zero_le
  · have e : (N : AE D) * incA D (N : D.host.E)⁻¹ = 1 := by
      rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ hN', map_one]
    have e2 : (x : AE D) - 1 = N * (((x : AE D) - 1) * incA D (N : D.host.E)⁻¹) := by
      linear_combination (1 - (x : AE D)) * e
    have e3 := congrArg (finPart D) e2
    rwa [RingHom.map_sub, RingHom.map_one, RingHom.map_mul, map_natCast] at e3
  · have e : Φ x Q * Φ (x⁻¹ : (AE D)ˣ) Q = 1 := by rw [← ev_mul, Units.mul_inv, ev_one]
    have e2 := congrArg Valued.v e
    rw [Valuation.map_mul, (h Q).1, one_mul, Valuation.map_one] at e2
    exact e2.le

theorem mem_grpH_of_good (hΦ : Comp D Φ) {N : ℕ} (hN : 0 < N) {B : Set (HeightOneSpectrum (𝓞 D.host.E))}
    (hB : B.Finite) : (∀ P ∈ B, cP P ≠ P) → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 →
      (∀ Q ∉ B, Valued.v (Φ x Q) = 1 ∧ Valued.v (Φ x Q - 1) ≤ Valued.v (N : Q.adicCompletion D.host.E)) →
      x ∈ grpH D N := by
  induction B, hB using Set.Finite.induction_on with
  | empty =>
    exact fun _ x h0 h => Subgroup.subset_closure (Or.inr (mem_modSet hΦ hN x h0 fun Q => h Q (Set.notMem_empty Q)))
  | @insert P B _ _ ih =>
    intro hB x h0 h
    obtain ⟨e, he⟩ := exists_delta hΦ P
    have hs := isSplitIdem_of_delta hΦ (hB P (Set.mem_insert _ _)) he
    have h1 : part hs.1 x ∈ grpH D N := by
      refine Subgroup.subset_closure (Or.inl (Or.inr ⟨e, hs, ?_⟩))
      change (e + cA D e) * (e * x + (1 - e) - 1) = e * x + (1 - e) - 1
      linear_combination ((x : AE D) - 1) * hs.1 + ((x : AE D) - 1) * hs.2.1
    have h2 : x * (part hs.1 x)⁻¹ ∈ grpH D N := by
      refine ih (fun Q hQ => hB Q (Set.mem_insert_of_mem _ hQ)) _ ?_ fun Q hQ => ?_
      · rw [mul_part_inv, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, he.1, h0]
        simp
      · rw [mul_part_inv, ev_add, ev_mul, ev_sub, ev_one]
        by_cases hQP : Q = P
        · subst hQP
          rw [he.2.1]
          simp
        · rw [he.2.2 Q hQP, zero_add, sub_zero, one_mul]
          exact h Q fun h' => h'.elim hQP hQ
    simpa using mul_mem h2 h1

theorem exists_fin_idem (hΦ : Comp D Φ) :
    ∃ f : AE D, f * f = f ∧ infPart D f = 0 ∧ finPart D f = 1 ∧ Φ f = 1 := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have he1 : ∀ z, (e z).1 = infPart D z := fun z => (he z).1
  have he2 : ∀ z, (e z).2 = finPart D z := fun z => (he z).2
  obtain ⟨f, hf⟩ := e.surjective (0, 1)
  have hf0 : infPart D f = 0 := by rw [← he1, hf]
  have hf1 : finPart D f = 1 := by rw [← he2, hf]
  have key : ∀ g, infPart D g = 0 → g * f = g := fun g hg => e.injective (Prod.ext
    (by rw [he1, he1, RingHom.map_mul, hg, zero_mul]) (by rw [he2, he2, RingHom.map_mul, hf1, mul_one]))
  refine ⟨f, key f hf0, hf0, hf1, ?_⟩
  obtain ⟨g, hg0, hg1⟩ := hΦ.surj 1
  have h4 := congrArg Φ (key g hg0)
  rwa [map_mul, hg1, one_mul] at h4

theorem map_mix_zero {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {f : A} (h : φ f = 0) (x : A) :
    φ (f * x + (1 - f)) = 1 := by simp [h]

theorem map_mix_one {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {f : A} (h : φ f = 1) (x : A) :
    φ (f * x + (1 - f)) = φ x ∧ φ (f + (1 - f) * x) = 1 := by simp [h]

theorem exists_of_good (hΦ : Comp D Φ) {N : ℕ} (hN : 0 < N) {B : Set (HeightOneSpectrum (𝓞 D.host.E))}
    (hB : B.Finite) (hB1 : ∀ P ∈ B, cP P ≠ P) (x : (AE D)ˣ)
    (h : ∀ Q ∉ B, Valued.v (Φ x Q) = 1 ∧ Valued.v (Φ x Q - 1) ≤ Valued.v (N : Q.adicCompletion D.host.E)) :
    ∃ z : (AE D)ˣ, finPart D (z : AE D) = 1 ∧ x * z⁻¹ ∈ grpH D N := by
  obtain ⟨f, hf, hf0, hf1, hf2⟩ := exists_fin_idem hΦ
  have h3 : part hf x ∈ grpH D N := by
    refine mem_grpH_of_good hΦ hN hB hB1 _ (map_mix_zero _ hf0 _) fun Q hQ => ?_
    have : Φ (part hf x : (AE D)ˣ) = Φ x := (map_mix_one Φ hf2 _).1
    rw [this]
    exact h Q hQ
  refine ⟨x * (part hf x)⁻¹, ?_, ?_⟩
  · rw [mul_part_inv]
    exact (map_mix_one _ hf1 _).2
  · rwa [mul_inv, inv_inv, mul_inv_cancel_left]

theorem exists_not_fixed (D : D7) : ∃ δ : 𝓞 D.host.E, cO D δ ≠ δ := by
  by_contra h
  push Not at h
  have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (𝓞 D.host.E) x
    have ha : star (a : D.host.E) = a := congrArg (fun t : 𝓞 D.host.E => (t : D.host.E)) (h a)
    have hb : star (b : D.host.E) = b := congrArg (fun t : 𝓞 D.host.E => (t : D.host.E)) (h b)
    refine (D.sp.cm.fixed _).1 ?_
    change star ((a : D.host.E) / (b : D.host.E)) = (a : D.host.E) / (b : D.host.E)
    rw [star_div₀, ha, hb]
  have h1 : Module.finrank D.host.F D.host.E = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap D.host.F D.host.E).injective, hs⟩
  have h2 := D.sp.cm.deg2
  omega

theorem mem_of_mul_mem {G : Type} [CommGroup G] {H : Subgroup G} {a b x z : G} (ha : a ∈ H) (hb : b ∈ H)
    (h : a * x * b * z ∈ H) : x * z ∈ H := by
  have e : x * z = a⁻¹ * (a * x * b * z) * b⁻¹ := by
    rw [mul_right_comm _ b z, mul_assoc a⁻¹, mul_inv_cancel_right, mul_assoc a, inv_mul_cancel_left]
  rw [e]
  exact mul_mem (mul_mem (inv_mem ha) h) (inv_mem hb)

theorem exists_finPart_eq_one_mul_inv_mem : ∀ (D : D7) (N : ℕ), 0 < N → ∀ x : (AE D)ˣ, ∃ z : (AE D)ˣ, finPart D (z : AE D) = 1 ∧ x * z⁻¹ ∈ GlobalTheory.HeckeSplitAll.grpH D N := by
  intro D N hN x
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨δ, hδ⟩ := exists_not_fixed D
  obtain ⟨m, hm, hm'⟩ := exists_den (Φ x)
  have hm0 : (m : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hj : ∀ y : D.host.E, y ≠ 0 → ∃ u ∈ grpH D N, (u : AE D) = incA D y := fun y hy =>
    ⟨_, Subgroup.subset_closure (Or.inl (Or.inl ⟨Units.mk0 y hy, rfl⟩)), rfl⟩
  obtain ⟨a, ha, ha'⟩ := hj _ hm0
  have hx₁ : ∀ Q, Valued.v (Φ (a * x : (AE D)ˣ) Q) ≤ 1 := fun Q => by
    rw [Units.val_mul, ha', ev_mul, ev_inc hΦ, map_natCast]
    exact hm' Q
  obtain ⟨y, hy, B, hB, hB1, hB2⟩ := approx_int (cO D) cO_cO δ hδ N hN (Φ (a * x : (AE D)ˣ))
    (Φ ((a * x)⁻¹ : (AE D)ˣ)) (by rw [← map_mul, Units.mul_inv, map_one]) hx₁
  obtain ⟨b, hb, hb'⟩ := hj _ (inv_ne_zero hy)
  obtain ⟨z, hz, hz'⟩ := exists_of_good hΦ hN hB
    (fun P hP h => hB1 P hP fun t ht => (mem_cP P t).1 (h.symm ▸ ht)) (a * x * b) fun Q hQ => by
      rw [Units.val_mul, hb', ev_mul, ev_inc hΦ, map_inv₀]
      exact hB2 Q hQ
  exact ⟨z, hz, mem_of_mul_mem ha hb hz'⟩

end GlobalTheory.HeckeSplitAll.Fin

end

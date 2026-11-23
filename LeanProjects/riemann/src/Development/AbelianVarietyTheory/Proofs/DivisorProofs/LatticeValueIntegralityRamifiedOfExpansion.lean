import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerIntegralValuationLowerBoundIffForallEmbeddiStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal

namespace GlobalTheory.LatValRam

section Sz

variable {l : ℕ} [hl : Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem sz_mul {r₁ r₂ : ℝ} {x y : ℂ} (hx : Sz l lam r₁ x) (hy : Sz l lam r₂ y) :
    Sz l lam (r₁ + r₂) (x * y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul, norm_mul, Real.rpow_add (by exact_mod_cast hl.out.pos)]
  exact mul_le_mul hx' hy' (norm_nonneg _) (by positivity)

theorem sz_mono {r r' : ℝ} {x : ℂ} (hx : Sz l lam r x) (h : r ≤ r') : Sz l lam r' x := by
  obtain ⟨hx, hx'⟩ := hx
  exact ⟨hx, hx'.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hl.out.one_lt.le) h)⟩

theorem norm_nat_le (n : ℕ) : ‖(n : ℂ_[l])‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))

theorem sz_nat (n : ℕ) : Sz l lam 0 (n : ℂ) := by
  refine ⟨natCast_mem _ n, ?_⟩
  have : (⟨(n : ℂ), natCast_mem _ n⟩ : algebraicClosure ℚ ℂ) = (n : algebraicClosure ℚ ℂ) := rfl
  rw [this, map_natCast, Real.rpow_zero]
  exact norm_nat_le n

theorem sz_one : Sz l lam 0 1 := by simpa using sz_nat (l := l) (lam := lam) 1

theorem sz_neg {r : ℝ} {x : ℂ} (hx : Sz l lam r x) : Sz l lam r (-x) := by
  obtain ⟨hx, hx'⟩ := hx
  refine ⟨neg_mem hx, ?_⟩
  have : (⟨-x, neg_mem hx⟩ : algebraicClosure ℚ ℂ) = -⟨x, hx⟩ := rfl
  rwa [this, map_neg, norm_neg]

theorem sz_neg_one_pow_mul {r : ℝ} {x : ℂ} (n : ℕ) (hx : Sz l lam r x) : Sz l lam r ((-1) ^ n * x) := by
  rcases neg_one_pow_eq_or ℂ n with h | h
  · rwa [h, one_mul]
  · rw [h, neg_one_mul]; exact sz_neg hx

theorem sz_pow {r : ℝ} {x : ℂ} (hx : Sz l lam r x) (n : ℕ) : Sz l lam (n * r) (x ^ n) := by
  induction n with
  | zero => simpa using sz_one (l := l) (lam := lam)
  | succ n ih =>
    have := sz_mul ih hx
    rw [pow_succ]
    convert this using 1
    push_cast; ring

theorem sz_prod {ι : Type} (s : Finset ι) (r : ι → ℝ) (x : ι → ℂ) (h : ∀ i ∈ s, Sz l lam (r i) (x i)) :
    Sz l lam (∑ i ∈ s, r i) (∏ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sz_one (l := l) (lam := lam)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact sz_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Sz

theorem card_eq_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    {φ : I → E →+* ℂ} (h : IsCMType φ) : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E) := by
  have hreal : ∀ i j, φ i ≠ ComplexEmbedding.conjugate (φ j) := by
    intro i j hij
    obtain ⟨k, -, hk⟩ := h (φ i)
    have e : i = j := (hk i (Or.inl rfl)).trans (hk j (Or.inr hij)).symm
    subst e
    have hr : ComplexEmbedding.IsReal (φ i) := ComplexEmbedding.isReal_iff.mpr hij.symm
    exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex (InfinitePlace.mk (φ i)))
      (InfinitePlace.isReal_mk_iff.mpr hr)
  have hbij : Function.Bijective (Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))) := by
    refine ⟨?_, ?_⟩
    · rintro (i | i) (j | j) hij
      · simp only [Sum.elim_inl] at hij
        obtain ⟨k, -, hk⟩ := h (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl hij)]
      · exact absurd hij (hreal i j)
      · exact absurd hij.symm (hreal j i)
      · simp only [Sum.elim_inr] at hij
        have hij' : φ i = φ j := by
          simpa using congrArg ComplexEmbedding.conjugate hij
        obtain ⟨k, -, hk⟩ := h (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl hij')]
    · intro σ
      obtain ⟨k, hk, -⟩ := h σ
      rcases hk with hk | hk
      · exact ⟨Sum.inl k, hk.symm⟩
      · exact ⟨Sum.inr k, hk.symm⟩
  have h1 := Fintype.card_of_bijective hbij
  rw [Fintype.card_sum, NumberField.Embeddings.card E ℂ] at h1
  have h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  omega

theorem gamma_nat_add (k n : ℕ) (hk : 1 ≤ k) :
    Real.Gamma ((k : ℝ) + n) = ((k - 1).factorial : ℝ) * ∏ j ∈ Finset.range n, ((k : ℝ) + j) := by
  induction n with
  | zero =>
    have : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hk]; ring
    simp only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]
    rw [this, Real.Gamma_nat_eq_factorial]
  | succ n ih =>
    have hpos : (k : ℝ) + n ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      positivity
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hpos, ih]
    ring

theorem exists_list_count {I : Type} [Fintype I] [DecidableEq I] (κ : I → ℕ) :
    ∃ u : List I, ∀ i, u.count i = κ i := by
  refine ⟨(∑ i, Multiset.replicate (κ i) i).toList, fun i => ?_⟩
  rw [← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum', Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Multiset.count_replicate]
    simp [hj]
  · simp

theorem per_factor (a b Ω r π : ℂ) (k n : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hΩ : Ω ≠ 0) (hr : r ≠ 0) (hpi : π ≠ 0)
    (f : ℂ) (hf : f ≠ 0) :
    (b / a) ^ n / (a ^ k * f) * (f * ((a * b * r / (2 * π))⁻¹) ^ n * (a / Ω) ^ (k + 2 * n)) =
      (2 * π / r) ^ n / Ω ^ (k + 2 * n) := by
  simp only [inv_div, div_pow, pow_add, pow_mul, mul_pow]
  have h1 : a ^ n ≠ 0 := pow_ne_zero _ ha
  have h2 : b ^ n ≠ 0 := pow_ne_zero _ hb
  have h3 : r ^ n ≠ 0 := pow_ne_zero _ hr
  have h4 : Ω ^ k ≠ 0 := pow_ne_zero _ hΩ
  have h5 : (Ω ^ 2) ^ n ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hΩ)
  have h6 : a ^ k ≠ 0 := pow_ne_zero _ ha
  field_simp
  ring

theorem cmPeriodConstant_eq_of_card_cmType {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
    (hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E)) (d s : ℕ) (hs : 1 ≤ s) (κ : I → ℕ) :
    C0 E d (2 * s) κ = GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) *
      (∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) * (2 * Real.pi / Real.sqrt d) ^ (∑ i, κ i) := by
  have hk : 1 ≤ 2 * s := by omega
  rw [cmValueConst_eq, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt, Finset.prod_congr rfl (fun i _ => gamma_nat_add (2 * s) (κ i) hk),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
  ring

theorem risingFactor_eq {I : Type} [Fintype I] (k : ℕ) (κ : I → ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor k κ =
      (-1) ^ (∑ i, κ i) * (((∏ i, ∏ j ∈ Finset.range (κ i), ((k : ℝ) + j)) : ℝ) : ℂ) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  push_cast
  rfl

open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (ValGe_vp betaBound_vp c_vp cE_vp a0 n_vp) in

theorem latIntRam : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → Expansion → LatIntRam := by
  intro hSt hEx E _ _ _ _ I _ d φ s hF hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy hc κ S hS
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  rw [GlobalTheory.T.powerIntegralValuationLowerBound_iff_forall_embedding]
  intro lam
  obtain ⟨Ω, hΩ⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc Λ) (by norm_num : 0 < 12)
  have hΩ0 : Ω ≠ 0 := by
    rintro rfl
    exact latDisc_ne_zero Λ (by rw [← hΩ]; simp)
  obtain ⟨a, b, hab, hT⟩ := hEx E I d φ s hF hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy hc lam Ω hΩ
  have hCM : IsCMType φ := hF.2.2.2.2.2.2.1
  have hcard := card_eq_finrank hCM
  have hf2 : 2 ≤ Module.finrank ℚ (maximalRealSubfield E) := hcard ▸ hF.2.2.2.2.2.1
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    show 𝔣 * ∏ q ∈ Q, q.asIdeal ≠ 0
    exact mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  obtain ⟨⟨g, hg⟩, hD⟩ := (((hSt E I φ hf2 hCM).1 s hs).1 (condQ 𝔣 Q) y hc0).1
  obtain ⟨u, hu⟩ := exists_list_count κ
  have hDg := ((hD g hg).2 κ u hu).1 S hS
  have hTg := hT g κ u hg hu
  have hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hF.1.pos)
    exact_mod_cast this.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hper : ∀ i, (b i / a i) ^ κ i / (a i ^ (2 * s) * ((κ i).factorial : ℂ)) *
      (((κ i).factorial : ℂ) * ((a i * b i * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))⁻¹) ^ κ i *
        (a i / Ω) ^ (2 * s + 2 * κ i)) =
      (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ κ i / Ω ^ (2 * s + 2 * κ i) := by
    intro i
    exact per_factor _ _ _ _ _ _ _ (hab i).1 (hab i).2.1 hΩ0 hsd hpi _ (by exact_mod_cast (Nat.factorial_pos _).ne')
  have hX : ((C0 E d (2 * s) κ : ℝ) : ℂ) * S 0 / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ =
      (-1) ^ (∑ i, κ i) * ((GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 *
        ∏ i, ((b i / a i) ^ κ i / (a i ^ (2 * s) * ((κ i).factorial : ℂ))))) *
        ∏ i, (((κ i).factorial : ℂ) * ((a i * b i * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))⁻¹) ^ κ i *
          (a i / Ω) ^ (2 * s + 2 * κ i)) := by
    have hQF := Finset.prod_congr (s₁ := (Finset.univ : Finset I)) rfl (fun i _ => hper i)
    have hR : ∏ i, (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ κ i / Ω ^ (2 * s + 2 * κ i) =
        (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ (∑ i, κ i) / Ω ^ (Fintype.card I • (2 * s) + 2 * ∑ i, κ i) := by
      rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Finset.mul_sum]
    have hM : Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ = Fintype.card I • (2 * s) + 2 * ∑ i, κ i := by
      simp [Formalism.PairingDivisionLocalBalance.wtM, Formalism.PairingDivisionLocalBalance.absK, mul_comm]
    have hsq : ((-1 : ℂ) ^ (∑ i, κ i)) * (-1) ^ (∑ i, κ i) = 1 := by
      rw [← mul_pow]; norm_num
    rw [hDg, risingFactor_eq, cmPeriodConstant_eq_of_card_cmType hcard d s hs κ, hM]
    calc _ = ((GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℝ) : ℂ) *
          (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) * S 0 *
          ((2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ (∑ i, κ i) /
            Ω ^ (Fintype.card I • (2 * s) + 2 * ∑ i, κ i)) := by
            push_cast; ring
      _ = _ := by
        rw [← hR, ← hQF, Finset.prod_mul_distrib]
        linear_combination (-(((GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℝ) : ℂ) *
          (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) * S 0 *
          (∏ i, ((b i / a i) ^ κ i / (a i ^ (2 * s) * ((κ i).factorial : ℂ)))) *
          (∏ i, (((κ i).factorial : ℂ) * ((a i * b i * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))⁻¹) ^ κ i *
              (a i / Ω) ^ (2 * s + 2 * κ i))))) * hsq
  have hSzX : Sz l lam (betaBound_vp d s κ 𝔣 z l / 12)
      (((C0 E d (2 * s) κ : ℝ) : ℂ) * S 0 / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) := by
    rw [hX, mul_assoc]
    refine sz_neg_one_pow_mul _ (sz_mono (sz_mul hTg (sz_prod Finset.univ
      (fun i => (0 + ((κ i : ℕ) : ℝ) * (c_vp 𝔣 l + if l = d then 1 / 2 else 0)) +
        ((2 * s + 2 * κ i : ℕ) : ℝ) * (a0 𝔣 l : ℝ)) _
      (fun i _ => sz_mul (sz_mul (sz_nat _) (sz_pow (hab i).2.2.2 _)) (sz_pow (hab i).2.2.1 _)))) (le_of_eq ?_))
    simp only [betaBound_vp, n_vp, if_neg hc, Formalism.PairingDivisionLocalBalance.nl, Formalism.PairingDivisionLocalBalance.wtM, Formalism.PairingDivisionLocalBalance.absK]
    push_cast
    simp only [zero_add, add_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  have hβ : beta E d s κ Λ (S 0) = (((C0 E d (2 * s) κ : ℝ) : ℂ) * S 0 / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) ^ 12 := by
    rw [beta, div_pow, ← hΩ, ← pow_mul, ← pow_mul, mul_comm 12]
  rw [hβ]
  convert sz_pow hSzX 12 using 1
  push_cast
  ring

end GlobalTheory.LatValRam

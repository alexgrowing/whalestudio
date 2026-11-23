import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FTDefs
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExponentFactorialAddSingleOne
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationNonnegIffIntegral

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory MvPolynomial

theorem fact_multinomial_le (p : ℕ) {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℕ) :
    (Nat.multinomial s f).factorization p ≤ s.card * Nat.log p (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Nat.multinomial_insert ha, Nat.factorization_mul (Nat.choose_pos (Nat.le_add_right _ _)).ne'
      (Nat.multinomial_pos _ _).ne', Finsupp.add_apply, Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    have h1 := Nat.factorization_choose_le_log (p := p) (n := f a + ∑ i ∈ s, f i) (k := f a)
    have h2 : Nat.log p (∑ i ∈ s, f i) ≤ Nat.log p (f a + ∑ i ∈ s, f i) := Nat.log_mono_right (Nat.le_add_left _ _)
    calc _ ≤ Nat.log p (f a + ∑ i ∈ s, f i) + s.card * Nat.log p (f a + ∑ i ∈ s, f i) :=
          add_le_add h1 (ih.trans (Nat.mul_le_mul_left _ h2))
      _ = (s.card + 1) * Nat.log p (f a + ∑ i ∈ s, f i) := by ring

theorem pow_div_mem {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hp : p.Prime)
    (S : UniformizedDVR p O) (M κ : ℕ) (hM : M ≠ 0) (h : M.factorization p ≤ κ) :
    ∃ y : O, (p : KK O) ^ κ / (M : KK O) = algebraMap O (KK O) y := by
  have := dvr_fraction_field_char_zero hp S
  set v := M.factorization p with hv
  set M' := M / p ^ v with hM'
  have hMM : p ^ v * M' = M := Nat.ordProj_mul_ordCompl_eq_self M p
  have hnd : ¬ p ∣ M' := Nat.not_dvd_ordCompl hp hM
  obtain ⟨uu, hu⟩ := natCast_isUnit_of_coprime hp S M' hnd
  have hy : (↑(uu⁻¹) : O) * (M' : O) = 1 := by rw [← hu]; exact Units.inv_mul uu
  have hK : algebraMap O (KK O) (↑(uu⁻¹) : O) * (M' : KK O) = 1 := by
    rw [← map_natCast (algebraMap O (KK O)), ← map_mul, hy, map_one]
  have hne : (M : KK O) ≠ 0 := Nat.cast_ne_zero.2 hM
  refine ⟨(p : O) ^ (κ - v) * ↑(uu⁻¹), ?_⟩
  rw [div_eq_iff hne]
  have hMK : (M : KK O) = (p : KK O) ^ v * (M' : KK O) := by rw [← hMM]; push_cast; rfl
  have hpow : (p : KK O) ^ κ = (p : KK O) ^ (κ - v) * (p : KK O) ^ v := by rw [← pow_add, Nat.sub_add_cancel h]
  simp only [map_mul, map_pow, map_natCast]
  rw [hMK, hpow]
  linear_combination (-((p : KK O) ^ (κ - v) * (p : KK O) ^ v)) * hK

theorem factorial_exponent_eq_prod {ι : Type} [Fintype ι] {k : ℕ} (μ : ι × Fin k →₀ ℕ) :
    expFact μ = ∏ x : ι, ∏ c : Fin k, (μ (x, c)).factorial := by
  rw [expFact, Finsupp.prod_fintype _ _ (fun _ => rfl), Fintype.prod_prod_type]

theorem tensor_factorial_integral {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hp : p.Prime)
    (S : UniformizedDVR p O) {n' : ℕ} (m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ)
    (μ : (TT × Bool) × Fin (m + 1) →₀ ℕ) (hμ : ∀ x, multideg μ x = hhDegs TT aT bT x) :
    ∃ y : O, zTen (KK O) p m TT aT bT * (expFact μ : KK O) = algebraMap O (KK O) y := by
  classical
  have := dvr_fraction_field_char_zero hp S
  set M : ℕ := ∏ x : TT × Bool, Nat.multinomial Finset.univ (fun c : Fin (m + 1) => μ (x, c)) with hMdef
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => (Nat.multinomial_pos _ _).ne'
  have hEM : expFact μ * M = ∏ x : TT × Bool, (hhDegs TT aT bT x).factorial := by
    rw [factorial_exponent_eq_prod, hMdef, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Nat.multinomial_spec, ← hμ x]
    rfl
  have hfac : M.factorization p ≤ kapZ p m TT aT bT := by
    rw [hMdef, Nat.factorization_prod (fun x _ => (Nat.multinomial_pos _ _).ne'), Finsupp.finsetSum_apply]
    unfold kapZ
    refine Finset.sum_le_sum fun x _ => ?_
    have := fact_multinomial_le p (Finset.univ : Finset (Fin (m + 1))) (fun c => μ (x, c))
    rw [Finset.card_univ, Fintype.card_fin] at this
    rw [← hμ x]
    exact this
  obtain ⟨y, hy⟩ := pow_div_mem hp S M _ hM0 hfac
  refine ⟨y, ?_⟩
  rw [← hy]
  unfold zTen
  have hE0 : (expFact μ : KK O) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    intro h0
    rw [h0, zero_mul] at hEM
    exact (Finset.prod_ne_zero_iff.2 fun x _ => Nat.factorial_ne_zero _) hEM.symm
  have hMK : (M : KK O) ≠ 0 := Nat.cast_ne_zero.2 hM0
  have hcast : (∏ x : TT × Bool, ((hhDegs TT aT bT x).factorial : KK O)) = (expFact μ : KK O) * (M : KK O) := by
    rw [← Nat.cast_mul, hEM]
    push_cast
    rfl
  rw [hcast]
  field_simp

theorem intAt : IntAt := by
  intro p O _ _ _ hp S w n' m TT aT bT P hP Q i hPi hQ
  have hsup : ∀ μ ∈ P.support, ∀ x, multideg μ x = hhDegs TT aT bT x := by
    intro μ hμ
    have := ((mem_restrictSupport_iff _).1 hP) (Finset.mem_coe.2 hμ)
    exact this
  unfold fock
  rw [Finset.mul_sum]
  refine Finset.sum_induction _ (fun x => ∃ y : O, x = algebraMap O (KK O) (w ^ i * y)) ?_ ⟨0, by simp⟩ ?_
  · rintro _ _ ⟨y, rfl⟩ ⟨y', rfl⟩
    exact ⟨y + y', by rw [← map_add]; congr 1; ring⟩
  · intro μ hμ
    obtain ⟨c, hc⟩ := hPi μ
    obtain ⟨c', hc'⟩ := hQ μ
    obtain ⟨y, hy⟩ := tensor_factorial_integral hp S m TT aT bT μ (hsup μ hμ)
    refine ⟨c * c' * y, ?_⟩
    rw [hc, hc']
    have : zTen (KK O) p m TT aT bT * (algebraMap O (KK O) (w ^ i * c) * algebraMap O (KK O) c' * (expFact μ : KK O)) =
        algebraMap O (KK O) (w ^ i * c) * algebraMap O (KK O) c' * (zTen (KK O) p m TT aT bT * (expFact μ : KK O)) := by
      ring
    rw [this, hy, ← map_mul, ← map_mul]
    congr 1
    ring

end Formalism.MainNotions.ColumnSystems.Pf

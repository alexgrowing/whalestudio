import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysPrism.ShMem

theorem coeff_iterate_derivative' {R : Type} [CommRing R] (f : R⟦X⟧) (i n : ℕ) :
    coeff n ((PowerSeries.derivative R)^[i] f) = ((n + i).descFactorial i : R) * coeff (n + i) f := by
  induction i generalizing f with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih, PowerSeries.coeff_derivative, ← add_assoc,
      Nat.succ_descFactorial_succ]
    push_cast; ring

theorem charZero_of_ql {l : ℕ} [Fact l.Prime] {K : Type} [NormedField K] [NormedAlgebra ℚ_[l] K] : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective

theorem coeff_sh {K : Type} [NormedField K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f)
    (e : ℕ) (f : K⟦X⟧) (i n : ℕ) :
    ((i.factorial * (n / e).factorial : ℕ) : K) * coeff n (coeff i (sh f)) =
      (((n / e).factorial * (n + i).descFactorial i : ℕ) : K) * coeff (n + i) f := by
  have h := congrArg (coeff n) (hsh f i)
  rw [← map_natCast (C : K →+* K⟦X⟧), coeff_C_mul, coeff_iterate_derivative'] at h
  push_cast
  rw [mul_comm (i.factorial : K), mul_assoc, h]; ring

theorem eventually_dvd {l : ℕ} [hl : Fact l.Prime] {e : ℕ} [NeZero e] (r : ℕ) :
    ∀ᶠ p : ℕ × ℕ in cofinite, l ^ r ∣ (p.2 / e).factorial * (p.2 + p.1).descFactorial p.1 := by
  rw [Filter.eventually_cofinite]
  refine ((Set.finite_lt_nat (l ^ r)).prod (Set.finite_lt_nat (e * l ^ r))).subset ?_
  rintro ⟨i, n⟩ h
  simp only [Set.mem_setOf_eq] at h
  refine ⟨?_, ?_⟩
  · show i < l ^ r
    by_contra hi; push_neg at hi
    exact h (Dvd.dvd.mul_left ((Nat.dvd_factorial (pow_pos hl.out.pos r) hi).trans
      (Nat.factorial_dvd_descFactorial _ _)) _)
  · show n < e * l ^ r
    by_contra hn; push_neg at hn
    apply h
    apply Dvd.dvd.mul_right
    apply Nat.dvd_factorial (pow_pos hl.out.pos r)
    exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (NeZero.ne e))).2 (by rw [mul_comm]; exact hn)

theorem dvd_descFactorial {l n i : ℕ} (hi : i ≠ 0) (h : l ∣ n + i) : l ∣ (n + i).descFactorial i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  rw [show n + j.succ = (n + j) + 1 from rfl, Nat.succ_descFactorial_succ]
  exact h.mul_right _

section Main

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a]

def nSh (e : ℕ) (p : ℕ × ℕ) : ℕ := (p.2 / e).factorial * (p.2 + p.1).descFactorial p.1

variable (l a) in

def wSh (e : ℕ) (x : (Wq l a)⟦X⟧) (p : ℕ × ℕ) : Wq l a :=
  (nSh e p : Wq l a) * coeff (p.2 + p.1) (frobS l a x)

def wDiff (e : ℕ) (x : (Wq l a)⟦X⟧) (p : ℕ × ℕ) : Wq l a :=
  if p.1 ≠ 0 ∧ l ∣ nSh e p then ((nSh e p / l : ℕ) : Wq l a) * coeff (p.2 + p.1) (frobS l a x) else 0

theorem coeff_frobS_eq_zero (x : (Wq l a)⟦X⟧) {m : ℕ} (h : ¬ l ∣ m) : coeff m (frobS l a x) = 0 := by
  have : coeff m (frobS l a x) = if l ∣ m then sigma l a (coeff (m / l) x) else 0 := by
    simp only [frobS, RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_expand]
    split_ifs <;> simp
  rw [this, if_neg h]

theorem tendsToZero_crystallinePrismShiftedFrobeniusCoeff {e : ℕ} [NeZero e] (x : (Wq l a)⟦X⟧) : LTo0 l (wSh l a e x) := fun r =>
  (eventually_dvd (l := l) (e := e) r).mono fun p hp => by
    have h := Nat.cast_dvd_cast (α := Wq l a) hp
    rw [Nat.cast_pow] at h
    exact h.mul_right _

theorem tendsToZero_crystallinePrismShiftedCoeffDivPrime {e : ℕ} [NeZero e] (x : (Wq l a)⟦X⟧) : LTo0 l (wDiff e x) := fun r =>
  (eventually_dvd (l := l) (e := e) (r + 1)).mono fun p hp => by
    unfold wDiff
    split_ifs with h
    · have h2 : l ^ r ∣ nSh e p / l := Nat.dvd_div_of_mul_dvd (by rw [← pow_succ']; exact hp)
      have h3 := Nat.cast_dvd_cast (α := Wq l a) h2
      rw [Nat.cast_pow] at h3
      exact h3.mul_right _
    · exact dvd_zero _

end Main

theorem shP_frob_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → ∀ x : (Wq l a)⟦X⟧, shP a sh (inclS t K (frobS l a x)) ∈ PPSet t K e ∧ ∃ B ∈ PPSet t K e, shP a sh (inclS t K (frobS l a x)) - constP a K (inclS t K (frobS l a x)) = (l : ZMod a → K⟦X⟧⟦X⟧) * B := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t sh hsh x
  haveI : CharZero K := charZero_of_ql (l := l)
  have hkey : ∀ τ i n, ((i.factorial * (n / e).factorial : ℕ) : K) *
      coeff n (coeff i (sh (toAc t K (frobS l a x) τ : K⟦X⟧))) = algebraMap O K (emb t τ (wSh l a e x (i, n))) := by
    intro τ i n
    rw [coeff_sh sh hsh e, coeff_toAc]
    simp only [wSh, nSh, map_mul, map_natCast, Nat.cast_mul]
  have hD : ∀ i n : ℕ, ((i.factorial * (n / e).factorial : ℕ) : K) ≠ 0 := fun i n =>
    Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
  refine ⟨⟨wSh l a e x, tendsToZero_crystallinePrismShiftedFrobeniusCoeff x, fun τ i n => hkey τ i n⟩,
    fun τ => mk fun i => mk fun n => algebraMap O K (emb t τ (wDiff e x (i, n))) /
      ((i.factorial * (n / e).factorial : ℕ) : K), ⟨wDiff e x, tendsToZero_crystallinePrismShiftedCoeffDivPrime x, fun τ i n => ?_⟩, ?_⟩
  · simp only [coeff_mk]; exact mul_div_cancel₀ _ (hD i n)
  · funext τ
    refine PowerSeries.ext fun i => PowerSeries.ext fun n => ?_
    change coeff n (coeff i (sh (toAc t K (frobS l a x) τ : K⟦X⟧) - C (toAc t K (frobS l a x) τ : K⟦X⟧))) =
      coeff n (coeff i ((l : K⟦X⟧⟦X⟧) * mk fun i => mk fun n => algebraMap O K (emb t τ (wDiff e x (i, n))) /
        ((i.factorial * (n / e).factorial : ℕ) : K)))
    rw [← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), coeff_C_mul, ← map_natCast (C : K →+* K⟦X⟧), coeff_C_mul,
      coeff_mk, coeff_mk, map_sub, map_sub, coeff_C]
    by_cases hi : i = 0
    · subst hi
      have h0 : wDiff e x (0, n) = 0 := by simp [wDiff]
      rw [if_pos rfl, coeff_zero_eq_constantCoeff_apply, constantCoeff_sh sh hsh, sub_self, h0]
      simp
    · rw [if_neg hi, map_zero, sub_zero]
      apply mul_left_cancel₀ (hD i n)
      rw [hkey, mul_left_comm, mul_div_cancel₀ _ (hD i n)]
      unfold wDiff
      split_ifs with h
      · have h1 : (nSh e (i, n) : Wq l a) = l * ((nSh e (i, n) / l : ℕ) : Wq l a) := by
          rw [← Nat.cast_mul, Nat.mul_div_cancel' h.2]
        simp only [wSh, h1, map_mul, map_natCast]
        ring
      · have hn : ¬ l ∣ n + i := fun hd => h ⟨hi, (dvd_descFactorial hi hd).mul_left _⟩
        simp [wSh, coeff_frobS_eq_zero x hn]

end GlobalTheory.CrysPrism.ShMem

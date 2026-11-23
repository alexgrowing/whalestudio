import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.IdemDen
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.IntegralPartDecomposition

open scoped TensorProduct NumberField nonZeroDivisors
open Module UniqueFactorizationMonoid IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.IndefiniteRowSideFullHecke.IntegralPartDecomposition

noncomputable section

namespace GlobalTheory.IdemCompare

variable {E : Type} [Field E] [NumberField E] {C : Type} [Field C] [CharZero C]

theorem evAt_eq (σ : E →+* C) : evAt σ = evalAt σ := rfl

theorem trDual_ratBasis {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ (𝓞 E)) :
    trDual (ratBasis b) = dualBasis b := by
  rename_i inst
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  rfl

theorem trDual_eq {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι ℚ E) :
    trDual b = b.traceDual := by
  unfold trDual
  rw [Basis.traceDual_def]

theorem sum_dual_swap {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Basis ι ℚ E) (c : Basis κ ℚ E) (τ : E →+* C) :
    ∑ i, b.traceDual i ⊗ₜ[ℚ] τ (b i) = ∑ j, c j ⊗ₜ[ℚ] τ (c.traceDual j) := by
  have h1 : ∀ i, b.traceDual i = ∑ j, Algebra.trace ℚ E (b.traceDual i * c.traceDual j) • c j := by
    intro i
    conv_lhs => rw [← c.traceDual.traceDual.sum_repr (b.traceDual i)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Basis.traceDual_repr_apply, Algebra.traceForm_apply, Basis.traceDual_traceDual]
  have h2 : ∀ j, c.traceDual j = ∑ i, Algebra.trace ℚ E (b.traceDual i * c.traceDual j) • b i := by
    intro j
    conv_lhs => rw [← b.traceDual.traceDual.sum_repr (c.traceDual j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Basis.traceDual_repr_apply, Algebra.traceForm_apply, Basis.traceDual_traceDual, mul_comm]
  calc ∑ i, b.traceDual i ⊗ₜ[ℚ] τ (b i)
      = ∑ i, ∑ j, Algebra.trace ℚ E (b.traceDual i * c.traceDual j) • (c j ⊗ₜ[ℚ] τ (b i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_lhs => rw [h1 i, TensorProduct.sum_tmul]
        simp only [TensorProduct.smul_tmul']
    _ = ∑ j, c j ⊗ₜ[ℚ] τ (c.traceDual j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        conv_rhs => rw [h2 j, map_sum, TensorProduct.tmul_sum]
        simp only [map_rat_smul, TensorProduct.tmul_smul]

theorem idemOf_eq_idem {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (b : Basis ι ℚ E) (c : Basis κ ℤ (𝓞 E)) (τ : E →+* C) : idemOf b τ = idem c τ := by
  classical
  unfold idemOf idem dualBasis
  rw [trDual_eq]
  simp only [← ratBasis_apply]
  exact sum_dual_swap b (ratBasis c) τ

theorem integral_iff_ratBasis {ι : Type} [Fintype ι] (b : Basis ι ℚ E) :
    ((∀ i, IsIntegral ℤ (b i)) ∧ ∀ x : 𝓞 E, ∃ c : ι → ℤ, (x : E) = ∑ i, (c i : ℚ) • b i) ↔
      ∃ c : Basis ι ℤ (𝓞 E), ratBasis c = b := by
  constructor
  · rintro ⟨h1, h2⟩
    let v : ι → 𝓞 E := fun i => ⟨b i, h1 i⟩
    have hli : LinearIndependent ℤ v := by
      have : LinearIndependent ℤ (fun i => b i) := b.linearIndependent.restrict_scalars' ℤ
      exact LinearIndependent.of_comp (IsScalarTower.toAlgHom ℤ (𝓞 E) E).toLinearMap this
    have hsp : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
      intro x _
      obtain ⟨c, hc⟩ := h2 x
      have : x = ∑ i, c i • v i := by
        apply NumberField.RingOfIntegers.ext
        rw [hc]
        simp only [map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
        rfl
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    refine ⟨Basis.mk hli hsp, ?_⟩
    ext i
    rw [ratBasis_apply, Basis.mk_apply]
    rfl
  · rintro ⟨c, rfl⟩
    refine ⟨fun i => ?_, fun x => ⟨c.repr x, ?_⟩⟩
    · rw [ratBasis_apply]; exact (c i).isIntegral_coe
    · conv_lhs => rw [← c.sum_repr x]
      simp [ratBasis_apply, Int.cast_smul_eq_zsmul]

open Classical in

theorem eval_iff {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (b : Basis ι ℚ E) (c : Basis κ ℤ (𝓞 E)) (τ : E →+* C) :
    (∀ σ : E →+* C, evAt σ (idemOf b τ) = if σ = τ then 1 else 0) ↔ EvalClaim c τ := by
  rw [idemOf_eq_idem b c τ]
  simp only [evAt_eq]
  constructor
  · intro h
    exact ⟨by rw [h, if_pos rfl], fun σ hσ => by rw [h, if_neg hσ]⟩
  · rintro ⟨h1, h2⟩ σ
    split_ifs with hσ
    · rw [hσ, h1]
    · exact h2 σ hσ

theorem idemEvalSt_iff :
    IdemEvalSt ↔ ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
      [IsAlgClosed C] (ι : Type) [Fintype ι] (b : Basis ι ℤ (𝓞 E)) (τ : E →+* C),
      EvalClaim b τ := by
  classical
  constructor
  · intro h E _ _ C _ _ _ ι _ b τ
    exact (eval_iff (ratBasis b) b τ).1 fun σ => h E C ι (ratBasis b) τ σ
  · intro h E _ _ C _ _ _ ι _ _ b τ
    exact (eval_iff b (NumberField.RingOfIntegers.basis E) τ).2 (h E C _ _ τ)

theorem sum_mem_integralPart_iff {ι : Type} [Fintype ι] (b : Basis ι ℤ (𝓞 E)) (R : Subring C)
    (x : ι → C) :
    ∑ i, ((b i : 𝓞 E) : E) ⊗ₜ[ℚ] x i ∈ integralPart E R ↔ ∀ i, x i ∈ R := by
  classical
  constructor
  · rintro ⟨t, ht⟩ i
    have key : ∀ t : (𝓞 E) ⊗[ℤ] R, ∃ y : ι → C, (∀ i, y i ∈ R) ∧
        integralMap E R t = ∑ i, ((b i : 𝓞 E) : E) ⊗ₜ[ℚ] y i := by
      intro t
      induction t with
      | zero => exact ⟨0, fun _ => R.zero_mem, by simp⟩
      | tmul a r =>
        refine ⟨fun i => (b.repr a i : C) * r, fun i => R.mul_mem (intCast_mem R _) r.2, ?_⟩
        rw [integralMap_tmul]
        have ha : (a : E) = ∑ i, ((b.repr a i : ℤ) : ℚ) • ((b i : 𝓞 E) : E) := by
          conv_lhs => rw [← b.sum_repr a]
          simp [Int.cast_smul_eq_zsmul]
        rw [ha, TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [TensorProduct.smul_tmul, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
      | add s t hs ht =>
        obtain ⟨y, hy, hy'⟩ := hs
        obtain ⟨z, hz, hz'⟩ := ht
        refine ⟨y + z, fun i => R.add_mem (hy i) (hz i), ?_⟩
        rw [map_add, hy', hz', ← Finset.sum_add_distrib]
        simp [TensorProduct.tmul_add]
    obtain ⟨y, hy, hy'⟩ := key t
    have ht' : ∑ i, ratBasis b i ⊗ₜ[ℚ] y i = ∑ i, ratBasis b i ⊗ₜ[ℚ] x i := by
      simp only [ratBasis_apply]
      rw [← hy']; exact ht
    have h2 := congrArg (fun z => TensorProduct.lid ℚ C
      (TensorProduct.map ((ratBasis b).coord i) LinearMap.id z)) ht'
    simp [Finsupp.single_apply, map_sum, ite_smul] at h2
    rw [← h2]; exact hy i
  · intro h
    refine Subring.sum_mem _ fun i _ => ⟨b i ⊗ₜ[ℤ] ⟨x i, h i⟩, ?_⟩
    exact integralMap_tmul R (b i) ⟨x i, h i⟩

theorem mul_idem_mem_iff {ι : Type} [Fintype ι] (b : Basis ι ℤ (𝓞 E)) (τ : E →+* C)
    (R : Subring C) (c : C) :
    ((1 : E) ⊗ₜ[ℚ] c) * idem b τ ∈ integralPart E R ↔ ∀ i, c * τ (dualBasis b i) ∈ R := by
  rw [← sum_mem_integralPart_iff b R]
  simp [idem, Finset.mul_sum]

theorem den_iff {ι : Type} [Fintype ι] (b : Basis ι ℤ (𝓞 E)) (τ : E →+* C) (δ : E) :
    (∀ i, IsIntegral ℤ (δ * dualBasis b i)) ↔
      ∀ R : Subring C, (∀ a : 𝓞 E, τ (a : E) ∈ R) →
        ((1 : E) ⊗ₜ[ℚ] τ δ) * idem b τ ∈ integralPart E R := by
  simp only [mul_idem_mem_iff, ← map_mul]
  constructor
  · intro h R hR i
    exact hR ⟨_, h i⟩
  · intro h i
    obtain ⟨a, ha⟩ := h (τ.comp (algebraMap (𝓞 E) E)).range (fun a => ⟨a, rfl⟩) i
    have : (a : E) = δ * dualBasis b i := τ.injective ha
    rw [← this]; exact a.isIntegral_coe

theorem different_iff {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ (𝓞 E))
    (τ : E →+* C) :
    (∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ i, IsIntegral ℤ ((δ : E) * trDual (ratBasis b) i)) ↔
      DifferentClaim b τ := by
  rw [trDual_ratBasis]
  simp only [den_iff b τ]
  exact ⟨fun h R hR δ hδ => h δ hδ R hR, fun h δ hδ R hR => h R hR δ hδ⟩

theorem dualDiffSt_iff :
    DualDiffSt ↔ ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
      [IsAlgClosed C] (ι : Type) [Fintype ι] (b : Basis ι ℤ (𝓞 E)) (τ : E →+* C),
      DifferentClaim b τ := by
  classical
  constructor
  · intro h E _ _ C _ _ _ ι _ b τ
    obtain ⟨h1, h2⟩ := (integral_iff_ratBasis (ratBasis b)).2 ⟨b, rfl⟩
    exact (different_iff b τ).1 (h E ι _ h1 h2)
  · intro h E _ _ ι _ _ b h1 h2
    obtain ⟨c, rfl⟩ := (integral_iff_ratBasis b).1 ⟨h1, h2⟩
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact (different_iff c τ).2 (h E ℂ ι c τ)

theorem integer_mem (O : ValuationSubring C) (τ : E →+* C) {x : E} (hx : IsIntegral ℤ x) :
    τ x ∈ O := by
  have h1 : IsIntegral ℤ (τ x) := hx.map τ.toIntAlgHom
  have h2 : IsIntegral O (τ x) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h2
  rw [← hy]; exact y.2

theorem val_pow_le (O : ValuationSubring C) (τ : E →+* C) (I : Ideal (𝓞 E)) (u : O.ValueGroup)
    (h : ∀ x ∈ I, O.valuation (τ (x : E)) * u ≤ 1) (n : ℕ) :
    ∀ z ∈ I ^ n, O.valuation (τ (z : E)) * u ^ n ≤ 1 := by
  induction n with
  | zero =>
    intro z _
    rw [pow_zero, mul_one]
    exact (O.valuation_le_one_iff _).2 (integer_mem O τ z.isIntegral_coe)
  | succ n ih =>
    intro z hz
    rw [pow_succ] at hz
    refine Submodule.mul_induction_on hz (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · have := mul_le_one' (ih x hx) (h y hy)
      simp only [map_mul]
      calc _ = O.valuation (τ (x : E)) * u ^ n * (O.valuation (τ (y : E)) * u) := by
            rw [pow_succ]; ac_rfl
        _ ≤ 1 := this
    · simp only [map_add]
      rcases le_max_iff.1 (O.valuation.map_add (τ (x : E)) (τ (y : E))) with h1 | h1
      · exact (mul_le_mul_left h1 _).trans hx
      · exact (mul_le_mul_left h1 _).trans hy

theorem val_eq_one {O : ValuationSubring C} {τ : E →+* C} {w : HeightOneSpectrum (𝓞 E)}
    (hw : Induces O τ w) {s : 𝓞 E} (hs : s ∉ w.asIdeal) : O.valuation (τ (s : E)) = 1 :=
  le_antisymm ((O.valuation_le_one_iff _).2 (integer_mem O τ s.isIntegral_coe))
    (not_lt.1 fun h => hs ((hw s).2 h))

omit [NumberField E] in
theorem exists_not_mem {w : HeightOneSpectrum (𝓞 E)} {Q : Ideal (𝓞 E)}
    (h : w.asIdeal ⊔ Q = ⊤) : ∃ s ∈ Q, s ∉ w.asIdeal := by
  by_contra hh
  push Not at hh
  exact w.isPrime.ne_top (by rw [← h]; exact (sup_eq_left.2 hh).symm)

theorem differentClaim_iff_vp {ι : Type} [Fintype ι] (b : Basis ι ℤ (𝓞 E)) (τ : E →+* C) :
    DifferentClaim b τ ↔ DifferentClaim_vp b τ := by
  classical
  have hD : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  rw [← different_iff, trDual_ratBasis]
  constructor
  · intro h p hp O hO w hw c hc
    rw [mul_idem_mem_iff]
    intro i
    have := w.isMaximal
    have hp0 : Ideal.span {(p : 𝓞 E)} ≠ ⊥ := by simpa using hp.ne_zero
    obtain ⟨J, hJ, hJ'⟩ := Ideal.eq_prime_pow_mul_coprime hD w.asIdeal
    obtain ⟨K, hK, hK'⟩ := Ideal.eq_prime_pow_mul_coprime hp0 w.asIdeal
    change _ = w.asIdeal ^ differentExp_vw w * J at hJ'
    change _ = w.asIdeal ^ ramExp p w * K at hK'
    have hpw : (p : 𝓞 E) ∈ w.asIdeal := (hw _).2 (by simpa using hO)
    have he : ramExp p w ≠ 0 := by
      intro h0
      obtain ⟨s, hs, hs'⟩ := exists_not_mem hK
      rw [h0, pow_zero, one_mul] at hK'
      rw [← hK'] at hs
      exact hs' ((Ideal.span_singleton_le_iff_mem _).2 hpw hs)
    obtain ⟨s, hs, hs'⟩ := exists_not_mem hJ
    have h1 : ∀ x ∈ w.asIdeal ^ differentExp_vw w,
        O.valuation (τ (x : E)) * O.valuation (τ (dualBasis b i)) ≤ 1 := by
      intro x hx
      have := (O.valuation_le_one_iff _).2
        (integer_mem O τ (h (x * s) (by rw [hJ']; exact Ideal.mul_mem_mul hx hs) i))
      simpa only [map_mul, val_eq_one hw hs', mul_one] using this
    have hpe : (p : 𝓞 E) ∈ w.asIdeal ^ ramExp p w :=
      Ideal.mul_le_left (by rw [← hK']; exact Ideal.mem_span_singleton_self _)
    have h2 := val_pow_le O τ _ _ h1 (ramExp p w) ((p : 𝓞 E) ^ differentExp_vw w) (by
      rw [← pow_mul, mul_comm, pow_mul]; exact Ideal.pow_mem_pow hpe _)
    simp only [map_pow, map_natCast] at h2
    have h3 : (O.valuation (c * τ (dualBasis b i))) ^ ramExp p w ≤ 1 := by
      rw [map_mul, mul_pow]
      exact (mul_le_mul_left hc _).trans h2
    exact (O.valuation_le_one_iff _).1 ((pow_le_one_iff he).1 h3)
  · intro h δ hδ i
    by_contra hx
    have hx' : τ ((δ : E) * dualBasis b i) ∉ (integralClosure ℤ C).toSubring := fun hh =>
      hx ((isIntegral_algHom_iff τ.toIntAlgHom τ.injective).1 hh)
    have : IsIntegrallyClosedIn (integralClosure ℤ C).toSubring C :=
      Subring.isIntegrallyClosedIn_iff.mpr fun x hx =>
        isIntegral_trans (R := ℤ) (A := integralClosure ℤ C) x hx
    obtain ⟨O, -, hO⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hx'
    obtain ⟨p, hp, hpO⟩ : ∃ p : ℕ, p.Prime ∧ O.valuation (p : C) < 1 := by
      by_contra hh
      push Not at hh
      have hn : ∀ n : ℕ, n ≠ 0 → O.valuation (n : C) = 1 := by
        intro n
        induction n using induction_on_primes with
        | zero => simp
        | one => simp
        | prime_mul p a hp ih =>
          intro h0
          rw [Nat.cast_mul, map_mul, ih (right_ne_zero_of_mul h0), mul_one]
          exact le_antisymm ((O.valuation_le_one_iff _).2 (natCast_mem O p)) (hh p hp)
      obtain ⟨k, hk, hki⟩ := exists_integral_multiples ℤ ℚ ({(δ : E) * dualBasis b i} : Finset E)
      have h1 := (O.valuation_le_one_iff _).2
        (integer_mem O τ (hki _ (Finset.mem_singleton_self _)))
      have h2 : O.valuation (k : C) = 1 := by
        have := hn k.natAbs (by simpa using hk)
        rcases Int.natAbs_eq k with h3 | h3
        · rw [h3]; simpa using this
        · rw [h3]; simpa using this
      rw [zsmul_eq_mul, map_mul, map_mul, map_intCast, h2, one_mul] at h1
      exact hO ((O.valuation_le_one_iff _).1 h1)
    let φ : 𝓞 E →+* O := (τ.comp (algebraMap (𝓞 E) E)).codRestrict O
      fun a => integer_mem O τ a.isIntegral_coe
    have hφ : ∀ a : 𝓞 E, a ∈ (IsLocalRing.maximalIdeal O).comap φ ↔
        O.valuation (τ (a : E)) < 1 := fun a => by
      rw [Ideal.mem_comap, O.valuation_lt_one_iff]; rfl
    have hpw : (p : 𝓞 E) ∈ (IsLocalRing.maximalIdeal O).comap φ := (hφ _).2 (by simpa using hpO)
    let w : HeightOneSpectrum (𝓞 E) := ⟨(IsLocalRing.maximalIdeal O).comap φ, inferInstance,
      fun h0 => hp.ne_zero (by rw [h0] at hpw; simpa using hpw)⟩
    have hw : Induces O τ w := hφ
    have := w.isMaximal
    have hp0 : Ideal.span {(p : 𝓞 E)} ≠ ⊥ := by simpa using hp.ne_zero
    obtain ⟨J, hJ, hJ'⟩ := Ideal.eq_prime_pow_mul_coprime hD w.asIdeal
    obtain ⟨K, hK, hK'⟩ := Ideal.eq_prime_pow_mul_coprime hp0 w.asIdeal
    change _ = w.asIdeal ^ differentExp_vw w * J at hJ'
    change _ = w.asIdeal ^ ramExp p w * K at hK'
    obtain ⟨s, hs, hs'⟩ := exists_not_mem hK
    have hδw : δ ∈ w.asIdeal ^ differentExp_vw w := Ideal.mul_le_left (by rwa [← hJ'])
    have hmem : δ ^ ramExp p w * s ^ differentExp_vw w ∈
        Ideal.span {(p : 𝓞 E) ^ differentExp_vw w} := by
      rw [← Ideal.span_singleton_pow, hK', mul_pow, ← pow_mul, mul_comm (ramExp p w), pow_mul]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hδw _) (Ideal.pow_mem_pow hs _)
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hmem
    have hv : ValGeDifferent_vp O p w (τ (δ : E)) := by
      have h1 := congrArg (fun a : 𝓞 E => O.valuation (τ (a : E))) ht
      simp only [map_mul, map_pow, map_natCast, val_eq_one hw hs', one_pow, mul_one] at h1
      unfold ValGeDifferent_vp
      rw [← h1]
      exact mul_le_of_le_one_left'
        ((O.valuation_le_one_iff _).2 (integer_mem O τ t.isIntegral_coe))
    have := (mul_idem_mem_iff b τ _ _).1 (h p hp O hpO w hw _ hv) i
    exact hO (by rw [map_mul]; exact this)

theorem dualDiffSt_iff_vp :
    DualDiffSt ↔ ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
      [IsAlgClosed C] (ι : Type) [Fintype ι] (b : Basis ι ℤ (𝓞 E)) (τ : E →+* C),
      DifferentClaim_vp b τ := by
  simp only [dualDiffSt_iff, differentClaim_iff_vp]

end GlobalTheory.IdemCompare

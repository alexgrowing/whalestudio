import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTranslationInvariantSubfieldIffExponents
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.NTr

theorem zt_prim {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p n : ℕ) (hp : 0 < p) :
    IsPrimitiveRoot (zt ε p n) (p ^ n) := by
  have h := GlobalTheory.Glue.KTExp.map_eOm ε (1 / (p : ℚ) ^ n)
  have hn : p ^ n ≠ 0 := pow_ne_zero _ hp.ne'
  have hc := Complex.isPrimitiveRoot_exp (p ^ n) hn
  have e : Complex.exp (2 * Real.pi * Complex.I * (((1 / (p : ℚ) ^ n : ℚ)) : ℂ)) = Complex.exp (2 * Real.pi * Complex.I / ((p ^ n : ℕ) : ℂ)) := by
    congr 1; push_cast; ring
  rw [e] at h
  unfold zt
  rw [← h] at hc
  exact (IsPrimitiveRoot.map_iff_of_injective ε.injective).mp hc

theorem zt_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p L m : ℕ) (hp : 0 < p) (hm : m ≤ L) :
    zt ε p L ^ (p ^ (L - m)) = zt ε p m := by
  apply ε.injective
  unfold zt
  rw [map_pow, GlobalTheory.Glue.KTExp.map_eOm, GlobalTheory.Glue.KTExp.map_eOm, ← Complex.exp_nat_mul]
  congr 1
  have hpL : (p : ℂ) ^ L = (p : ℂ) ^ (L - m) * (p : ℂ) ^ m := by rw [← pow_add, Nat.sub_add_cancel hm]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  rw [hpL]
  field_simp

theorem exists_algEquiv_primitiveRoot_pow_of_isAlgClosed {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic ℚ Ω] (ζ : Ω) (n : ℕ) (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (k : ℕ) (hk : k.Coprime n) : ∃ σ : Ω ≃+* Ω, σ ζ = ζ ^ k := by
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  haveI : NeZero (n : Ω) := ⟨by exact_mod_cast hn.ne'⟩
  have hint : IsIntegral ℚ ζ := (hζ.isIntegral hn).tower_top
  have hk' : IsPrimitiveRoot (ζ ^ k) n := hζ.pow_of_coprime k hk
  have hmin : minpoly ℚ ζ = Polynomial.cyclotomic n ℚ := (Polynomial.cyclotomic_eq_minpoly_rat hζ hn).symm
  have hroot : ζ ^ k ∈ (minpoly ℚ ζ).aroots Ω := by
    rw [Polynomial.mem_aroots, hmin]
    refine ⟨Polynomial.cyclotomic_ne_zero n ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff).2 hk'
  let φ := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hint).symm ⟨ζ ^ k, hroot⟩
  let ψ : Ω →ₐ[ℚ] Ω := φ.liftNormal Ω
  refine ⟨(AlgEquiv.ofBijective ψ (Algebra.IsAlgebraic.algHom_bijective ψ)).toRingEquiv, ?_⟩
  have h1 := φ.liftNormal_commutes Ω (IntermediateField.AdjoinSimple.gen ℚ ζ)
  rw [IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen] at h1
  simpa [ψ] using h1

theorem exists_aut {Ω : Type} [Field Ω] [iA : Algebra ℚ Ω] [iC : IsAlgClosure ℚ Ω] (ζ : Ω) (n : ℕ) (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (k : ℕ) (hk : k.Coprime n) : ∃ σ : Ω ≃ₐ[ℚ] Ω, σ ζ = ζ ^ k := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have e : iA = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have i1 : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI i2 : @Algebra.IsAlgebraic ℚ Ω _ _ DivisionRing.toRatAlgebra := by convert i1 using 2; exact e.symm
  obtain ⟨σ, hσ⟩ := exists_algEquiv_primitiveRoot_pow_of_isAlgClosed (Ω := Ω) ζ n hn hζ k hk
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) (fun x => ?_), hσ⟩
  rw [eq_ratCast]
  exact map_ratCast σ x

open Classical in
theorem sum_reindex (p : ℕ) [hpf : Fact p.Prime] (L m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ L) {M : Type} [AddCommMonoid M] (g : ℕ → M) :
    ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), g (a : ZMod (p ^ L)).val
      = ∑ k ∈ Finset.range (p ^ (L - m)), g (1 + p ^ m * k) := by
  have hp : p.Prime := hpf.out
  have hp1 : 1 < p := hp.one_lt
  have hpm : 1 < p ^ m := Nat.one_lt_pow (by omega) hp1
  have hN : p ^ m * p ^ (L - m) = p ^ L := by rw [← pow_add, Nat.add_sub_cancel' hm]
  have cop : ∀ k : ℕ, Nat.Coprime (1 + p ^ m * k) (p ^ L) := by
    intro k
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have h2 : p ∣ p ^ m * k := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) k
    exact hp.not_dvd_one ((Nat.dvd_add_left h2).mp h)
  have hlt : ∀ k < p ^ (L - m), 1 + p ^ m * k < p ^ L := by
    intro k hk
    have : p ^ m * (k + 1) ≤ p ^ m * p ^ (L - m) := Nat.mul_le_mul_left _ hk
    rw [hN] at this
    nlinarith
  have hval : ∀ k < p ^ (L - m), ((ZMod.unitOfCoprime (1 + p ^ m * k) (cop k) : (ZMod (p ^ L))ˣ) : ZMod (p ^ L)).val = 1 + p ^ m * k := by
    intro k hk
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (hlt k hk)]
  symm
  refine Finset.sum_bij (fun k _ => ZMod.unitOfCoprime (1 + p ^ m * k) (cop k)) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range] at hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hval k hk]
    simp [Nat.ModEq, Nat.add_mul_mod_self_left]
  · intro k hk k' hk' h
    rw [Finset.mem_range] at hk hk'
    have := congrArg (fun u : (ZMod (p ^ L))ˣ => (u : ZMod (p ^ L)).val) h
    rw [hval k hk, hval k' hk'] at this
    have h3 : p ^ m * k = p ^ m * k' := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) h3
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hv : (b : ZMod (p ^ L)).val % p ^ m = 1 := by
      have := hb; unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hpm]
    have hvl : (b : ZMod (p ^ L)).val < p ^ L := ZMod.val_lt _
    have hdm := Nat.div_add_mod ((b : ZMod (p ^ L)).val) (p ^ m)
    rw [hv] at hdm
    set k := (b : ZMod (p ^ L)).val / p ^ m
    have hk : k < p ^ (L - m) := by
      by_contra hc
      push_neg at hc
      have : p ^ m * p ^ (L - m) ≤ p ^ m * k := Nat.mul_le_mul_left _ hc
      rw [hN] at this
      omega
    refine ⟨k, Finset.mem_range.mpr hk, ?_⟩
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime]
    have : 1 + p ^ m * k = (b : ZMod (p ^ L)).val := by omega
    rw [this, ZMod.natCast_zmod_val]
  · intro k hk
    rw [hval k (Finset.mem_range.mp hk)]

open Classical in
theorem trace_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (L m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ L)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω))
    (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val) (i : ℕ) :
    ∃ z ∈ Subring.closure {ζ ^ p ^ (L - m)},
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a (ζ ^ i)
        = (p : Ω) ^ (L - m) * z := by
  have hp : p.Prime := hpf.out
  have hN : p ^ L = p ^ m * p ^ (L - m) := by rw [← pow_add, Nat.add_sub_cancel' hm]
  have hs : ∀ a : (ZMod (p ^ L))ˣ, τ a (ζ ^ i) = ζ ^ ((a : ZMod (p ^ L)).val * i) := by
    intro a; rw [map_pow, hτ, ← pow_mul]
  have hr := sum_reindex p L m hm1 hm (fun v => ζ ^ (v * i))
  rw [Finset.sum_congr rfl (fun a _ => hs a), hr]
  have hw : IsPrimitiveRoot (ζ ^ p ^ m) (p ^ (L - m)) := hζ.pow (pow_pos hp.pos _) hN
  have hterm : ∀ k, ζ ^ ((1 + p ^ m * k) * i) = ζ ^ i * ((ζ ^ p ^ m) ^ i) ^ k := by
    intro k; rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  simp only [hterm, ← Finset.mul_sum]
  by_cases hd : p ^ (L - m) ∣ i
  · obtain ⟨j, hj⟩ := hd
    refine ⟨(ζ ^ p ^ (L - m)) ^ j, Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _, ?_⟩
    have h1 : (ζ ^ p ^ m) ^ i = 1 := by rw [hj, pow_mul, hw.pow_eq_one, one_pow]
    have h2 : ζ ^ i = (ζ ^ p ^ (L - m)) ^ j := by rw [hj, pow_mul]
    rw [h1, h2]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow]
    ring
  · refine ⟨0, Subring.zero_mem _, ?_⟩
    have h1 : (ζ ^ p ^ m) ^ i ≠ 1 := fun h => hd ((hw.pow_eq_one_iff_dvd i).mp h)
    rw [geom_sum_eq h1, ← pow_mul, mul_comm i, pow_mul, hw.pow_eq_one, one_pow, sub_self, zero_div, mul_zero, mul_zero]

open Classical in
theorem trace_closure {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (L m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ L)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω))
    (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val) (y : Ω) (hy : y ∈ Subring.closure {ζ}) :
    ∃ z ∈ Subring.closure {ζ ^ p ^ (L - m)},
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a y
        = (p : Ω) ^ (L - m) * z := by
  rw [Subring.mem_closure_iff, Submonoid.closure_singleton_eq] at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact trace_pow p L m hm1 hm ζ hζ τ hτ i
  | zero => exact ⟨0, Subring.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨z1, h1, e1⟩ := hx
    obtain ⟨z2, h2, e2⟩ := hy
    exact ⟨z1 + z2, Subring.add_mem _ h1 h2, by simp only [map_add, Finset.sum_add_distrib, e1, e2]; ring⟩
  | neg x _ hx =>
    obtain ⟨z1, h1, e1⟩ := hx
    exact ⟨-z1, Subring.neg_mem _ h1, by simp only [map_neg, Finset.sum_neg_distrib, e1]; ring⟩

open Classical in

theorem normTrace_exists_unique : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime] (L m : ℕ), 1 ≤ m → m ≤ L → ∀ F : Ω, InZl ε p L F → ∃ F' : Ω, IsNT ε p L m F F' ∧ InZl ε p m F' ∧ ∀ F'' : Ω, IsNT ε p L m F F'' → F'' = F' := by
  intro Ω _ _ _ ε p hpf L m hm1 hm F hF
  have hp : p.Prime := hpf.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hζ := zt_prim ε p L hp.pos
  have hpow := zt_pow ε p L m hp.pos hm
  have hcop : ∀ a : (ZMod (p ^ L))ˣ, ((a : ZMod (p ^ L)).val).Coprime (p ^ L) := fun a => ZMod.val_coe_unit_coprime a
  choose τ hτ using fun a : (ZMod (p ^ L))ˣ => exists_aut (zt ε p L) (p ^ L) (pow_pos hp.pos _) hζ _ (hcop a)
  obtain ⟨D, hD, hDF⟩ := hF
  have hD0 : (D : Ω) ≠ 0 := by
    have : D ≠ 0 := by rintro rfl; exact hD (dvd_zero p)
    exact_mod_cast this
  have hpN : (p : Ω) ^ (L - m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  obtain ⟨z, hz, hT⟩ := trace_closure p L m hm1 hm (zt ε p L) hζ τ hτ _ hDF
  rw [hpow] at hz
  simp only [map_mul, map_natCast, ← Finset.mul_sum] at hT
  have hsum : ∀ σ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω), (∀ a, σ a (zt ε p L) = zt ε p L ^ (a : ZMod (p ^ L)).val) →
      ∀ a, σ a F = τ a F := by
    intro σ hσ a
    have hagree : Set.EqOn ((σ a : Ω ≃+* Ω) : Ω →+* Ω) ((τ a : Ω ≃+* Ω) : Ω →+* Ω) (Subring.closure {zt ε p L}) := by
      apply RingHom.eqOn_set_closure
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      show σ a (zt ε p L) = τ a (zt ε p L)
      rw [hσ, hτ]
    have h2 : σ a ((D : Ω) * F) = τ a ((D : Ω) * F) := hagree hDF
    rw [map_mul, map_mul, map_natCast, map_natCast] at h2
    exact mul_left_cancel₀ hD0 h2
  have hE : (p : Ω) ^ (L - m) * (z / D) = ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a F := by
    rw [← mul_div_assoc, ← hT, mul_div_cancel_left₀ _ hD0]
  refine ⟨z / D, ⟨τ, hτ, hE⟩, ⟨D, hD, ?_⟩, ?_⟩
  · have : (D : Ω) * (z / D) = z := by field_simp
    rw [this]; exact hz
  · rintro F'' ⟨σ, hσ, hF''⟩
    rw [Finset.sum_congr rfl (fun a _ => hsum σ hσ a), ← hE] at hF''
    exact mul_left_cancel₀ hpN hF''

end GlobalTheory.NTr

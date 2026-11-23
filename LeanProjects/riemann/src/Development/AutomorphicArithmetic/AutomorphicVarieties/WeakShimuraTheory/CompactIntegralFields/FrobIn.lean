import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DiagChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FrobInPowCong

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem frobIn_pow_cong {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω} (ha : A.valuation a ≤ 1)
    (hb : A.valuation b ≤ 1) (h : A.valuation (a - b) < 1) (m : ℕ) : A.valuation (a ^ m - b ^ m) < 1 :=
  _root_.UpperTheory.Reformulated.B.Qf16.frobIn_pow_cong A ha hb h m

private theorem frobIn_dec_le {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω}
    {g : G K Ω} (hg : g ∈ Dec (F := K) A) {x : Ω} (hx : A.valuation x ≤ 1) : A.valuation (g x) ≤ 1 :=
  (A.valuation_le_one_iff _).2 ((apply_mem_iff_of_mem_Dec hg x).2 ((A.valuation_le_one_iff _).1 hx))

private theorem frobIn_isFrob_pow {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    {A : ValuationSubring Ω} {q : ℕ} {g : G K Ω} (hg : IsFrob (F := K) A q g) (n : ℕ) :
    IsFrob (F := K) A (q ^ n) (g ^ n) := by
  induction n with
  | zero => exact ⟨by rw [pow_zero]; exact one_mem _, fun x _ => by simp⟩
  | succ n ih =>
    refine ⟨Subgroup.pow_mem _ hg.1 _, fun x hx => ?_⟩
    have h1 := hg.2 _ (frobIn_dec_le ih.1 hx)
    have h2 := frobIn_pow_cong A (frobIn_dec_le ih.1 hx) (b := x ^ q ^ n)
      (by rw [map_pow]; exact pow_le_one' hx _) (ih.2 x hx) q
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [sub_add_sub_cancel, ← pow_mul, ← pow_succ] at h3
    rw [pow_succ' g, AlgEquiv.mul_apply]
    exact h3

theorem UpperTheory.V.Ws.frobIn :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G ℚ Ω)) (M : ℕ),
          IsOpen (U : Set (G ℚ Ω)) → M ≠ 0 → ∃ (p : ℕ) (A : ValuationSubring Ω) (f : ℕ) (σ : G ℚ Ω), p.Prime ∧ ¬ p ∣ M ∧
            A.valuation (p : Ω) < 1 ∧ 0 < f ∧ σ ∈ U ∧ IsFrob A (p ^ f) σ ∧ ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = (p : ℤ_[l]) ^ f := by
  intro Ω _ _ _ l hl U M hU hM
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (M + l + 1)
  have hpM : ¬ p ∣ M := fun h => by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hM) h
    omega
  have hlp : p ≠ l := by omega
  obtain ⟨hex, hfr, -, hco, -, -, -, -, hpl, -⟩ := ML.placeBasic Ω
  obtain ⟨A, hA⟩ := hex p hp
  obtain ⟨φ, hφ⟩ := hfr A p hp hA
  obtain ⟨w, hw, -, -⟩ := hpl A p hp hA
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => by
    refine hco _ p l ((Nat.coprime_primes hp hl.out).2 hlp) hA ?_
    have h1 := (hw ((l : ℕ) : 𝓞 ℚ)).2 h
    have e : algebraMap ℚ Ω (((l : ℕ) : 𝓞 ℚ) : ℚ) = (l : Ω) := by simp
    rw [e] at h1
    exact h1
  have h : ((cycZ ℚ Ω l φ : ℤ_[l]ˣ) : ℤ_[l]) = (p : ℤ_[l]) := by
    refine PadicInt.ext_of_toZModPow.1 fun n => ?_
    rw [cycZ_toZModPow_eq hlw hw (q := p) hφ.2 n]
  haveI : IsGalois ℚ Ω := inferInstance
  haveI : Finite (G ℚ Ω ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  obtain ⟨f, hf, -, hfU⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (H := U) Subgroup.index_ne_zero_of_finite φ
  refine ⟨p, A, f, φ ^ f, hp, hpM, hA, hf, hfU, frobIn_isFrob_pow hφ f, ?_⟩
  rw [map_pow, Units.val_pow_eq_pow_val, h]

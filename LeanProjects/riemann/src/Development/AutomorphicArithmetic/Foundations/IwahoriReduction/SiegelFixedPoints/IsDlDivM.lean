import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowSlashTPow
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem exists_pow_eq {Ω : Type} [Field Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω)
    (hl : ((l : ℕ) : Ω) ∈ A.nonunits) (M : ℕ) (hM : 0 < M) : ∃ k : ℕ, ∃ u ∈ A, (l : Ω) ^ k = (M : Ω) * u := by
  have hp : l.Prime := Fact.out
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' l hp.ne_one
  have hc : IsCoprime (l : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have hc' : IsCoprime (l : A) (m : A) := by simpa using hc.map (Int.castRingHom A)
  have hlu : ¬ IsUnit (l : A) := by
    have h1 : ((l : A) : Ω) ∈ A.nonunits := by simpa using hl
    have := (ValuationSubring.coe_mem_nonunits_iff).1 h1
    exact (IsLocalRing.mem_maximalIdeal _).1 this
  have hmu : IsUnit (m : A) := by
    obtain ⟨a, b, e⟩ := hc'
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (e ▸ isUnit_one) with h | h
    · exact absurd (isUnit_of_mul_isUnit_right h) hlu
    · exact isUnit_of_mul_isUnit_right h
  obtain ⟨u, hu⟩ := hmu.exists_right_inv
  refine ⟨k, (u : Ω), u.2, ?_⟩
  have e : (m : Ω) * (u : Ω) = 1 := by simpa using congrArg (fun x : A => (x : Ω)) hu
  push_cast
  rw [mul_assoc, e, mul_one]

private theorem isDl_divM {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] {ε : Ω →+* ℂ}
    (X : Tower Ω ε) (A : ValuationSubring Ω) (l n k M : ℕ) (hM : 0 < M) (u : Ω) (hu : u ∈ A)
    (hk : (l : Ω) ^ k = (M : Ω) * u) (F : X.K) (ψ : HahnSeries ℚ Ω) (hψ : ∀ r, ψ.coeff r ∈ A)
    (h : IsDl X A l (n + k) (M : ℚ) F (HahnSeries.C (M : Ω) * ψ)) : IsDl X A l n 1 F ψ := by
  obtain ⟨-, a, c, κ, hκ, he, ha, hc, hcg⟩ := h
  refine ⟨hψ, a, c, κ, hκ, he, ha, hc, fun r => ?_⟩
  obtain ⟨z, hz, e⟩ := hcg r
  refine ⟨u * z, mul_mem hu hz, ?_⟩
  have hm : algebraMap ℚ Ω (M : ℚ) = (M : Ω) := map_natCast _ _
  rw [NrmT.theta_eq_C_mul _ (X.exp a), NrmT.theta_eq_C_mul _ (X.exp c), hm] at e
  have hM0 : (M : Ω) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have e2 : HahnSeries.C (M : Ω) * ψ * X.exp a * X.exp c =
      HahnSeries.C (M : Ω) * (ψ * X.exp a * X.exp c) := by ring
  have e3 : HahnSeries.C (M : Ω) * theta 1 (X.exp a) * X.exp c -
      X.exp a * (HahnSeries.C (M : Ω) * theta 1 (X.exp c)) =
      HahnSeries.C (M : Ω) * (theta 1 (X.exp a) * X.exp c - X.exp a * theta 1 (X.exp c)) := by ring
  rw [e2, e3, HahnSeries.C_mul_eq_smul, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.coeff_smul,
    smul_eq_mul, smul_eq_mul, ← mul_sub, pow_add, hk] at e
  apply mul_left_cancel₀ hM0
  rw [e]; ring

private theorem isDl_weak {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
    (X : Tower Ω ε) (A : ValuationSubring Ω) (l n k : ℕ) (s : ℚ) (F : X.K) (φ : HahnSeries ℚ Ω)
    (h : IsDl X A l (n + k) s F φ) : IsDl X A l n s F φ := by
  obtain ⟨hφ, a, c, κ, hκ, he, ha, hc, hcg⟩ := h
  refine ⟨hφ, a, c, κ, hκ, he, ha, hc, fun r => ?_⟩
  obtain ⟨z, hz, e⟩ := hcg r
  exact ⟨(l : Ω) ^ k * z, mul_mem (pow_mem (natCast_mem A l) k) hz, by rw [e, pow_add]; ring⟩

theorem UpperTheory.Kd.L.nrm :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n M : ℕ), 0 < M → ∀ (w : X.K) (φ φ' : HahnSeries ℚ Ω), w ∈ KT X M → IsDl X A l n (M : ℚ) w φ → (∀ r : ℚ, φ.coeff r ≠ 0 → (r * M).den = 1) → (∀ r : ℚ, φ'.coeff r = if r.den = 1 then φ.coeff r else 0) → IsDl X A l n 1 (nrmT X M w) φ' := by
  intro Ω _ _ _ _ ε X l _ A hl n M hM w φ φ' hw hφ _ hφ'
  have hj := X.j_hol.imp fun _ h => And.symm h
  obtain ⟨k, u, huA, hk⟩ := exists_pow_eq l A hl M hM
  have hw0 : w ≠ 0 := by
    rintro rfl
    obtain ⟨-, a, c, κ, hκ, he, ha, -, -⟩ := hφ
    rw [zero_mul] at he
    have ha0 : a = 0 := by
      rcases mul_eq_zero.1 he.symm with h | h
      · exact absurd ((map_eq_zero_iff _ (algebraMap Ω X.K).injective).1 h) hκ
      · exact h
    obtain ⟨-, r, hr, -⟩ := ha
    exact hr (by rw [ha0, map_zero]; rfl)
  obtain ⟨φ2, h2, hs2⟩ := GlobalTheory.T.exists_logDerivQExpansion_modPrimePow_of_translationInvariant ε X hj l A hl (n + k) M w hM hw0 hw
  have hu := GlobalTheory.T.isLogDerivQExpansionModPrimePow_unique ε X hj l A hl n (M : ℚ) w φ φ2 hφ (isDl_weak X A l n k _ w φ2 h2)
  have hT : ∀ b ∈ Finset.range M,
      IsDl X A l (n + k) (M : ℚ) (X.sl (ofSL (ModularGroup.T ^ b)) w) (NrmT.trT ε b φ2) :=
    fun b _ => NrmT.isLogDerivQExpansionModPrimePow_slash_T_pow X A l (n + k) _ w φ2 b h2
  have hP := GlobalTheory.T.isLogDerivQExpansion_finset_prod_zpow ε X hj l A hl (n + k) (M : ℚ) ℕ (Finset.range M)
    (fun b => X.sl (ofSL (ModularGroup.T ^ b)) w) (fun b => NrmT.trT ε b φ2) (fun _ => 1) hT
  simp only [zpow_one, one_smul] at hP
  rw [NrmT.sum_trT M φ2 hs2 (NrmT.resZ φ2) (NrmT.resZ_coeff φ2)] at hP
  have hN := isDl_divM X A l n k M hM u huA hk _ (NrmT.resZ φ2) (fun r => by
    rw [NrmT.resZ_coeff]; split_ifs
    · exact h2.1 r
    · exact zero_mem A) hP
  refine NrmT.isDl_congr X A l n 1 _ (NrmT.resZ φ2) φ' hN (fun r => ?_) (fun r => ?_)
  · rw [hφ']; split_ifs
    · exact hφ.1 r
    · exact zero_mem A
  · rw [hφ', NrmT.resZ_coeff]; split_ifs
    · exact hu r
    · exact ⟨0, zero_mem A, by ring⟩

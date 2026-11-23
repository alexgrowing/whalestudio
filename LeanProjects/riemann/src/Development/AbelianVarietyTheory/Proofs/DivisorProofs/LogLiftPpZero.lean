import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

section LogMul

variable {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p] (π : Kt →+* K)
  {ι : Type} (F : ι → Kt →+* Kt) (s : Finset ι) (A : Subring K)

omit [Fact p.Prime] in
lemma logLift_pp_zero (hπ : IsFlatLift p π) : (p : Kt) * p = 0 := by
  rw [hπ.ann]; simp [map_natCast, CharP.cast_eq_zero]

omit [Fact p.Prime] in
lemma logLift_one : LogLift p π F s (A : Set K) 1 :=
  ⟨1, map_one π, fun i _ => ⟨0, by simp [A.zero_mem], by simp⟩⟩

omit [Fact p.Prime] in
lemma logLift_mul (hπ : IsFlatLift p π) {g g' : K} (hg : LogLift p π F s (A : Set K) g)
    (hg' : LogLift p π F s (A : Set K) g') : LogLift p π F s (A : Set K) (g * g') := by
  obtain ⟨z, hz, hF⟩ := hg
  obtain ⟨z', hz', hF'⟩ := hg'
  have hpp := logLift_pp_zero p π hπ
  refine ⟨z * z', by simp [hz, hz'], fun i hi => ?_⟩
  obtain ⟨w, hw, hFw⟩ := hF i hi
  obtain ⟨w', hw', hFw'⟩ := hF' i hi
  refine ⟨w + w', by rw [map_add]; exact A.add_mem hw hw', ?_⟩
  rw [map_mul, hFw, hFw', mul_pow]
  linear_combination (z ^ p * z' ^ p * w * w') * hpp

omit [Fact p.Prime] in
lemma logLift_inv (hπ : IsFlatLift p π) {g : K} (hg0 : g ≠ 0) (hg : LogLift p π F s (A : Set K) g) :
    LogLift p π F s (A : Set K) g⁻¹ := by
  obtain ⟨z, hz, hF⟩ := hg
  have hpp := logLift_pp_zero p π hπ
  have hπp : π (p : Kt) = 0 := by simp [map_natCast, CharP.cast_eq_zero]
  obtain ⟨z', hz'⟩ := hπ.surj g⁻¹
  obtain ⟨e, he⟩ := (hπ.ker (z * z' - 1)).1 (by simp [hz, hz', hg0])
  set u := z' * (1 - p * e) with hu
  have hzu : z * u = 1 := by
    have : z * z' = 1 + p * e := by linear_combination he
    rw [hu, ← mul_assoc, this]; linear_combination (-(e * e)) * hpp
  have hπu : π u = g⁻¹ := by simp [hu, hz', hπp]
  clear_value u
  refine ⟨u, hπu, fun i hi => ?_⟩
  obtain ⟨w, hw, hFw⟩ := hF i hi
  refine ⟨-w, by rw [map_neg]; exact A.neg_mem hw, ?_⟩
  have h1 : F i z * F i u = 1 := by rw [← map_mul, hzu, map_one]
  have h2 : F i z * (u ^ p * (1 + p * -w)) = 1 := by
    rw [hFw]
    have : z ^ p * u ^ p = 1 := by rw [← mul_pow, hzu, one_pow]
    linear_combination (1 - (p:Kt) * w * ((p:Kt) * w)) * this - (w * w) * hpp
  linear_combination (u ^ p * (1 + p * -w)) * h1 - (F i u) * h2

omit [Fact p.Prime] in
lemma logLift_zpow (hπ : IsFlatLift p π) {g : K} (hg0 : g ≠ 0) (hg : LogLift p π F s (A : Set K) g) :
    ∀ n : ℤ, LogLift p π F s (A : Set K) (g ^ n) := by
  have hpow : ∀ {h : K}, LogLift p π F s (A : Set K) h → ∀ k : ℕ, LogLift p π F s (A : Set K) (h ^ k) := by
    intro h hh k
    induction k with
    | zero => simpa using logLift_one p π F s A
    | succ k ih => rw [pow_succ]; exact logLift_mul p π F s A hπ ih hh
  intro n
  cases n with
  | ofNat k => rw [Int.ofNat_eq_coe, zpow_natCast]; exact hpow hg k
  | negSucc k =>
    rw [zpow_negSucc, ← inv_pow]
    exact hpow (logLift_inv p π F s A hπ hg0 hg) (k + 1)

end LogMul

end GlobalTheory.DI

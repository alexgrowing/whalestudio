import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.LaHatMod

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct

theorem valued_algebraMap (w : HeightOneSpectrum ℤ) (q : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) q) = w.valuation ℚ q :=
  valuedAdicCompletion_eq_valuation' w q

theorem exists_int_valued_sub_le (w : HeightOneSpectrum ℤ) {x : w.adicCompletion ℚ} (hx : Valued.v x ≤ 1)
    {c : ℚ} (hc0 : c ≠ 0) (hc : w.valuation ℚ c ≤ 1) :
    ∃ r : ℤ, Valued.v (x - (r : w.adicCompletion ℚ)) ≤ w.valuation ℚ c := by
  set c' : w.adicCompletion ℚ := algebraMap ℚ (w.adicCompletion ℚ) c
  have hc' : c' ≠ 0 := by
    simp only [c', ne_eq, map_eq_zero_iff _ (algebraMap ℚ (w.adicCompletion ℚ)).injective]; exact hc0
  have hpos : (0 : WithZero (Multiplicative ℤ)) < Valued.v c' := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hc')
  have hU : IsOpen ((fun y => (y - x) / c') ⁻¹' (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))) :=
    (Valued.isOpen_valuationSubring _).preimage ((continuous_id.sub continuous_const).div_const c')
  obtain ⟨k, hk⟩ := (denseRange_algebraMap (K := ℚ) w).exists_mem_open hU
    ⟨x, by simp [SetLike.mem_coe, sub_self, zero_div]⟩
  have hk' : Valued.v (x - algebraMap ℚ (w.adicCompletion ℚ) k) ≤ w.valuation ℚ c := by
    have h : Valued.v ((algebraMap ℚ (w.adicCompletion ℚ) k - x) / c') ≤ 1 := hk
    rw [map_div₀, div_le_one₀ hpos] at h
    rw [Valuation.map_sub_swap, ← valued_algebraMap]; exact h
  have hk1 : w.valuation ℚ k ≤ 1 := by
    rw [← valued_algebraMap]
    have e : algebraMap ℚ (w.adicCompletion ℚ) k = x - (x - algebraMap ℚ (w.adicCompletion ℚ) k) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le hx (hk'.trans hc))
  have hne : w.valuation ℚ c ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  obtain ⟨r, hr⟩ := exists_valuation_sub_lt_of_integer w hk1 (Units.mk0 _ hne)
  refine ⟨r, ?_⟩
  have hr' : Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (k - algebraMap ℤ ℚ r)) ≤ w.valuation ℚ c := by
    rw [valued_algebraMap, Valuation.map_sub_swap]; exact hr.le
  have e : x - (r : w.adicCompletion ℚ) =
      (x - algebraMap ℚ (w.adicCompletion ℚ) k) + algebraMap ℚ (w.adicCompletion ℚ) (k - algebraMap ℤ ℚ r) := by
    rw [map_sub, algebraMap_int_eq, eq_intCast, map_intCast]; ring
  rw [e]
  exact (Valuation.map_add _ _ _).trans (max_le hk' hr')

variable {p : ℕ} [Fact p.Prime]

theorem valued_intCast (w : HeightOneSpectrum ℤ) (z : ℤ) :
    Valued.v ((z : w.adicCompletion ℚ)) ≤ 1 := by
  rw [← map_intCast (algebraMap ℚ (w.adicCompletion ℚ)), valued_algebraMap]
  have := w.valuation_le_one (K := ℚ) z
  simpa using this

theorem exists_int_add_prime_mul (l : ℕ) (hl : l.Prime) (hlp : l ≠ p) (a : AfP p) (ha : IsIntAf a) :
    ∃ (z : ℤ) (a' : AfP p), IsIntAf a' ∧ a = (z : AfP p) + (l : AfP p) * a' := by
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hl).irreducible
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  let w0 : HeightOneSpectrum ℤ := ⟨Ideal.span {(l : ℤ)}, hmax.isPrime, by simpa using hl0⟩
  have hw0 : w0.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro h
    have hp : (p : ℤ) ∈ Ideal.span {(l : ℤ)} := by
      change (p : ℤ) ∈ w0.asIdeal; rw [h]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_singleton] at hp
    have hd : l ∣ p := by exact_mod_cast hp
    rcases (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : p.Prime) l hd) with h1 | h1
    · exact hl.ne_one h1
    · exact hlp h1
  let v0 : AwayP p := ⟨w0, hw0⟩
  have hlq0 : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hlv : ∀ w : HeightOneSpectrum ℤ, w.valuation ℚ (l : ℚ) ≤ 1 := fun w => by
    have := w.valuation_le_one (K := ℚ) (l : ℤ); simpa using this
  obtain ⟨z, hz⟩ := exists_int_valued_sub_le w0 (ha v0) hlq0 (hlv w0)
  refine ⟨z, (a - (z : AfP p)) * algebraMap ℚ (AfP p) (l : ℚ)⁻¹, ?_, ?_⟩
  · intro v
    rw [mem_adicCompletionIntegers, map_mul, map_sub, map_intCast, AlgHom.commutes, Valuation.map_mul,
      valued_algebraMap, map_inv₀]
    have hne : v.1.valuation ℚ (l : ℚ) ≠ 0 := (Valuation.ne_zero_iff _).2 hlq0
    by_cases hv : v = v0
    · subst hv
      rw [mul_inv_le_iff₀ (zero_lt_iff.2 hne), _root_.one_mul]
      exact hz
    · have hnot : (l : ℤ) ∉ v.1.asIdeal := by
        intro hm
        apply hv
        have hle : Ideal.span {(l : ℤ)} ≤ v.1.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hm
        have heq := hmax.eq_of_le v.1.isPrime.ne_top hle
        exact Subtype.ext (HeightOneSpectrum.ext heq.symm)
      have h1 : v.1.valuation ℚ (l : ℚ) = 1 := by
        have := (valuation_eq_one_iff_notMem (v := v.1) (K := ℚ) (r := (l : ℤ))).2 hnot
        simpa using this
      rw [h1, inv_one, _root_.mul_one]
      exact (Valuation.map_sub _ _ _).trans (max_le (ha v) (valued_intCast v.1 z))
  · have e : (l : AfP p) * algebraMap ℚ (AfP p) (l : ℚ)⁻¹ = 1 := by
      rw [← map_natCast (algebraMap ℚ (AfP p)), ← map_mul, mul_inv_cancel₀ hlq0, map_one]
    calc a = (z : AfP p) + (a - (z : AfP p)) * ((l : AfP p) * algebraMap ℚ (AfP p) (l : ℚ)⁻¹) := by
          rw [e, _root_.mul_one]; ring
      _ = _ := by ring

theorem exists_int_add_mul (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) (a : AfP p) (ha : IsIntAf a) :
    ∃ (z : ℤ) (a' : AfP p), IsIntAf a' ∧ a = (z : AfP p) + (n : AfP p) * a' := by
  induction n using Nat.recOnMul generalizing a with
  | zero => exact absurd hn (lt_irrefl 0)
  | one => exact ⟨0, a, ha, by simp⟩
  | prime l hl =>
    exact exists_int_add_prime_mul l hl (fun h => by
      subst h; exact hl.ne_one ((Nat.coprime_self _).1 hnp)) a ha
  | mul m k ihm ihk =>
    have hm : 0 < m := Nat.pos_of_ne_zero (fun h => by simp [h] at hn)
    have hk : 0 < k := Nat.pos_of_ne_zero (fun h => by simp [h] at hn)
    obtain ⟨hmp, hkp⟩ := Nat.coprime_mul_iff_left.1 hnp
    obtain ⟨z1, a1, h1, e1⟩ := ihm hm hmp a ha
    obtain ⟨z2, a2, h2, e2⟩ := ihk hk hkp a1 h1
    exact ⟨z1 + m * z2, a2, h2, by rw [e1, e2]; push_cast; ring⟩

end GlobalTheory.LKGeo.LaHatMod

namespace GlobalTheory.LKGeo

theorem exists_inAf_add_nsmul_of_mem_laHat : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (n : ℕ), 0 < n → n.Coprime p →
    ∀ v ∈ LaHat D, ∃ (x : D.La) (w : TensorProduct ℚ (AfP p) (VQ D)), w ∈ LaHat D ∧ v = inAf D x + n • w := by
  intro p _ D n hn hnp v hv
  induction hv using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨a, x, ha, rfl⟩ := hu
    obtain ⟨z, a', ha', e⟩ := LaHatMod.exists_int_add_mul n hn hnp a ha
    refine ⟨z • x, a' ⊗ₜ ((1 : ℚ) ⊗ₜ x), AddSubgroup.subset_closure ⟨a', x, ha', rfl⟩, ?_⟩
    have h1 : ((z : AfP p)) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) = (1 : AfP p) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] (z • x)) := by
      rw [show (z : AfP p) = (z : ℚ) • (1 : AfP p) by rw [← Algebra.algebraMap_eq_smul_one, map_intCast],
        TensorProduct.smul_tmul, TensorProduct.smul_tmul',
        show (z : ℚ) • (1 : ℚ) = z • (1 : ℚ) by simp, TensorProduct.smul_tmul]
    have h2 : ((n : AfP p) * a') ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) = n • (a' ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x)) := by
      rw [← nsmul_eq_mul, TensorProduct.smul_tmul']
    rw [e, TensorProduct.add_tmul, h1, h2, inAf]
  | zero => exact ⟨0, 0, zero_mem _, by simp [inAf]⟩
  | add u u' _ _ ih ih' =>
    obtain ⟨x, w, hw, e⟩ := ih
    obtain ⟨x', w', hw', e'⟩ := ih'
    refine ⟨x + x', w + w', add_mem hw hw', ?_⟩
    rw [e, e', inAf, inAf, inAf, TensorProduct.tmul_add, TensorProduct.tmul_add, smul_add]
    abel
  | neg u _ ih =>
    obtain ⟨x, w, hw, e⟩ := ih
    refine ⟨-x, -w, neg_mem hw, ?_⟩
    rw [e, inAf, inAf, TensorProduct.tmul_neg, TensorProduct.tmul_neg, smul_neg, neg_add]

end GlobalTheory.LKGeo

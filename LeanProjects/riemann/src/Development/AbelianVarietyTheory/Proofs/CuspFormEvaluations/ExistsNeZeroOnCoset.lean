import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TBNFinal
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNeZeroPair

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.TorsionCoset

variable {E : Type} [Field E] [NumberField E]

theorem eps_zero (X : PT E) : X.eps 0 = 1 := by
  have h := X.eps_add 0 (zero_mem _) 0 (zero_mem _)
  simp only [add_zero] at h
  rcases X.eps_pm 0 (zero_mem _) with h1 | h1
  · exact h1
  · rw [h1] at h
    norm_num [Hf] at h

theorem natCast_smul_mem (X : PT E) {x : Vsp X.dim} (hx : x ∈ X.L) (k : ℕ) :
    (k : ℂ) • x ∈ X.L := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hx k

theorem eps_natCast_smul (X : PT E) {x : Vsp X.dim} (hx : x ∈ X.L) (k : ℕ) :
    (X.eps ((k : ℂ) • x) : ℝ) = (X.eps x : ℝ) ^ k := by
  induction k with
  | zero => simp [eps_zero]
  | succ k ih =>
    have h := X.eps_add _ (natCast_smul_mem X hx k) x hx
    have him : (Hf ((k : ℂ) • x) x).im = 0 := by
      unfold Hf
      rw [Complex.im_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [PiLp.smul_apply, mul_assoc, Complex.mul_conj]
    rw [show ((k + 1 : ℕ) : ℂ) • x = (k : ℂ) • x + x by push_cast; rw [add_smul, one_smul],
      h, ih, him]
    simp [pow_succ]

theorem isPi_natCast (X : PT E) (n : ℕ) : IsPi X (n ^ 2) ((n : ℂ) • LinearMap.id) := by
  refine ⟨fun α v => ?_, fun x hx => ?_, fun v w => ?_, fun x hx => ?_⟩
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    ext i
    simp [act]
    ring
  · exact natCast_smul_mem X hx n
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    unfold Hf
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
    ring
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    have h := eps_natCast_smul X hx n
    have h2 : (X.eps x : ℝ) ^ n = (X.eps x : ℝ) ^ (n ^ 2) := by
      rcases X.eps_pm x hx with h1 | h1
      · simp [h1]
      · rw [h1]
        push_cast
        rw [sq, pow_mul]
        rcases neg_one_pow_eq_or ℝ n with h3 | h3 <;> simp [h3]
    exact_mod_cast h.trans h2

theorem exists_isReps (X : PT E) (n : ℕ) (hn : n ≠ 0) :
    ∃ K, IsReps X (n ^ 2) 1 ((n : ℂ) • LinearMap.id) K := by
  classical
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hsq : ∀ x : Vsp X.dim, ((n ^ 2 : ℕ) : ℂ) • x = (n : ℂ) • (n : ℂ) • x := fun x => by
    rw [smul_smul]; push_cast; rw [sq]
  let S : Set (Fin 1 → Vsp X.dim) :=
    {b | (n : ℂ) • (n : ℂ) • b 0 ∈ X.L ∧ (n : ℂ) • b 0 ∈ ZSpan.fundamentalDomain X.b}
  have hS : S.Finite := by
    have hb := ZSpan.setFinite_inter X.b
      ((ZSpan.fundamentalDomain_isBounded X.b).smul₀ (n : ℂ))
    refine Set.Finite.of_injOn (f := fun b => (n : ℂ) • (n : ℂ) • b 0) ?_ ?_ hb
    · intro b hb
      exact ⟨Set.smul_mem_smul_set hb.2, hb.1⟩
    · intro b _ c _ h
      funext k
      rw [Subsingleton.elim k 0]
      exact smul_right_injective _ hn' (smul_right_injective _ hn' h)
  refine ⟨hS.toFinset, fun b hb k => ?_, fun b hb => ?_⟩
  · rw [Subsingleton.elim k 0, hsq]
    exact (hS.mem_toFinset.1 hb).1
  · have hb0 := hb 0
    rw [hsq] at hb0
    have hfl : (n : ℂ) • b 0 - ZSpan.fract X.b ((n : ℂ) • b 0) ∈ X.L := by
      rw [ZSpan.fract_apply, sub_sub_cancel]
      exact (ZSpan.floor X.b _).2
    refine ⟨fun _ => (n : ℂ)⁻¹ • ZSpan.fract X.b ((n : ℂ) • b 0), ⟨hS.mem_toFinset.2 ⟨?_, ?_⟩,
      fun k => ?_⟩, ?_⟩
    · simp only [smul_inv_smul₀ hn']
      have := sub_mem hb0 (natCast_smul_mem X hfl n)
      rwa [smul_sub, sub_sub_cancel] at this
    · simp only [smul_inv_smul₀ hn']
      exact ZSpan.fract_mem_fundamentalDomain X.b _
    · rw [Subsingleton.elim k 0]
      simpa only [LinearMap.smul_apply, LinearMap.id_apply, smul_sub, smul_inv_smul₀ hn'] using hfl
    · rintro c ⟨hc, hc'⟩
      have h1 := (hS.mem_toFinset.1 hc).2
      have h2 := hc' 0
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_sub] at h2
      funext k
      rw [Subsingleton.elim k 0, eq_inv_smul_iff₀ hn', ← (ZSpan.fract_eq_self.2 h1),
        ZSpan.fract_eq_fract, neg_add_eq_sub]
      exact h2

theorem exists_ne_zero_on_coset (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E)
    (s : (Fin 1 → Vsp X.dim) → ℂ) (hs : s ∈ X.Sec 1 1) (h0 : s ≠ 0) (n : ℕ) (hn : 2 ≤ n)
    (a : Vsp X.dim) : ∃ y ∈ X.L, s (fun _ => a + ((n : ℂ)⁻¹) • y) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hn0 : n ≠ 0 := by omega
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn0
  have hq : 2 ≤ n ^ 2 := by nlinarith
  obtain ⟨K, hK⟩ := exists_isReps X n hn0
  obtain ⟨-, -, -, hspan⟩ :=
    thetaBasis_holds E X (n ^ 2) 1 _ (by omega) (isPi_natCast X n) s hs h0 K hK
  obtain ⟨F, hF, hFv⟩ := GlobalTheory.BasePointFree.exists_sec_ne_zero E X s hs h0 (n ^ 2) hq
    (fun _ => (n : ℂ)⁻¹ • a)
  apply hFv
  have hle : Submodule.span ℂ ((fun b => X.U (n ^ 2) b (s0 X ((n : ℂ) • LinearMap.id) s)) ''
      (K : Set _)) ≤ LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ => ℂ)
        (fun _ : Fin 1 => (n : ℂ)⁻¹ • a)) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have h := hcon _ (neg_mem (hK.1 b hb 0))
    have e : a + (n : ℂ)⁻¹ • -(((n ^ 2 : ℕ) : ℂ) • b 0) = (n : ℂ) • ((n : ℂ)⁻¹ • a - b 0) := by
      rw [smul_sub, smul_inv_smul₀ hn', smul_neg, smul_smul, sub_eq_add_neg]
      congr 3
      push_cast
      field_simp
    rw [e] at h
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply, PT.U, s0,
      Fin.prod_univ_one, LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply, h, mul_zero]
  exact hle (hspan hF)

end GlobalTheory.TorsionCoset

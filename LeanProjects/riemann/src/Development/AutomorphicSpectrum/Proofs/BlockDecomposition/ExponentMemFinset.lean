import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsLintegralConstantTermL2SqLe
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.Latexp

open GroundTheory.Automorphic.Reduction in
theorem detModule_tor_one (K : Type) [Field K] [NumberField K] (n : ℕ) :
    (detModule K n (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) : ℝ)
      = Real.exp ((n : ℝ) * (Module.finrank ℚ K : ℝ)) := by
  unfold PositivityTheory.Rg.Rs.An.tor
  rw [CuspidalSpectrum.detModule_diagUnits_posIdele]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, ← Real.exp_nat_mul]
  simp

open GroundTheory.Automorphic.Reduction in
theorem detModule_lhs (K : Type) [Field K] [NumberField K] (n : ℕ) (γ₀ : GL (Fin n) K) (m : ℤ) :
    (detModule K n (AdelicGLn.diagonal K n γ₀ * (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) ^ m) : ℝ)
      = Real.exp ((m : ℝ) * ((n : ℝ) * (Module.finrank ℚ K : ℝ))) := by
  have h1 : detModule K n (AdelicGLn.diagonal K n γ₀) = 1 :=
    mem_normOneGL_iff_detModule.1 (rationalGL_le_normOneGL ⟨γ₀, rfl⟩)
  rw [map_mul, h1, one_mul, map_zpow]
  have hv : ∀ (s : {r : ℝ // 0 < r}) (k : ℤ), ((s ^ k : {r : ℝ // 0 < r}) : ℝ) = (s : ℝ) ^ k := by
    intro s k
    have hinv : ∀ u : {r : ℝ // 0 < r}, ((u⁻¹ : {r : ℝ // 0 < r}) : ℝ) = (u : ℝ)⁻¹ := by
      intro u
      have h := congrArg Subtype.val (mul_inv_cancel u)
      rw [Positive.val_mul, Positive.val_one] at h
      exact eq_inv_of_mul_eq_one_right h
    have hpow : ∀ (u : {r : ℝ // 0 < r}) (j : ℕ), ((u ^ j : {r : ℝ // 0 < r}) : ℝ) = (u : ℝ) ^ j := by
      intro u j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, pow_succ, Positive.val_mul, ih]
    cases k with
    | ofNat j => simp only [Int.ofNat_eq_natCast, zpow_natCast, hpow]
    | negSucc j => rw [zpow_negSucc, zpow_negSucc, hinv, hpow]
  rw [hv, detModule_tor_one, ← Real.rpow_intCast, ← Real.exp_mul, mul_comm]

open GroundTheory.Automorphic.Reduction in
theorem detModule_rhs (K : Type) [Field K] [NumberField K] (n r : ℕ) (X Y : UPos n r → 𝔸[K])
    (a q : AdelicGLn.AdelicGL K n) :
    detModule K n (unipGL X * a * q * a⁻¹ * (unipGL Y)⁻¹) = detModule K n q := by
  have h1 : detModule K n (unipGL X) = 1 :=
    mem_normOneGL_iff_detModule.1 (CuspidalSpectrum.unipGL_mem_normOneGL X)
  have h2 : detModule K n (unipGL Y) = 1 :=
    mem_normOneGL_iff_detModule.1 (CuspidalSpectrum.unipGL_mem_normOneGL Y)
  simp only [map_mul, map_inv, h1, h2, inv_one, one_mul, mul_one]
  rw [mul_comm (detModule K n a), mul_assoc, mul_inv_cancel, mul_one]

end GlobalTheory.CompanionTheory.Latexp

namespace GlobalTheory.CompanionTheory.Latexp
open GroundTheory.Automorphic.Reduction in

theorem exponent_mem_finset : ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ), 0 < n → ∀ (Q : Set (AdelicGLn.AdelicGL K n)), IsCompact Q → ∃ M : Finset ℤ, ∀ (t : ℝ) (X Y : UPos n r → 𝔸[K]), ∀ q ∈ Q, ∀ (γ₀ : GL (Fin n) K) (m : ℤ), AdelicGLn.diagonal K n γ₀ * (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) ^ m = unipGL X * PositivityTheory.Rg.Rs.An.aR K n r t * q * (PositivityTheory.Rg.Rs.An.aR K n r t)⁻¹ * (unipGL Y)⁻¹ → m ∈ M := by
  intro K _ _ n r hn Q hQ
  have hdc : Continuous fun g : AdelicGLn.AdelicGL K n => (detModule K n g : ℝ) :=
    continuous_subtype_val.comp continuous_detModule
  obtain ⟨a, b, ha, -, hab⟩ := Reduction.exists_pos_bounds hQ hdc (fun g _ => (detModule K n g).2)
  have hN : 0 < (n : ℝ) * (Module.finrank ℚ K : ℝ) :=
    mul_pos (Nat.cast_pos.2 hn) (Nat.cast_pos.2 Module.finrank_pos)
  set N : ℝ := (n : ℝ) * (Module.finrank ℚ K : ℝ) with hNdef
  refine ⟨Finset.Icc ⌊Real.log a / N⌋ ⌈Real.log b / N⌉, ?_⟩
  intro t X Y q hq γ₀ m h
  have h1 := congrArg (fun g => (detModule K n g : ℝ)) h
  beta_reduce at h1
  rw [detModule_lhs, detModule_rhs] at h1
  obtain ⟨h2, h3⟩ := hab q hq
  rw [← h1] at h2 h3
  have h4 : Real.log a ≤ (m : ℝ) * N := (Real.log_le_iff_le_exp ha).2 h2
  have h5 : (m : ℝ) * N ≤ Real.log b := by
    have hb : 0 < b := lt_of_lt_of_le (Real.exp_pos _) h3
    exact (Real.le_log_iff_exp_le hb).2 h3
  rw [Finset.mem_Icc]
  constructor
  · have : Real.log a / N ≤ (m : ℝ) := (div_le_iff₀ hN).2 h4
    exact Int.cast_le.1 ((Int.floor_le _).trans this)
  · have : (m : ℝ) ≤ Real.log b / N := (le_div_iff₀ hN).2 h5
    exact Int.cast_le.1 (this.trans (Int.le_ceil _))
end GlobalTheory.CompanionTheory.Latexp

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvSubstNatMultiplePrimePowConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallInvariantDifferentialDvdStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieZero

theorem eq_zero_of_pow_dvd {O : Type} [CommRing O] {p : O} [IsHausdorff (Ideal.span {p}) O] (x : O)
    (h : ∀ n : ℕ, p ^ n ∣ x) : x = 0 := by
  refine IsHausdorff.haus (I := Ideal.span {p}) ‹_› x fun n => ?_
  rw [SModEq.sub_mem, sub_zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  exact Ideal.mem_span_singleton.2 (h n)

variable {R : Type} [CommRing R] {d : ℕ}

theorem nmul_succ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (n : ℕ) :
    nmul μ (n + 1) = op μ (nmul μ n) (fun k => X k) := by
  unfold nmul
  rw [Function.iterate_succ_apply']

theorem constantCoeff_nmul (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (i : Fin d) : constantCoeff (nmul μ n i) = 0 := by
  induction n generalizing i with
  | zero => simp [nmul]
  | succ n ih =>
    have hb : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun k => (X k : MvPowerSeries (Fin d) R)) j)
        = 0 := by
      rintro (j | j)
      · exact ih j
      · simp
    rw [nmul_succ]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hb) hb (hμ i)

theorem subst_eq_add_of_cob1_eq_zero {E : Type} [CommRing E] (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) E)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) E) (hf : cob1 μ f = 0)
    {τ : Type} (b : Fin d ⊕ Fin d → MvPowerSeries τ E) (hb : HasSubst b) :
    subst (fun i => subst b (μ i)) f = subst (fun i => b (Sum.inl i)) f + subst (fun i => b (Sum.inr i)) f := by
  have hμs : HasSubst μ := hasSubst_of_constantCoeff_zero hμ
  have hL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) E)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) E)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have h := congrArg (subst b) hf
  unfold cob1 inL inR at h
  rw [subst_sub hb, subst_sub hb, subst_comp_subst_apply hμs hb,
    subst_comp_subst_apply hL hb, subst_comp_subst_apply hR hb, ← coe_substAlgHom hb, map_zero,
    coe_substAlgHom hb] at h
  simp only [subst_X hb] at h
  rw [← sub_eq_zero, ← h, sub_sub]

theorem subst_nmul_of_cob1_eq_zero {O E : Type} [CommRing O] [CommRing E] [Algebra O E]
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) E) (hf : cob1 (up E μ) f = 0) (m : ℕ) :
    subst (up E (nmul μ m)) f = (m : E) • f := by
  have hμ' : ∀ i, constantCoeff (up E μ i) = 0 := fun i => by
    simp [up, constantCoeff_map, hμ i]
  induction m with
  | zero =>
    have h0 : up E (nmul μ 0) = (0 : Fin d → MvPowerSeries (Fin d) E) := by
      funext i; simp [up, nmul]
    rw [h0, Nat.cast_zero, zero_smul]
    have h := subst_eq_add_of_cob1_eq_zero (up E μ) hμ' f hf (0 : Fin d ⊕ Fin d → MvPowerSeries (Fin d) E)
      HasSubst.zero
    have h1 : (fun i => subst (0 : Fin d ⊕ Fin d → MvPowerSeries (Fin d) E) (up E μ i)) = 0 := by
      funext i; exact subst_zero_of_constantCoeff_zero (hμ' i)
    rw [h1] at h
    have h2 : (fun i : Fin d => (0 : Fin d ⊕ Fin d → MvPowerSeries (Fin d) E) (Sum.inl i)) = 0 := rfl
    have h3 : (fun i : Fin d => (0 : Fin d ⊕ Fin d → MvPowerSeries (Fin d) E) (Sum.inr i)) = 0 := rfl
    rw [h2, h3] at h
    linear_combination -h
  | succ m ih =>
    have hc : ∀ j, constantCoeff (Sum.elim (nmul μ m) (fun k => (X k : MvPowerSeries (Fin d) O)) j)
        = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul μ hμ m j
      · simp
    have hc' : ∀ j, constantCoeff (Sum.elim (up E (nmul μ m))
        (fun k => (X k : MvPowerSeries (Fin d) E)) j) = 0 := by
      rintro (j | j)
      · simp [up, constantCoeff_map, constantCoeff_nmul μ hμ m j]
      · simp
    have hs : up E (nmul μ (m + 1)) = fun i => subst (Sum.elim (up E (nmul μ m))
        (fun k => (X k : MvPowerSeries (Fin d) E))) (up E μ i) := by
      funext i
      simp only [up, nmul_succ, op, at2]
      rw [map_subst (hasSubst_of_constantCoeff_zero hc)]
      congr 1
      funext j
      rcases j with j | j <;> simp [up]
    rw [hs, subst_eq_add_of_cob1_eq_zero (up E μ) hμ' f hf _ (hasSubst_of_constantCoeff_zero hc')]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [ih, show (subst (fun k => (X k : MvPowerSeries (Fin d) E)) f) = f from
      congrFun (subst_self (R := E) (σ := Fin d)) f]
    push_cast
    rw [add_smul, one_smul]

theorem lie_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E],
    IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d),
    ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), c.IsLie f l →
    (In (⊤ : Ideal O) f → constantCoeff f = 0 → l = 0) ∧ (cob1 (up E c.μ) f = 0 → l = 0) := by
  intro p _ O E _ _ _ hF G d c f l hl
  haveI : IsAdicComplete (Ideal.span {(p : O)}) O := hF.complete
  unfold Chart.IsLie at hl
  have key : (∀ n, ∃ s : MvPowerSeries (Fin d) O, MvPowerSeries.map (algebraMap O E) s =
      defect c.μ (p ^ n) f ∧ ∃ z, c.ev n s = (p : O) ^ n • z) → l = 0 := by
    intro H
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.zero_apply]
    refine eq_zero_of_pow_dvd (p := (p : O)) _ fun n => ?_
    obtain ⟨s, hs, z, hz⟩ := H n
    obtain ⟨φ, hφ⟩ := (T.dvd_of_forall_invariantDifferential_dvd p O G n 1 0 (fun _ _ _ => one_dvd _)).2 w
    have h1 := hl.2 n w φ s hφ hs
    have h2 : (p : O) ^ n ∣ φ (c.ev n s) := by
      rw [hz]
      simp
    simpa using dvd_add h1 h2
  refine ⟨fun hIn hc0 => key fun n => ?_, fun hcob => key fun n => ?_⟩
  · choose g hg using hIn
    let s0 : MvPowerSeries (Fin d) O := fun α => g α
    have hs0 : MvPowerSeries.map (algebraMap O E) s0 = f := by
      ext α
      rw [coeff_map, (hg α).2]
      rfl
    have hc : constantCoeff s0 = 0 := by
      apply hF.inj
      rw [map_zero, ← constantCoeff_map, hs0, hc0]
    have hsub : HasSubst (nmul c.μ (p ^ n)) :=
      hasSubst_of_constantCoeff_zero (constantCoeff_nmul c.μ c.isLaw.const _)
    refine ⟨(p ^ n) • s0 - subst (nmul c.μ (p ^ n)) s0, ?_, c.ev n s0, ?_⟩
    · rw [map_sub, map_nsmul, map_subst hsub, hs0]
      unfold defect
      rw [Nat.cast_smul_eq_nsmul]
      rfl
    · rw [map_sub, map_nsmul, (T.ev_subst_natMultiple_prime_pow_constant p O G d c n).1 s0, hc, map_zero, sub_zero,
        ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
  · refine ⟨0, ?_, 0, ?_⟩
    · unfold defect
      rw [subst_nmul_of_cob1_eq_zero c.μ c.isLaw.const f hcob, sub_self, map_zero]
    · simp

end GlobalTheory.LieZero

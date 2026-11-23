import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationFormalGroupLawIsLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationMonomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInvariantDerivationFormalGroupLawIterateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationCongrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffQuasiLogarithmIntegralLowDegreeStatement

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory.FrobIter

def iterLin {R : Type} [CommRing R] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (u : Fin d → R) (n : ℕ) :
    MvPowerSeries (Fin d) R →ₗ[R] MvPowerSeries (Fin d) R where
  toFun := (invDer μ u)^[n]
  map_add' := by
    obtain ⟨hadd, -, -⟩ := GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear R d μ hμ u
    induction n with
    | zero => intro F G; rfl
    | succ n ih => intro F G; simp only [Function.iterate_succ_apply', ih, hadd]
  map_smul' := by
    obtain ⟨-, hsmul, -⟩ := GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear R d μ hμ u
    induction n with
    | zero => intro a F; rfl
    | succ n ih => intro a F; simp only [Function.iterate_succ_apply', ih, hsmul, RingHom.id_apply]

theorem iterLin_apply {R : Type} [CommRing R] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (u : Fin d → R) (n : ℕ) (F : MvPowerSeries (Fin d) R) :
    iterLin hμ u n F = (invDer μ u)^[n] F := rfl

theorem constantCoeff_iterate_invDer_X_sub_mem : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (l : MvPowerSeries (Fin d) Q) (j : Fin d), QL μ ⊤ l → In (RingHom.ker θ) (cob1 (up Q μ) l) → lin l = Pi.single j 1 → ∀ c : Fin d → B, (∀ i, algebraMap B Q (c i) = (p : Q) * coeff (Finsupp.single i p) l) → ∀ u : Fin d → B, constantCoeff ((invDer μ u)^[p] (X j)) - ∑ i, c i * u i ^ p ∈ RingHom.ker θ ⊔ Ideal.span {(p : B)} := by
  intro p _ B O Q _ _ _ _ θ hF d μ hL l j hQL hcob hlin c hc u
  classical
  have hp : p.Prime := Fact.out
  have hμ := hL.const
  have hμQ : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ,
      map_zero]
  obtain ⟨b, hbN, hb⟩ := GlobalTheory.T.constantCoeff_iterate_invariantDerivation_mem B Q d μ hμ (RingHom.ker θ) l j hcob hlin u p hp.two_le
  have h3 := GlobalTheory.T.coeff_quasiLogarithm_integral_low_degree p B O Q θ hF d μ hL l hQL
  let P : (Fin d →₀ ℕ) → Prop := fun α => α.degree ≤ p ∧ ∀ i, α ≠ Finsupp.single i p
  let h : (Fin d →₀ ℕ) → B := fun α => if hα : P α then (h3 α hα.1 hα.2).choose else 0
  have hh : ∀ α, P α → algebraMap B Q (h α) = coeff α l := fun α hα => by
    simp only [h, dif_pos hα]; exact (h3 α hα.1 hα.2).choose_spec.symm
  let H : MvPowerSeries (Fin d) B := fun α => h α
  have hH : ∀ α, coeff α H = h α := fun α => rfl
  let q : Fin d → Q := fun i => coeff (Finsupp.single i p) l
  have hinj : ∀ i k : Fin d, Finsupp.single i p = Finsupp.single k p ↔ i = k := fun i k =>
    Finsupp.single_left_inj hp.ne_zero
  let G : MvPowerSeries (Fin d) Q :=
    map (algebraMap B Q) H + ∑ i, q i • monomial (Finsupp.single i p) (1 : Q)
  have hG : ∀ α : Fin d →₀ ℕ, α.degree ≤ p → coeff α l = coeff α G := by
    intro α hα
    simp only [G, map_add, coeff_map, hH, map_sum, map_smul, coeff_monomial, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    by_cases hP : ∀ i, α ≠ Finsupp.single i p
    · rw [hh α ⟨hα, hP⟩, Finset.sum_eq_zero (fun i _ => if_neg (hP i)), add_zero]
    · push_neg at hP
      obtain ⟨i, rfl⟩ := hP
      have : h (Finsupp.single i p) = 0 := dif_neg fun hα => hα.2 i rfl
      rw [this, map_zero, zero_add, Finset.sum_eq_single i (fun k _ hk => if_neg fun e =>
        hk ((hinj i k).1 e).symm) (by simp), if_pos rfl]

  have hnat : ∀ F : MvPowerSeries (Fin d) B,
      constantCoeff ((invDer (up Q μ) (fun i => algebraMap B Q (u i)))^[p] (map (algebraMap B Q) F)) =
        algebraMap B Q (constantCoeff ((invDer μ u)^[p] F)) := fun F => by
    rw [← constantCoeff_map, GlobalTheory.T.map_invariantDerivationFormalGroupLaw_iterate B Q (algebraMap B Q) d μ hμ u p F]; rfl
  have hmon : ∀ i : Fin d, monomial (Finsupp.single i p) (1 : Q) =
      map (algebraMap B Q) (monomial (Finsupp.single i p) (1 : B)) := fun i => by
    rw [map_monomial, (algebraMap B Q).map_one]
  have hmono : ∀ i : Fin d, constantCoeff ((invDer μ u)^[p] (monomial (Finsupp.single i p) (1 : B))) =
      (p.factorial : B) * u i ^ p := fun i => by
    have := GlobalTheory.T.constantCoeff_iterate_invariant_derivation_monomial B d μ hμ hL.unit hL.comm u (Finsupp.single i p)
    rw [Finsupp.degree_single] at this
    rw [this, Finset.prod_eq_single i (fun k _ hk => by rw [Finsupp.single_apply, if_neg (Ne.symm hk),
      pow_zero]) (by simp), Finsupp.single_eq_same]
  have e1 := GlobalTheory.T.constantCoeff_iterate_invariantDerivation_congr Q d (up Q μ) hμQ (fun i => algebraMap B Q (u i)) p l G hG
  have e2 : constantCoeff ((invDer (up Q μ) (fun i => algebraMap B Q (u i)))^[p] G) =
      algebraMap B Q (constantCoeff ((invDer μ u)^[p] H)) +
        ∑ i, q i * algebraMap B Q ((p.factorial : B) * u i ^ p) := by
    rw [← iterLin_apply hμQ]
    simp only [G, map_add, map_sum, map_smul, iterLin_apply, hmon, hnat]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_C_mul, map_mul, constantCoeff_C, hnat, hmono]
  obtain ⟨r, hr⟩ := GlobalTheory.T.constantCoeff_iterate_invariant_derivation_linear p B d μ hμ hL.unit hL.comm u H
  have hlin1 : ∀ k, coeff (Finsupp.single k 1) H = if k = j then 1 else 0 := fun k => by
    apply hF.inj
    have hPk : P (Finsupp.single k 1) := ⟨by rw [Finsupp.degree_single]; exact hp.one_le, fun i e => by
      rcases (Finsupp.single_eq_single_iff _ _ _ _).1 e with ⟨_, h1⟩ | ⟨h1, _⟩
      · exact hp.one_lt.ne h1
      · exact one_ne_zero h1⟩
    rw [hH, hh _ hPk]
    have := congrFun hlin k
    simp only [lin] at this
    rw [this, Pi.single_apply]
    split_ifs <;> simp
  have hsumX : ∑ k, constantCoeff ((invDer μ u)^[p] (X k)) * coeff (Finsupp.single k 1) H =
      constantCoeff ((invDer μ u)^[p] (X j)) := by
    simp [hlin1]
  rw [hsumX] at hr
  have key : b = constantCoeff ((invDer μ u)^[p] H) + ((p - 1).factorial : B) * ∑ i, c i * u i ^ p := by
    apply hF.inj
    rw [← hb, e1, e2]
    simp only [map_add, map_mul, map_sum, map_pow, map_natCast]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc, ← Nat.mul_factorial_pred hp.ne_zero]
    push_cast
    ring
  obtain ⟨m, hm⟩ : p ∣ (p - 1).factorial + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.wilsons_lemma]
    ring
  have hmB : ((p - 1).factorial : B) = p * m - 1 := by
    have := congrArg (Nat.cast : ℕ → B) hm
    push_cast at this
    linear_combination this
  have eq : constantCoeff ((invDer μ u)^[p] (X j)) - ∑ i, c i * u i ^ p =
      b - p * (r + m * ∑ i, c i * u i ^ p) := by
    rw [key, hmB]
    linear_combination -hr
  rw [eq]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left hbN)
    (Ideal.mem_sup_right (Ideal.mem_span_singleton.2 ⟨_, rfl⟩))

end GlobalTheory.FrobIter

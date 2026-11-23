import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalTwoGroupsRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubSubstIntegralOfIntegralDifferentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstMemIntegralDifferentialSubmoduleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralReducingToMvPowerSeriesSubstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstLeadingOfAgreeDegreeOneStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.KatzPull

open GlobalTheory.Katz

theorem lift_X (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ : Type} (s : σ) :
    Katz.lift p (X s : MvPowerSeries σ k) = X s := by
  classical
  ext α
  rw [coeff_lift, coeff_X, coeff_X]
  split_ifs
  · rw [map_one, map_one]
  · rw [WittVector.teichmuller_zero, map_zero]

theorem lin_subst {R : Type} [CommRing R] {d e : ℕ} (a : Fin e → MvPowerSeries (Fin d) R)
    (ha : ∀ j, constantCoeff (a j) = 0) (f : MvPowerSeries (Fin e) R) :
    lin (subst a f) = pullLin a (lin f) := by
  classical
  have ha' := hasSubst_of_constantCoeff_zero ha
  have hcard : ∀ α : Fin e →₀ ℕ, Multiset.card (Finsupp.toMultiset α) = α.degree := fun α => by
    rw [Finsupp.card_toMultiset, Finsupp.degree]; rfl
  have inj : Function.Injective (Finsupp.toMultiset : (Fin e →₀ ℕ) → Multiset (Fin e)) :=
    fun x y hxy => by simpa using congrArg Multiset.toFinsupp hxy
  set f1 : MvPowerSeries (Fin e) R := C (constantCoeff f) + ∑ j, C (lin f j) * X j with hf1
  have hf2 : ∀ α : Fin e →₀ ℕ, α.degree < 2 → coeff α (f - f1) = 0 := by
    intro α hα
    rcases (show α.degree = 0 ∨ α.degree = 1 by omega) with h | h
    · have h0 : α = 0 := by
        apply inj
        rw [map_zero, ← Multiset.card_eq_zero, hcard, h]
      subst h0
      simp [hf1, coeff_X]
    · obtain ⟨j, hj⟩ := Multiset.card_eq_one.1 ((hcard α).trans h)
      have h1 : α = Finsupp.single j 1 := by
        apply inj
        rw [hj, Finsupp.toMultiset_single, one_smul]
      subst h1
      simp [hf1, coeff_X, coeff_C, lin, Finsupp.single_eq_single_iff]
  funext i
  have key := (GlobalTheory.T.coeff_subst_leading_of_agree_degree_one R (Fin e) (Fin d) a a 2 (f - f1) ha ha (fun _ _ _ => rfl) hf2
    (Finsupp.single i 1)).1 (by rw [Finsupp.degree_single]; norm_num)
  rw [subst_sub ha', map_sub, sub_eq_zero] at key
  unfold lin pullLin
  rw [key, hf1, subst_add ha', subst_C, map_add, coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero),
    zero_add, ← coe_substAlgHom ha', map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, coe_substAlgHom ha', subst_C, subst_X ha', coeff_C_mul]
  rfl

theorem quasiLog_pull : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d e : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (hμ : IsLaw μ) (hν : IsLaw ν) (φ : Fin e → MvPowerSeries (Fin d) k), IsHom μ ν φ → ∀ f ∈ quasiLog p hν, subst (fun j => Katz.lift p (φ j)) f ∈ quasiLog p hμ ∧ (∀ c, Red p (cob1 (fun j => Katz.lift p (ν j)) f) c → Red p (cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f)) (pull2 φ c)) ∧ ∀ w, RedV p (lin f) w → RedV p (lin (subst (fun j => Katz.lift p (φ j)) f)) (pullLin φ w) := by
  intro p _ k _ _ _ d e μ ν hμ hν φ hφ f hf
  obtain ⟨hf1, hf2⟩ := hf
  have hΦ0 : ∀ j, constantCoeff (Katz.lift p (φ j)) = 0 := fun j => constantCoeff_lift p (hφ.const j)
  have hΦs : HasSubst (fun j => Katz.lift p (φ j)) := hasSubst_of_constantCoeff_zero hΦ0
  have hLμ0 : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (hμ.const i)
  have hLμs : HasSubst (fun i => Katz.lift p (μ i)) := hasSubst_of_constantCoeff_zero hLμ0
  have hLν0 : ∀ i, constantCoeff (Katz.lift p (ν i)) = 0 := fun i => constantCoeff_lift p (hν.const i)
  have hXl0 : ∀ i : Fin d, constantCoeff (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)) = 0 :=
    fun _ => constantCoeff_X _
  have hXr0 : ∀ i : Fin d, constantCoeff (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)) = 0 :=
    fun _ => constantCoeff_X _
  have hXls := hasSubst_of_constantCoeff_zero hXl0
  have hXrs := hasSubst_of_constantCoeff_zero hXr0
  have RR := fun σ => GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k σ
  have hRedΦ : ∀ j, Red p (Katz.lift p (φ j)) (φ j) := fun j => (RR _).2.2.1 (φ j)
  have redX : ∀ {σ : Type} (s : σ), Red p (X s : MvPowerSeries σ (Fr p k)) (X s) := fun s => by
    simpa [lift_X] using (RR _).2.2.1 (X s : MvPowerSeries _ k)
  have hIL := GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin d) (Fin d ⊕ Fin d) (fun i => X (Sum.inl i)) (fun i => X (Sum.inl i))
    hXl0 (fun i => redX _)
  have hIR := GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin d) (Fin d ⊕ Fin d) (fun i => X (Sum.inr i)) (fun i => X (Sum.inr i))
    hXr0 (fun i => redX _)

  set U : Fin e ⊕ Fin e → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k) :=
    Sum.elim (fun j => inL (Katz.lift p (φ j))) (fun j => inR (Katz.lift p (φ j))) with hU
  set U' : Fin e ⊕ Fin e → MvPowerSeries (Fin d ⊕ Fin d) k :=
    Sum.elim (fun j => inL (φ j)) (fun j => inR (φ j)) with hU'
  have hinL0 : ∀ j, constantCoeff (inL (Katz.lift p (φ j))) = 0 := fun j =>
    constantCoeff_subst_eq_zero hXls hXl0 (hΦ0 j)
  have hinR0 : ∀ j, constantCoeff (inR (Katz.lift p (φ j))) = 0 := fun j =>
    constantCoeff_subst_eq_zero hXrs hXr0 (hΦ0 j)
  have hU0 : ∀ s, constantCoeff (U s) = 0 := by
    rintro (j | j)
    · exact hinL0 j
    · exact hinR0 j
  have hRedU : ∀ s, Red p (U s) (U' s) := by
    rintro (j | j)
    · exact hIL.1 _ _ (hRedΦ j)
    · exact hIR.1 _ _ (hRedΦ j)
  have hIU := GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin e ⊕ Fin e) (Fin d ⊕ Fin d) U U' hU0 hRedU
  have C6 := GlobalTheory.T.powerSeriesEvalTwoGroups_rules (Fr p k) e (Fin d ⊕ Fin d) (Fin d ⊕ Fin d)
    (fun j => inL (Katz.lift p (φ j))) (fun j => inR (Katz.lift p (φ j))) hinL0 hinR0

  set A : Fin e → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k) :=
    fun j => subst (fun i => Katz.lift p (μ i)) (Katz.lift p (φ j)) with hA
  set B : Fin e → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k) :=
    fun j => subst U (Katz.lift p (ν j)) with hB
  have hA0 : ∀ j, constantCoeff (A j) = 0 := fun j => constantCoeff_subst_eq_zero hLμs hLμ0 (hΦ0 j)
  have hB0 : ∀ j, constantCoeff (B j) = 0 := fun j =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hU0) hU0 (hLν0 j)
  have hRA : ∀ j, Red p (A j) (subst μ (φ j)) := fun j =>
    (GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin d) (Fin d ⊕ Fin d) _ μ hLμ0 (fun i => (RR _).2.2.1 (μ i))).1 _ _ (hRedΦ j)
  have hRB : ∀ j, Red p (B j) (subst μ (φ j)) := fun j => by
    rw [hφ.hom j]
    exact hIU.1 _ _ ((RR _).2.2.1 (ν j))
  have hD := GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin e) (Fin d ⊕ Fin d) A B (fun j => subst μ (φ j)) f hA0 hB0 hRA hRB hf1

  have hid : cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f) =
      (subst A f - subst B f) + subst U (cob1 (fun j => Katz.lift p (ν j)) f) := by
    have e1 : subst U (cob1 (fun j => Katz.lift p (ν j)) f) =
        subst B f - subst (fun j => inL (Katz.lift p (φ j))) f - subst (fun j => inR (Katz.lift p (φ j))) f := by
      change at2 (cob1 (fun j => Katz.lift p (ν j)) f) _ _ = _
      unfold cob1
      rw [(C6.2.2.1 _ _).2, (C6.2.2.1 _ _).2, C6.1, C6.2.1, C6.2.2.2.2.2.1 e _ hLν0]
      rfl
    rw [e1]
    unfold cob1 inL inR
    rw [subst_comp_subst_apply hΦs hLμs, subst_comp_subst_apply hΦs hXls,
      subst_comp_subst_apply hΦs hXrs]
    abel
  have part2 : ∀ c, Red p (cob1 (fun j => Katz.lift p (ν j)) f) c →
      Red p (cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f)) (pull2 φ c) := by
    intro c hc
    rw [hid]
    have h1 := ((RR _).2.2.2.2.2.1 _).1 hD
    have h2 := hIU.1 _ _ hc
    have := ((RR _).2.2.2.1 _ _ _ _ h1 h2).1
    rwa [zero_add] at this
  refine ⟨⟨GlobalTheory.T.subst_mem_integralDifferentialSubmodule p k (Fin e) (Fin d) _ f hΦ0
      (fun j => ((RR _).1 _).2 ⟨φ j, hRedΦ j⟩) hf1, ?_⟩, part2, ?_⟩
  · obtain ⟨c, hc⟩ := ((RR _).1 _).1 hf2
    exact ((RR _).1 _).2 ⟨_, part2 c hc⟩
  · intro w hw i
    rw [lin_subst _ hΦ0]
    choose a ha ha' using hw
    refine ⟨∑ j, a j * WittVector.teichmuller p (lin (φ j) i), ?_, ?_⟩
    · simp only [pullLin, map_sum, map_mul, ha]
      rfl
    · simp only [pullLin, map_sum, map_mul, ha', WittVector.teichmuller_coeff_zero]
      rfl

end GlobalTheory.KatzPull

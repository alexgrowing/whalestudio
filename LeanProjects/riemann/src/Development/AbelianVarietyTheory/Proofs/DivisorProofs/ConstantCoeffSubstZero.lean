import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalTwoGroupsRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubSubstIntegralOfIntegralDifferentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralReducingToMvPowerSeriesSubstStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.PullQuasiLog

theorem lift_X (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ : Type} (j : σ) :
    Katz.lift p (X j : MvPowerSeries σ k) = X j := by
  classical
  ext α
  rw [coeff_lift, coeff_X, coeff_X]
  split_ifs <;> simp

theorem intBy_le_one (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ : Type}
    (c : WittVector p k) : intBy p k σ c ≤ intBy p k σ 1 := by
  intro f hf α
  obtain ⟨w, hw⟩ := hf α
  exact ⟨c * w, by rw [hw, one_mul]⟩

theorem constantCoeff_subst_zero {R : Type} [CommRing R] {σ τ : Type} [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ R}
    (hf : constantCoeff f = 0) : constantCoeff (subst a f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha hf

theorem elim_const {R : Type} [CommRing R] {d : ℕ} {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    ∀ s, constantCoeff (Sum.elim u v s) = 0 := fun s => by cases s <;> simp [hu, hv]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d e : ℕ) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (hν : IsLaw ν), ∀ f ∈ quasiLog p hν, subst (fun j => Katz.lift p (X j : MvPowerSeries (Fin e) k)) f = f ∧ (∀ (d' : ℕ) (φ : Fin d → MvPowerSeries (Fin d') k) (ψ : Fin e → MvPowerSeries (Fin d) k), (∀ j, constantCoeff (φ j) = 0) → (∀ j, constantCoeff (ψ j) = 0) → subst (fun l => Katz.lift p (subst φ (ψ l))) f - subst (fun j => Katz.lift p (φ j)) (subst (fun l => Katz.lift p (ψ l)) f) ∈ intBy p k (Fin d') 1) ∧ ∀ φ ψ : Fin e → MvPowerSeries (Fin d) k, (∀ j, constantCoeff (φ j) = 0) → (∀ j, constantCoeff (ψ j) = 0) → subst (fun l => Katz.lift p (op ν φ ψ l)) f - subst (fun l => Katz.lift p (φ l)) f - subst (fun l => Katz.lift p (ψ l)) f ∈ intBy p k (Fin d) 1 := by
  intro p _ k _ _ _ d e ν hν f hf
  have hf' : f ∈ quasiInt p k (Fin e) ∧ cob1 (fun i => lift p (ν i)) f ∈ intBy p k _ 1 := hf
  have hred := fun (σ : Type) => GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k σ
  refine ⟨?_, ?_, ?_⟩
  · have : (fun j => Katz.lift p (X j : MvPowerSeries (Fin e) k)) = X := funext fun j => lift_X p j
    rw [this, subst_self]; rfl
  · intro d' φ ψ hφ hψ
    have hΦ : ∀ j, constantCoeff (lift p (φ j)) = 0 := fun j => constantCoeff_lift p (hφ j)
    have hΨ : ∀ j, constantCoeff (lift p (ψ j)) = 0 := fun j => constantCoeff_lift p (hψ j)
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hΨ)
      (hasSubst_of_constantCoeff_zero hΦ)]
    apply intBy_le_one p (p : WittVector p k)
    refine GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin e) (Fin d') _ _ (fun l => subst φ (ψ l)) f
      (fun l => constantCoeff_lift p (constantCoeff_subst_zero hφ (hψ l)))
      (fun l => constantCoeff_subst_zero hΦ (hΨ l))
      (fun l => (hred (Fin d')).2.2.1 _)
      (fun l => (GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin d) (Fin d') (fun j => lift p (φ j)) φ hΦ
        (fun j => (hred (Fin d')).2.2.1 _)).1 _ _ ((hred (Fin d)).2.2.1 _)) hf'.1
  · intro φ ψ hφ hψ
    set Φ : Fin e → MvPowerSeries (Fin d) (Fr p k) := fun l => lift p (φ l) with hΦdef
    set Ψ : Fin e → MvPowerSeries (Fin d) (Fr p k) := fun l => lift p (ψ l) with hΨdef
    have hΦ : ∀ j, constantCoeff (Φ j) = 0 := fun j => constantCoeff_lift p (hφ j)
    have hΨ : ∀ j, constantCoeff (Ψ j) = 0 := fun j => constantCoeff_lift p (hψ j)
    have hL : ∀ i, constantCoeff (lift p (ν i)) = 0 := fun i => constantCoeff_lift p (hν.const i)
    have hcalc := GlobalTheory.T.powerSeriesEvalTwoGroups_rules (Fr p k) e (Fin d) (Fin d) Φ Ψ hΦ hΨ
    have hredE : ∀ s, Red p (Sum.elim Φ Ψ s) (Sum.elim φ ψ s) := fun s => by
      cases s <;> exact (hred (Fin d)).2.2.1 _
    have hsub := GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin e ⊕ Fin e) (Fin d) (Sum.elim Φ Ψ) (Sum.elim φ ψ)
      (elim_const hΦ hΨ) hredE
    have hcob : at2 (cob1 (fun i => lift p (ν i)) f) Φ Ψ =
        subst (op (fun i => lift p (ν i)) Φ Ψ) f - subst Φ f - subst Ψ f := by
      unfold cob1
      rw [(hcalc.2.2.1 _ _).2, (hcalc.2.2.1 _ _).2, hcalc.1, hcalc.2.1,
        hcalc.2.2.2.2.2.1 e _ hL f]
      rfl
    have h1 : at2 (cob1 (fun i => lift p (ν i)) f) Φ Ψ ∈ intBy p k (Fin d) 1 :=
      hsub.2 1 _ hf'.2
    have h2 : subst (fun l => lift p (op ν φ ψ l)) f - subst (op (fun i => lift p (ν i)) Φ Ψ) f
        ∈ intBy p k (Fin d) 1 := by
      apply intBy_le_one p (p : WittVector p k)
      refine GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin e) (Fin d) _ _ (op ν φ ψ) f
        (fun l => constantCoeff_lift p (constantCoeff_subst_zero (elim_const hφ hψ) (hν.const l)))
        (fun l => constantCoeff_subst_zero (elim_const hΦ hΨ) (hL l))
        (fun l => (hred (Fin d)).2.2.1 _)
        (fun l => hsub.1 _ _ ((hred (Fin e ⊕ Fin e)).2.2.1 _)) hf'.1
    have := add_mem h2 h1
    rw [hcob] at this
    convert this using 1
    abel

end GlobalTheory.Katz.PullQuasiLog

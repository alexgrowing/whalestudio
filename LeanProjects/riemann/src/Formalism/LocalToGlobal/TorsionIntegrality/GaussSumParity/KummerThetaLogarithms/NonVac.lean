import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementN
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.KernelFromKOne
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D.ChainWitness

open Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Integral Unram)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog Simeq Gser BetaHyp)

theorem fieldWitness (hF : KurFrob) (hR : KurRoots) (hC : KurComplete) (hT : TrDualExists)
    (hB : FOfBetaHyp) (l : ℕ) [Fact l.Prime] (hl : 2 < l) (ν : ℕ) [NeZero ν] :
    ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ ∧ CompleteSpace (MaximalUnramifiedExtension l) ∧
      (∀ a, ‖(MaximalUnramifiedExtension l).subtype a‖ = ‖a‖) ∧
      (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ 2 - 1)) ∧
      (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ (2 * ν) - 1)) ∧
      2 ≤ 2 * ν ∧ Even (2 * ν) ∧
      (∃ ϖ : ℂ_[l], ϖ ^ (l ^ 2 - 1) = (l : ℂ_[l])) ∧
      (∃ om oms : Fin ν → MaximalUnramifiedExtension l, OwOK (2 * ν) σ om oms ∧ TrDual (2 * ν) σ om oms) ∧
      ∃ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F ∧
        ∃ be : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), F1 F be ∧ F2 l σ be ∧ ¬ Simeq be 0 := by
  obtain ⟨σ, hσ, -⟩ := hF l hl
  have hl1 : 1 < l := by omega
  have hnd : ∀ k : ℕ, 0 < k → 0 < l ^ k - 1 ∧ ¬ l ∣ l ^ k - 1 := by
    intro k hk
    have h1 : 1 < l ^ k := Nat.one_lt_pow hk.ne' hl1
    refine ⟨by omega, fun hdv => ?_⟩
    have h2 : l ∣ l ^ k := dvd_pow_self l hk.ne'
    have h3 : l ∣ 1 := by
      have := (Nat.dvd_sub h2 hdv)
      rwa [Nat.sub_sub_self h1.le] at this
    exact absurd (Nat.le_of_dvd one_pos h3) (by omega)
  have hν : 0 < ν := Nat.pos_of_ne_zero (NeZero.ne ν)
  obtain ⟨ζ2, hζ2⟩ := hR l (l ^ 2 - 1) (hnd 2 (by norm_num)).1 (hnd 2 (by norm_num)).2
  obtain ⟨ζd, hζd⟩ := hR l (l ^ (2 * ν) - 1) (hnd _ (by omega)).1 (hnd _ (by omega)).2
  have hdual := hT (MaximalUnramifiedExtension l) l (2 * ν) σ hσ (even_two_mul ν) ζd hζd
  rw [Nat.mul_div_cancel_left ν two_pos] at hdual
  obtain ⟨F, hFl⟩ := (Formalism.InvariantFactorPaths.G7.Top.lawExists (MaximalUnramifiedExtension l) l hσ.1 hσ.2.2.1).1
  have h1 : σ (σ (1 : MaximalUnramifiedExtension l)) = 1 := by simp
  have hbeta := Formalism.InvariantFactorPaths.G7.Top.gcIsBeta (MaximalUnramifiedExtension l) l σ hσ F hFl 1 (by simp) h1
  have hFF := hB (MaximalUnramifiedExtension l) l σ hσ ⟨ζ2, hζ2⟩ F hFl _ hbeta
  refine ⟨σ, hσ, hC l, fun _ => rfl, ⟨ζ2, hζ2⟩, ⟨ζd, hζd⟩, by omega, even_two_mul ν, ?_, hdual,
    F, hFl, _, hFF.1, hFF.2, ?_⟩
  · exact IsAlgClosed.exists_pow_nat_eq _ (hnd 2 (by norm_num)).1
  · intro h0
    have hz : (Gser l (0 : MaximalUnramifiedExtension l) (σ 0)) = 0 := by simp [Gser]
    have := Formalism.InvariantFactorPaths.G7.Top.gcUnique (MaximalUnramifiedExtension l) l σ hσ 1 0 h1 (by simp) (by rw [hz]; exact h0)
    exact one_ne_zero this

theorem fullWitness (hF : KurFrob) (hR : KurRoots) (hC : KurComplete) (hT : TrDualExists)
    (hB : FOfBetaHyp) (l : ℕ) [Fact l.Prime] (hl : 2 < l) (ν r0 r1 : ℕ) [NeZero ν] :
    ∃ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F be : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (om oms : Fin ν → MaximalUnramifiedExtension l)
      (U0 Φ : MvPowerSeries (Bool × Fin ν × Fin r0 × Fin r1) ℂ_[l]) (ph : PowerSeries (MaximalUnramifiedExtension l)),
      UnrOK (MaximalUnramifiedExtension l) l σ ∧ CompleteSpace (MaximalUnramifiedExtension l) ∧ (∀ a, ‖(MaximalUnramifiedExtension l).subtype a‖ = ‖a‖) ∧
      (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ 2 - 1)) ∧
      (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ (2 * ν) - 1)) ∧ 2 ≤ 2 * ν ∧ Even (2 * ν) ∧
      (∃ ϖ : ℂ_[l], ϖ ^ (l ^ 2 - 1) = (l : ℂ_[l])) ∧
      OwOK (2 * ν) σ om oms ∧ TrDual (2 * ν) σ om oms ∧ IsLawOfLog l F ∧ F1 F be ∧ F2 l σ be ∧
      ¬ Simeq be 0 ∧ Integral U0 ∧ MvPowerSeries.constantCoeff Φ = 0 ∧
      Simeq Φ (sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be)) ∧
      Simeq (MvPowerSeries.C (2 : MaximalUnramifiedExtension l) * ph)
        (MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries (MaximalUnramifiedExtension l))) be) := by
  obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7, h8, ⟨om, oms, h9, h10⟩, F, h11, be, h12, h13, h14⟩ :=
    fieldWitness hF hR hC hT hB l hl ν
  have hbe0 : MvPowerSeries.constantCoeff be = 0 := by
    have := h12.1 0 (Or.inl rfl)
    simpa using this
  refine ⟨σ, F, be, om, oms, 1, sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be),
    PowerSeries.C ((2 : MaximalUnramifiedExtension l)⁻¹) *
      MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries (MaximalUnramifiedExtension l))) be,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [MvPowerSeries.coeff_one]
    split_ifs <;> simp
  · unfold sumE
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro e _
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro i; simp)) (by intro i; simp)
      (by rw [MvPowerSeries.constantCoeff_map, hbe0, map_zero])
  · exact (Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[l] _).1 _
  · have : MvPowerSeries.C (2 : MaximalUnramifiedExtension l) * (PowerSeries.C ((2 : MaximalUnramifiedExtension l)⁻¹) *
        MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries (MaximalUnramifiedExtension l))) be) =
        MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries (MaximalUnramifiedExtension l))) be := by
      rw [← mul_assoc]
      have h2 : (MvPowerSeries.C (2 : MaximalUnramifiedExtension l) : MvPowerSeries Unit (MaximalUnramifiedExtension l)) *
          PowerSeries.C ((2 : MaximalUnramifiedExtension l)⁻¹) = 1 := by
        change (MvPowerSeries.C (2 : MaximalUnramifiedExtension l) : MvPowerSeries Unit (MaximalUnramifiedExtension l)) *
          MvPowerSeries.C ((2 : MaximalUnramifiedExtension l)⁻¹) = 1
        rw [← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
      rw [h2, one_mul]
    rw [this]
    exact (Formalism.InvariantFactorPaths.G7.Top.simeqRules (MaximalUnramifiedExtension l) _).1 _

end Formalism.L2.Th1.D.ChainWitness

namespace Formalism.L2.Th1.D

theorem chain_nonvacuous : ChainNonVacuous := fun l _ hl ν r0 r1 _ =>
  ChainWitness.fullWitness kurFrob kurRoots kurComplete trDualExists fOfBetaHyp l hl ν r0 r1

end Formalism.L2.Th1.D

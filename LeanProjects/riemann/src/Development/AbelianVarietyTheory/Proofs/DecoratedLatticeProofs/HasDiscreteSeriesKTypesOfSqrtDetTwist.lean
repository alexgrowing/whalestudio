import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KStableSubmoduleEqTopOfHighestWeightLeStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

noncomputable section

namespace GlobalTheory.CoverDS.TwistTypes

variable {p q : ℕ}

theorem sum_rhoNC (lam : Ix p q → ℚ) : ∑ a, rhoNC lam a = 0 := by
  have symm : ∀ a b : Ix p q, sameBlock a b ↔ sameBlock b a := by
    intro a b; cases a <;> cases b <;> simp [sameBlock]
  have k1 : ∑ a, ((Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam b < lam a).card : ℚ) =
      ∑ a, ((Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam a < lam b).card : ℚ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [symm a b]
  have k2 : ∑ a, ((Finset.univ.filter fun b => sameBlock a b ∧ lam b < lam a).card : ℚ) =
      ∑ a, ((Finset.univ.filter fun b => sameBlock a b ∧ lam a < lam b).card : ℚ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [symm a b]
  simp only [rhoNC, Finset.sum_sub_distrib, ← Finset.sum_div, k1, k2, sub_self, zero_div]

theorem normSq_add_half (lam : Ix p q → ℚ) :
    normSq (fun a => lam a + 1 / 2) =
      normSq lam + ∑ a, (lam a + 1 / 2) - (Fintype.card (Ix p q) : ℚ) / 4 := by
  have e : ∀ a, (lam a + 1 / 2) ^ 2 = lam a ^ 2 + (lam a + 1 / 2) - 1 / 4 := fun a => by ring
  simp only [normSq, e, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem casimir_twAct (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (v : V) :
    casimir (Cover.twAct act) v = casimir act v - act 1 v + ((Fintype.card (Ix p q) : ℂ) / 4) • v := by
  have hterm : ∀ a b, Cover.twAct act (Eab a b) (Cover.twAct act (Eab b a) v) =
      act (Eab a b) (act (Eab b a) v) - if a = b then act (Eab a a) v - (1 / 4 : ℂ) • v else 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      simp only [Cover.twAct_apply, if_true, Eab, Matrix.trace_single_eq_same, map_sub, map_smul]
      module
    · simp [Cover.twAct_apply, hab, Eab, Matrix.trace_single_eq_of_ne _ _ _ hab,
        Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hab)]
  have h1 : act 1 v = ∑ a, act (Eab a a) v := by
    rw [← Matrix.sum_single_one, map_sum, LinearMap.sum_apply]
    rfl
  simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, hterm, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, h1, Finset.sum_const, Finset.card_univ]
  module

theorem hwSub_twAct (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) :
    hwSub (Cover.twAct act) μ = hwSub act fun a => μ a + 1 / 2 := by
  ext v
  by_cases hv : v = 0
  · subst hv
    exact iff_of_true (Submodule.zero_mem _) (Submodule.zero_mem _)
  · exact ⟨fun h => ((Cover.isHW_twAct act μ v).1 ⟨hv, h⟩).2, fun h => ((Cover.isHW_twAct act μ v).2 ⟨hv, h⟩).2⟩

theorem sum_of_inCone {lam μ : Ix p q → ℚ} (h : InCone lam μ) : ∑ a, μ a = ∑ a, lam a := by
  obtain ⟨m, -, rfl⟩ := h
  have e : ∑ c, ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_add_distrib, e, blattner, sum_rhoNC, add_zero]

theorem inCone_add {lam μ : Ix p q → ℚ} (c : ℚ) (h : InCone lam fun a => μ a - c) :
    InCone (fun a => lam a + c) μ := by
  obtain ⟨m, hm, hμ⟩ := h
  refine ⟨m, fun a b hab => add_lt_add_left (hm a b hab) c, funext fun a => ?_⟩
  have := congrFun hμ a
  rw [Cover.blattner_add]
  simp only at this ⊢
  linarith

theorem hasTypes_of_twist (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ)
    (h : HasTypes (Cover.twist R) lam) : HasTypes R fun a => lam a + 1 / 2 := by
  have h1 : Module.finrank ℂ ↥(hwSub (Cover.twAct R.HK.act) (blattner lam)) = 1 := h.1
  have h2 : ∀ v, casimir (Cover.twAct R.HK.act) v = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • v := h.2.1
  have h3 : ∀ (μ : Ix p q → ℚ) v, IsHW (Cover.twAct R.HK.act) μ v → InCone lam μ := h.2.2
  have hcone : ∀ (μ : Ix p q → ℚ) v, IsHW R.HK.act μ v → InCone (fun a => lam a + 1 / 2) μ := fun μ v hv =>
    inCone_add _ (h3 _ v ((Cover.isHW_twAct _ _ v).2 (by simpa only [sub_add_cancel] using hv)))
  refine ⟨by rwa [Cover.blattner_add, ← hwSub_twAct], fun v => ?_, hcone⟩
  set c : ℂ := ((∑ a, (lam a + 1 / 2) : ℚ) : ℂ) with hc
  have htop : LinearMap.ker (R.HK.act 1 - c • LinearMap.id) = ⊤ := by
    refine GlobalTheory.T.kStable_submodule_eq_top_of_highestWeight_le p q R.HK _ (fun X _ w hw => ?_) fun μ w hw => ?_
    · have e := congrArg (fun f : Module.End ℂ R.HK.V => f w) (R.HK.lie X 1)
      simp only [Matrix.mul_one, Matrix.one_mul, sub_self, map_zero, LinearMap.zero_apply, LinearMap.sub_apply,
        Module.End.mul_apply] at e
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hw ⊢
      rw [← sub_eq_zero.1 e.symm, hw, map_smul]
    · by_cases h0 : w = 0
      · rw [h0]
        exact Submodule.zero_mem _
      have e := sum_of_inCone (hcone μ w ⟨h0, hw⟩)
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      rw [hc, ← e, ← Matrix.sum_single_one, map_sum, LinearMap.sum_apply, Rat.cast_sum, Finset.sum_smul]
      exact Finset.sum_congr rfl fun a _ => ((mem_hwSub_iff _ _ _).1 hw).1 a
  have hv : R.HK.act 1 v = c • v := by
    simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      using Submodule.eq_top_iff'.1 htop v
  have e := casimir_twAct R.HK.act v
  rw [h2, hv] at e
  rw [normSq_add_half, Rat.cast_sub, Rat.cast_sub, Rat.cast_add, ← hc]
  rw [Rat.cast_sub] at e
  push_cast
  linear_combination (norm := module) -e

end GlobalTheory.CoverDS.TwistTypes

end

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSmoothAdelicFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSlowlyIncreasingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreEnvelopingAlgebraCommuteRealLieSmoothingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingRightTranslateMaxCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimensionalSpaceAutomorphicSmoothing
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth

noncomputable section

open GlobalTheory.AutGrowth.SmoothFinite

namespace GlobalTheory.CapKilledSmooth

theorem smoothing_mem_space : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (b : ℕ) (ν : Measure (Lie E b)) [ν.IsAddHaarMeasure] (α : Lie E b → ℂ), IsTest (invSet E b) α → KInv α → ∀ (L : Subgroup (GL (Fin b) (Af E))) (W : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W → ∀ (q : (E →+* ℂ) → ℂ → Polynomial ℂ) (ψ : Sm E b), ψ ∈ leftInv E b ⊓ fixL E b L ⊓ GlobalTheory.CapKilled.ktype E b W ⊓ GlobalTheory.CapKilled.killed E b q → ψ.1 ∈ growth E b → ∃ h : smoothing ν α ψ.1 ∈ Sm E b, (⟨smoothing ν α ψ.1, h⟩ : Sm E b) ∈ GlobalTheory.CapKilled.space E b L W q := by
  intro E _ _ _ b ν _ α hα hK L W hW q ψ hψ hg
  obtain ⟨⟨⟨hl, hL⟩, hk⟩, hq⟩ := hψ
  have h := GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E b ν α hα ψ.1 ψ.2
  refine ⟨h, GlobalTheory.CapKilled.mem_space.2 ⟨fun γ g => ?_, fun k hk' => ?_, fun g => ?_, fun τ u => ?_, fun l => ?_⟩⟩
  · show smoothing ν α ψ.1 (ratGL E b γ * g) = smoothing ν α ψ.1 g
    have hl' : ∀ γ g, ψ.1 (ratGL E b γ * g) = ψ.1 g := hl
    simp only [smoothing, chart, mul_assoc, hl']
  · apply Subtype.ext; funext g
    show smoothing ν α ψ.1 (g * finGL E b k) = smoothing ν α ψ.1 g
    have hw : (fun x => ψ.1 (x * finGL E b k)) = ψ.1 := congrArg Subtype.val (hL k hk')
    simp only [smoothing]
    rw [← chart_rt_fin, hw]
  · obtain ⟨s, c, hc⟩ := GlobalTheory.HCFct.exists_interp W hW
    have hpt : ∀ (k : Kinf E b) (x : GA E b), ψ.1 (x * infGL E b (Unitary.toUnits k)) =
        ∑ i : s, ψ.1 (x * infGL E b (Unitary.toUnits i.1)) * (c i).1 k := fun k x => hc _ (hk x) k
    have hfun : ∀ k : Kinf E b, (fun x => ψ.1 (x * infGL E b (Unitary.toUnits k))) =
        (∑ i : s, (c i).1 k • cptRep E b i.1 ψ : Sm E b).1 := by
      intro k; funext x
      rw [hpt k x, Submodule.coe_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
      rfl
    have e : (fun k : Kinf E b => (cptRep E b k ⟨smoothing ν α ψ.1, h⟩).1 g) =
        ∑ i : s, (smoothing ν α (cptRep E b i.1 ψ).1 g) • (c i).1 := by
      funext k
      have e1 : (cptRep E b k ⟨smoothing ν α ψ.1, h⟩).1 g =
          smoothing ν α ψ.1 (g * infGL E b (Unitary.toUnits k)) := rfl
      rw [e1, ← GlobalTheory.T.smoothing_right_translate_maxCompact E b ν α hK ψ.1 k g, hfun k]
      have hsum : ∀ (t : Finset s) (f : s → Sm E b),
          smoothing ν α (∑ i ∈ t, f i).1 = ∑ i ∈ t, smoothing ν α (f i).1 := by
        intro t f
        classical
        induction t using Finset.induction_on with
        | empty => funext x; simp [smoothing, chart]
        | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, smoothing_add ν hα, ih]
      rw [hsum, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smoothing_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
    rw [e]
    exact W.sum_mem fun i _ => W.smul_mem _ (c i).2
  · have hz : Polynomial.aeval (cap (a := b) τ u) (q τ u) ∈ Zalg E b := by
      show _ ∈ Algebra.adjoin ℂ _
      exact Algebra.adjoin_mono (s := {cap (a := b) τ u}) (by rintro _ rfl; exact ⟨τ, u, rfl⟩)
        (Polynomial.aeval_mem_adjoin_singleton ℂ _)
    apply Subtype.ext
    rw [GlobalTheory.T.centreEnvelopingAlgebra_commute_realLieSmoothing E b ν α hα ψ h _ hz, (GlobalTheory.CapKilled.mem_killed.1 hq) τ u]
    funext g
    simp [smoothing, chart]
  · obtain ⟨β, hβ, e⟩ : ∃ β, IsTest (invSet E b) β ∧
        ((l.map (lie E b)).prod (⟨smoothing ν α ψ.1, h⟩ : Sm E b)).1 = smoothing ν β ψ.1 := by
      induction l with
      | nil => exact ⟨α, hα, rfl⟩
      | cons X l ih =>
        obtain ⟨β, hβ, e⟩ := ih
        refine ⟨dens X β, isTest_dens X hβ, funext fun g => ?_⟩
        rw [List.map_cons, List.prod_cons, Module.End.mul_apply, lie_apply, e]
        exact GlobalTheory.T.lieDerivative_realLieSmoothing_eq_density E b ν β hβ ψ.1 ψ.2 X g
    rw [e]
    exact GlobalTheory.T.realLieSmoothing_mem_slowlyIncreasing E b ν β hβ ψ.1 hg

end GlobalTheory.CapKilledSmooth

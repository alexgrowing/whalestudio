import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift

open Formalism.REAL in

theorem kMean_translate {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) {n : ℕ}
    (c : Fin n → KG (M.ε τ) → ℂ) (hc : IsCoefFam c) (w : M.H τ) (i : Fin n) (k₀ : KG (M.ε τ)) :
    ∃ d : Fin n → ℂ, M.σ τ (toMK k₀) (kMean M τ (c i) w) = ∑ j, d j • kMean M τ (c j) w := by
  have hds := M.ds τ
  have : CompleteSpace (M.H τ) := hds.1
  obtain ⟨⟨-, hmul⟩, -, hcont⟩ := hds.2.2.1
  have hmem : ∀ k : KG (M.ε τ), toMK k ∈ Formalism.MainNotions.S.UJset (M.ε τ) := fun k => (k : UJ (M.ε τ)).2
  have hcK : Continuous fun k : KG (M.ε τ) => M.σ τ (toMK k) w :=
    (hcont w).comp_continuous (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)) hmem
  have hint : ∀ j, Integrable (fun k => c j k • M.σ τ (toMK k) w) (muK (M.ε τ)) := fun j =>
    ((hc.1 j).smul hcK).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  have hm : ∀ k : KG (M.ε τ), M.σ τ (toMK (k₀ * k)) = (M.σ τ (toMK k₀)).comp (M.σ τ (toMK k)) :=
    fun k => hmul _ (hmem k₀) _ (hmem k)
  obtain ⟨d, hd⟩ := hc.2 k₀⁻¹ i
  refine ⟨d, ?_⟩
  unfold kMean
  calc M.σ τ (toMK k₀) (∫ k, c i k • M.σ τ (toMK k) w ∂muK (M.ε τ))
      = ∫ k, M.σ τ (toMK k₀) (c i k • M.σ τ (toMK k) w) ∂muK (M.ε τ) :=
        (ContinuousLinearMap.integral_comp_comm _ (hint i)).symm
    _ = ∫ k, (fun x => c i (k₀⁻¹ * x) • M.σ τ (toMK x) w) (k₀ * k) ∂muK (M.ε τ) := by
        congr 1
        funext k
        simp only [inv_mul_cancel_left, ContinuousLinearMap.map_smul, hm k]
        rfl
    _ = ∫ k, c i (k₀⁻¹ * k) • M.σ τ (toMK k) w ∂muK (M.ε τ) :=
        integral_mul_left_eq_self (μ := muK (M.ε τ)) (fun x => c i (k₀⁻¹ * x) • M.σ τ (toMK x) w) k₀
    _ = ∑ j, d j • ∫ k, c j k • M.σ τ (toMK k) w ∂muK (M.ε τ) := by
        simp only [hd, Finset.sum_smul, mul_smul]
        have hs : ∀ j ∈ (Finset.univ : Finset (Fin n)),
            Integrable (fun k => d j • c j k • M.σ τ (toMK k) w) (muK (M.ε τ)) := fun j _ => (hint j).smul (d j)
        rw [integral_finsetSum _ hs]
        simp only [integral_smul]

theorem kMean_mem_kFin_of_coefFam : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
    (n : ℕ) (c : Fin n → Formalism.REAL.KG (M.ε τ) → ℂ), IsCoefFam c → ∀ (w : M.H τ) (i : Fin n),
    kMean M τ (c i) w ∈ kFin M τ := by
  intro D V S M τ n c hc w i
  unfold GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin
  rw [GlobalTheory.KFiniteVectors.mem_kFiniteVectors]
  refine ⟨Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w),
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _), Submodule.subset_span ⟨i, rfl⟩, ?_⟩
  intro g hg x hx
  rw [← Formalism.REAL.range_toMK] at hg
  obtain ⟨k₀, rfl⟩ := hg
  have hle : Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w) ≤
      (Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w)).comap
        (M.σ τ (Formalism.REAL.toMK k₀) : M.H τ →ₗ[ℂ] M.H τ) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨d, hd⟩ := kMean_translate M τ c hc w j k₀
    change M.σ τ (Formalism.REAL.toMK k₀) (kMean M τ (c j) w) ∈ Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w)
    rw [hd]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  exact hle hx

end GlobalTheory.Chain.IoLift

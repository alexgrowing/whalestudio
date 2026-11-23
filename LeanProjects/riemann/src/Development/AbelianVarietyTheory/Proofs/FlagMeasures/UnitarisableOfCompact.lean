import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne

open MeasureTheory GlobalTheory.Dec
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.UniTrick

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def crd (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
  (Module.finBasis ℂ V).equivFun.trans (WithLp.linearEquiv 2 ℂ (Fin (Module.finrank ℂ V) → ℂ)).symm

theorem continuous_lin {ι : Type} [Fintype ι] (ρ : Representation ℂ G V)
    (hρ : ∀ (φ : V →ₗ[ℂ] ℂ) (v : V), Continuous fun g => φ (ρ g v))
    (f : V →ₗ[ℂ] EuclideanSpace ℂ ι) (v : V) : Continuous fun g => f (ρ g v) := by
  have h : ∀ i, Continuous fun g => (f (ρ g v)) i := fun i =>
    hρ ((EuclideanSpace.proj i : EuclideanSpace ℂ ι →L[ℂ] ℂ).toLinearMap ∘ₗ f) v
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi h)

variable [MeasurableSpace G] [BorelSpace G]

def avgF (μ : Measure G) (ρ : Representation ℂ G V) (v w : V) : ℂ :=
  ∫ g, ⟪crd V (ρ g⁻¹ v), crd V (ρ g⁻¹ w)⟫_ℂ ∂μ

theorem continuous_crd_inv (ρ : Representation ℂ G V)
    (hρ : ∀ (φ : V →ₗ[ℂ] ℂ) (v : V), Continuous fun g => φ (ρ g v)) (v : V) :
    Continuous fun g : G => crd V (ρ g⁻¹ v) :=
  (continuous_lin ρ hρ (crd V).toLinearMap v).comp continuous_inv

variable [CompactSpace G]

theorem integrable_avg (μ : Measure G) [IsFiniteMeasure μ] (ρ : Representation ℂ G V)
    (hρ : ∀ (φ : V →ₗ[ℂ] ℂ) (v : V), Continuous fun g => φ (ρ g v)) (v w : V) :
    Integrable (fun g => ⟪crd V (ρ g⁻¹ v), crd V (ρ g⁻¹ w)⟫_ℂ) μ :=
  ((continuous_crd_inv ρ hρ v).inner (continuous_crd_inv ρ hρ w)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem avgF_self (μ : Measure G) (ρ : Representation ℂ G V) (v : V) :
    avgF μ ρ v v = ((∫ g, ‖crd V (ρ g⁻¹ v)‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [avgF, ← integral_complex_ofReal]
  congr 1
  funext g
  rw [inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

def core (μ : Measure G) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] (ρ : Representation ℂ G V)
    (hρ : ∀ (φ : V →ₗ[ℂ] ℂ) (v : V), Continuous fun g => φ (ρ g v)) : InnerProductSpace.Core ℂ V where
  inner v w := avgF μ ρ v w
  conj_inner_symm v w := by
    simp only [avgF]
    rw [← integral_conj]
    congr 1
    funext g
    exact inner_conj_symm _ _
  re_inner_nonneg v := by
    rw [avgF_self, RCLike.re_to_complex, Complex.ofReal_re]
    exact integral_nonneg fun _ => sq_nonneg _
  add_left u v w := by
    simp only [avgF, map_add, inner_add_left]
    exact integral_add (integrable_avg μ ρ hρ u w) (integrable_avg μ ρ hρ v w)
  smul_left v w r := by
    simp only [avgF, map_smul, inner_smul_left]
    exact integral_const_mul _ _
  definite v hv := by
    rw [avgF_self, Complex.ofReal_eq_zero] at hv
    have hc : Continuous fun g : G => ‖crd V (ρ g⁻¹ v)‖ ^ 2 := (continuous_crd_inv ρ hρ v).norm.pow 2
    have h1 := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)
      (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1 hv
    have h2 : ‖crd V (ρ (1 : G)⁻¹ v)‖ ^ 2 = 0 := congrFun ((hc.ae_eq_iff_eq μ continuous_zero).1 h1) 1
    simp only [inv_one, map_one, Module.End.one_apply, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at h2
    exact (crd V).map_eq_zero_iff.1 h2

end GlobalTheory.UniTrick

namespace GlobalTheory

end GlobalTheory

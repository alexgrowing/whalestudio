import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ULogBound
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

def IsZBasis {Em : Type} [Field Em] [NumberField Em] {N : ℕ} (I : Submodule (𝓞 Em) (Fin N → Em)) {m : ℕ}
    (b : Fin m → Fin N → Em) : Prop :=
  LinearIndependent ℤ b ∧ ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range b)

theorem UnitaryCovolumeLowerBound.one_le_rootDiscr (Em : Type) [Field Em] [NumberField Em] : 1 ≤ rootDiscr Em := by
  unfold rootDiscr
  refine Real.one_le_rpow ?_ (by positivity)
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs (discr_ne_zero Em)

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)

def hodgeInner (z : (Σ k, ι k) → ℂ) (v w : Fin D.N → Em) : ℝ :=
  ∑ τ, 2 * ‖D.herm.emb τ D.herm.ξ‖ *
    (∑ a, starRingEnd ℂ (((D.per z τ)⁻¹ *ᵥ fun b => D.herm.emb τ (v b)) a) *
      ((D.per z τ)⁻¹ *ᵥ fun b => D.herm.emb τ (w b)) a).re

theorem hodgeInner_self (z : (Σ k, ι k) → ℂ) (v : Fin D.N → Em) : D.hodgeInner z v v = D.hodgeNormSq z v := by
  unfold hodgeInner hodgeNormSq
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

open Classical in

def covolZ (z : (Σ k, ι k) → ℂ) (I : Submodule (𝓞 Em) (Fin D.N → Em)) : ℝ :=
  if h : ∃ m, ∃ b : Fin m → Fin D.N → Em, IsZBasis I b then
    Real.sqrt (Matrix.of fun k l => D.hodgeInner z (h.choose_spec.choose k) (h.choose_spec.choose l)).det
  else 0

theorem firstMinimum_le_period_norm (z : (Σ k, ι k) → ℂ) {v : Fin D.N → Em} (hv : v ∈ D.herm.L) (hv0 : v ≠ 0) :
    D.lam1 z ≤ Real.sqrt (D.hodgeNormSq z v) :=
  csInf_le ⟨0, by rintro r ⟨w, -, -, rfl⟩; exact Real.sqrt_nonneg _⟩ ⟨v, hv, hv0, rfl⟩

end FullerData

namespace UnitaryIsotropicLineExample

open GroundTheory.Heights₂.Heights.NineStatements.Gauss

abbrev z0 : (Σ _ : Unit, Fin 2) → ℂ := Line.chartBase 0

abbrev e11 : Fin 2 → Em := fun _ => 1

def isoLine : Submodule (𝓞 Em) (Fin 2 → Em) := Submodule.span (𝓞 Em) {e11}

end UnitaryIsotropicLineExample

end GroundTheory.Heights₂.Heights.NineStatements

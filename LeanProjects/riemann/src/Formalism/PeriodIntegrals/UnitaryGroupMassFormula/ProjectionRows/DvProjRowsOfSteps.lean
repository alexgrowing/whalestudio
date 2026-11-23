import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.Development

noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv

variable {K : Type} [Field K] [NumberField K] [StarRing K]

lemma star_mem_range (c : 𝓞 K) : star (algebraMap (𝓞 K) K c) ∈ Set.range (algebraMap (𝓞 K) K) := by
  have hc : IsIntegral ℤ (algebraMap (𝓞 K) K c) := c.2
  have : IsIntegral ℤ ((starRingEnd K) (algebraMap (𝓞 K) K c)) := hc.map (starRingEnd K).toIntAlgHom
  exact ⟨⟨_, this⟩, rfl⟩

def lamSub (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (U : Submodule K A.V) : Submodule (𝓞 K) A.V where
  carrier := {y | LamStar A e h U y}
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    refine ⟨Submodule.add_mem _ hx1 hy1, fun u hu => ?_, fun m hm => ?_⟩
    · rw [map_add, LinearMap.add_apply, hx2 u hu, hy2 u hu, add_zero]
    · rw [map_add, LinearMap.add_apply]
      obtain ⟨a, ha⟩ := hx3 m hm
      obtain ⟨b, hb⟩ := hy3 m hm
      exact ⟨a + b, by rw [map_add, ha, hb]⟩
  zero_mem' := by
    refine ⟨Submodule.zero_mem _, fun u _ => by simp, fun m _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro c y ⟨hy1, hy2, hy3⟩
    refine ⟨?_, fun u hu => ?_, fun m hm => ?_⟩
    · exact Submodule.smul_of_tower_mem _ c hy1
    · rw [h_smul_left, hy2 u hu, mul_zero]
    · rw [h_smul_left]
      obtain ⟨a, ha⟩ := hy3 m hm
      obtain ⟨s, hs⟩ := star_mem_range c
      exact ⟨s * a, by rw [map_mul, ha, hs]⟩

def DegDual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K),
    StarIsConj K → IsProj A e n → IsHermE A e h → IsCMFormE A e h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
      degL A (cutE A e A.L ⊓ U.restrictScalars (𝓞 K)) - degL A (cutE A e A.L) =
        degL A (lamSub A e h U)

def DegDualBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K),
    StarIsConj K → IsProj A e n → IsHermE A e h → IsCMFormE A e h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    ∀ γ : HeightOneSpectrum (𝓞 K) → ℤ, (∀ w, IsValG A e h U w (γ w)) →
      degL A (lamSub A e h U) ≤ ∑ᶠ w, lw K w * (γ w : ℝ)

theorem partB_of (h1 : DegDual) (h2 : DegDualBound) : PartB := by
  intro K _ _ _ _ _ A e n h hS hP hH hC _ U hU γ hγ
  rw [h1 K A e n h hS hP hH hC U hU]
  exact h2 K A e n h hS hP hH hC U hU γ hγ

end PI.DvRows

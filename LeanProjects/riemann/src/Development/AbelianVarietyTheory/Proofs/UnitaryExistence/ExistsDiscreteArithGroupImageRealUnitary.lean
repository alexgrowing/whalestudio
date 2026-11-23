import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral

set_option autoImplicit false

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

namespace GlobalTheory.ArithImage

open GlobalTheory.PeterssonCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem frameOf_one : frameOf X 1 = baseFr X := by
  funext τ
  show mat (frameOf X 1) τ = mat (baseFr X) τ
  rw [mat_frameOf]
  simp

theorem lact_one_fr (y : Frame X.Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ = mat y τ
  simp

theorem lact_mul_fr (a b : GL (Fin r) E) (y : Frame X.Ψ r) : lact (a * b) y = lact a (lact b y) := by
  funext τ
  show ((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ =
    (a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

def image : Subgroup (RealGrp X) where
  carrier := {s | ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s}
  one_mem' := ⟨1, X.Γ.one_mem, by rw [lact_one_fr, frameOf_one]⟩
  mul_mem' := by
    rintro s t ⟨γ, hγ, e⟩ ⟨δ, hδ, f⟩
    exact ⟨γ * δ, X.Γ.mul_mem hγ hδ, by rw [lact_mul_fr, f, lact_frameOf X e]⟩
  inv_mem' := by
    rintro s ⟨γ, hγ, e⟩
    refine ⟨γ⁻¹, X.Γ.inv_mem hγ, ?_⟩
    have h := lact_frameOf X e s⁻¹
    rw [mul_inv_cancel, frameOf_one] at h
    rw [← h, ← lact_mul_fr, inv_mul_cancel, lact_one_fr]

def smallSet : Set (RealGrp X) :=
  {s | ∀ (τ : X.Ψ) (a b : Fin r), ‖(mat (frameOf X s) τ * (mat (baseFr X) τ)⁻¹) a b‖ < 2}

theorem isOpen_smallSet : IsOpen (smallSet X) := by
  unfold smallSet
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
  refine isOpen_lt (Continuous.norm ?_) continuous_const
  have h : Continuous fun s : RealGrp X =>
      mat (baseFr X) τ * ((s τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat (baseFr X) τ)⁻¹ :=
    (continuous_const.matrix_mul (Units.continuous_val.comp
      (continuous_subtype_val.comp (continuous_apply τ)))).matrix_mul continuous_const
  exact h.matrix_elem a b

theorem one_mem_smallSet : (1 : RealGrp X) ∈ smallSet X := by
  intro τ a b
  rw [frameOf_one, Matrix.mul_nonsing_inv _ (det_baseFr X τ).isUnit, Matrix.one_apply]
  split_ifs <;> simp

theorem finite_image_inter : ((image X : Set (RealGrp X)) ∩ smallSet X).Finite := by
  refine Set.Finite.of_finite_image (f := frameOf X) ?_ (frameOf_injective X).injOn
  refine (((GlobalTheory.LatFin.latFin (E := E)).2 r X 2).image fun γ => lact γ (baseFr X)).subset ?_
  rintro _ ⟨s, ⟨⟨γ, hγ, e⟩, hs⟩, rfl⟩
  refine ⟨γ, ⟨X.Γ_stab γ hγ, fun τ a b => ?_⟩, e⟩
  have h1 : (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (baseFr X) τ = mat (frameOf X s) τ := congrFun e τ
  have h2 := hs τ a b
  rw [← h1, Matrix.mul_nonsing_inv_cancel_right _ _ (det_baseFr X τ).isUnit] at h2
  exact h2.le

theorem exists_discrete_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∃ Λ : Subgroup (RealGrp X), (∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) ∧ ∃ W ∈ 𝓝 (1 : RealGrp X), ∀ w ∈ Λ, w ∈ W → w = 1 := by
  intro E _ _ _ r X
  refine ⟨image X, fun _ => Iff.rfl, smallSet X \ (((image X : Set (RealGrp X)) ∩ smallSet X) \ {1}), ?_, ?_⟩
  · exact ((isOpen_smallSet X).sdiff ((finite_image_inter X).subset Set.diff_subset).isClosed).mem_nhds
      ⟨one_mem_smallSet X, fun h => h.2 rfl⟩
  · intro w hw hW
    by_contra hne
    exact hW.2 ⟨⟨hw, hW.1⟩, hne⟩

end GlobalTheory.ArithImage

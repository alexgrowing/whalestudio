import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsAdaptedAt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LinPart

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Adapted

section Lin

variable {a b : ℕ}

noncomputable def linPart (f : (Fin a → ℂ) →ₗ[ℝ] (Fin b → ℂ)) : (Fin a → ℂ) →ₗ[ℂ] (Fin b → ℂ) :=
  _root_.UpperTheory.Reformulated.B.ComplexLinearPart.linPart f

def starR : (Fin a → ℂ) →ₗ[ℝ] (Fin a → ℂ) where
  toFun := star
  map_add' := star_add
  map_smul' r y := by funext i; simp

end Lin

section GS

end GS

section Emb

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end Emb

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F) (R : RiemLat E g Λ)

theorem vec_add (x y : Λ) : C.vec (x + y) = C.vec x + C.vec y := by
  funext τ i
  simp [LatEmb.vec]

def vecHom : Λ →+ (Ψ → Fin (j + j') → ℂ) := AddMonoidHom.mk' C.vec (vec_add C)

def imB : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z z' => (z ⬝ᵥ R.Hm *ᵥ star z').im)
    (fun z z' w => by simp [add_dotProduct])
    (fun r z w => by simp [smul_dotProduct])
    (fun z w w' => by simp [star_add, mulVec_add, dotProduct_add])
    (fun r z w => by simp [star_smul, mulVec_smul, dotProduct_smul])

def fmB : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ C.Fm
    (fun z z' w => by
      simp only [LatEmb.Fm, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp [mulVec_add, dotProduct_add, mul_add])
    (fun r z w => by
      simp only [LatEmb.Fm, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp [mulVec_smul, dotProduct_smul]
      ring)
    (fun z w w' => by
      simp only [LatEmb.Fm, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp [add_dotProduct, mul_add])
    (fun r z w => by
      simp only [LatEmb.Fm, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp [star_smul, smul_dotProduct]
      ring)

def actV (c : 𝓞 E) : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Ψ → Fin (j + j') → ℂ) where
  toFun y τ := F.σ τ c • y τ
  map_add' y y' := by funext τ i; simp [mul_add]
  map_smul' r y := by funext τ i; simp; ring

open Classical in

def perAt (τ : Ψ) : (Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
  C.perExt R ∘ₗ LinearMap.single ℝ (fun _ : Ψ => Fin (j + j') → ℂ) τ

def pPartL (τ : Ψ) : (Fin (j + j') → ℂ) →ₗ[ℂ] (Fin g → ℂ) := linPart (perAt C R τ)

def pBarL (τ : Ψ) : (Fin (j + j') → ℂ) →ₗ[ℂ] (Fin g → ℂ) := linPart (perAt C R τ ∘ₗ starR)

def bs (τ : Ψ) (u v : Fin (j + j') → ℂ) : ℂ := star v ⬝ᵥ C.sgr τ *ᵥ u

theorem exists_adapted_at (hF : R.form = F.form) (hS : R.HasSig F.σ j j') (τ : Ψ) :
    ∃ A : Matrix (Fin (j + j')) (Sg j j') ℂ, Aᴴ * C.sgr τ * A = sgI j j' ∧
      (∀ v : Fin j → ℂ, C.pPart R τ (A *ᵥ Sum.elim v 0) = 0) ∧
      (∀ v : Fin j' → ℂ, C.pBar R τ (A *ᵥ Sum.elim 0 v) = 0) :=
  by apply _root_.UpperTheory.Reformulated.B.Gwb8.exists_adapted_at <;> assumption

end Lat

theorem exists_isAdapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ]
    (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F)
    (R : RiemLat E g Λ), R.form = F.form → R.HasSig F.σ j j' → ∃ A, C.IsAdapted R A := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R hF hS
  choose A h1 h2 h3 using exists_adapted_at C R hF hS
  exact ⟨A, ⟨h1, h2, h3⟩⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Adapted

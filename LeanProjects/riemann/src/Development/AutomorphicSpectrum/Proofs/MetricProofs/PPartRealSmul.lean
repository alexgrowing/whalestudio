import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F) (R : RiemLat E g Λ) (τ : Ψ)

open Classical in
theorem pPart_add (y y' : Fin (j + j') → ℂ) : C.pPart R τ (y + y') = C.pPart R τ y + C.pPart R τ y' := by
  simp only [LatEmb.pPart, smul_add, Pi.single_add, map_add, smul_sub]
  abel

open Classical in
theorem pPart_real_smul (r : ℝ) (y : Fin (j + j') → ℂ) : C.pPart R τ (r • y) = (r : ℂ) • C.pPart R τ y := by
  have h1 : ∀ y : Fin (j + j') → ℂ, C.perExt R (Pi.single τ (r • y)) = (r : ℂ) • C.perExt R (Pi.single τ y) := by
    intro y
    rw [Pi.single_smul, map_smul]
    ext i; simp
  have h2 : Complex.I • r • y = r • Complex.I • y := smul_comm _ _ _
  simp only [LatEmb.pPart, h2, h1, smul_sub]
  simp only [smul_smul]
  congr 2 <;> ring_nf

open Classical in
theorem pPart_I_smul (y : Fin (j + j') → ℂ) : C.pPart R τ (Complex.I • y) = Complex.I • C.pPart R τ y := by
  have h : Complex.I • Complex.I • y = -y := by simp [smul_smul]
  have h2 : C.perExt R (Pi.single τ (-y)) = - C.perExt R (Pi.single τ y) := by
    rw [Pi.single_neg, map_neg]
  simp only [LatEmb.pPart, h, h2]
  ext k
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  linear_combination (1 / 2 * (C.perExt R (Pi.single τ (Complex.I • y))) k) * Complex.I_mul_I

def pPartL : (Fin (j + j') → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun := C.pPart R τ
  map_add' := pPart_add C R τ
  map_smul' a y := by
    have ha : a • y = a.re • y + a.im • Complex.I • y := by
      ext i; simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
      conv_lhs => rw [← Complex.re_add_im a]
      ring
    rw [ha, pPart_add, pPart_real_smul, pPart_real_smul, pPart_I_smul]
    simp only [RingHom.id_apply]
    conv_rhs => rw [← Complex.re_add_im a]
    rw [add_smul, mul_smul]

theorem pPart_elim (A : Matrix (Fin (j + j')) (Sg j j') ℂ) (v : Fin j → ℂ) (x : Fin j' → ℂ) :
    C.pPart R τ (A *ᵥ Sum.elim v x) =
      ∑ i, v i • C.pPart R τ (A *ᵥ Sum.elim (Pi.single i 1) 0) +
      ∑ b, x b • C.pPart R τ (A *ᵥ Sum.elim 0 (Pi.single b 1)) := by
  have hs : Sum.elim v x = ∑ i, v i • (Sum.elim (Pi.single i 1) 0 : Sg j j' → ℂ) +
      ∑ b, x b • (Sum.elim 0 (Pi.single b 1) : Sg j j' → ℂ) := by
    ext (i | b)
    · simp [Finset.sum_apply, Pi.single_apply]
    · simp [Finset.sum_apply, Pi.single_apply]
  change pPartL C R τ _ = ∑ i, v i • pPartL C R τ _ + ∑ b, x b • pPartL C R τ _
  rw [hs, Matrix.mulVec_add, map_add, Matrix.mulVec_sum, Matrix.mulVec_sum, map_sum, map_sum]
  simp [Matrix.mulVec_smul]

end

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

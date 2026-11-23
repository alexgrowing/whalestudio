import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PPartRealSmul
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F) (R : RiemLat E g Λ)

omit [IsCMField E] in

theorem embOf_coe (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : embOf s (a : E) = s a :=
  IsFractionRing.lift_algebraMap (intEmb_injective s) a

def mulPt (a : 𝓞 E) : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Ψ → Fin (j + j') → ℂ) where
  toFun y := fun τ => F.σ τ a • y τ
  map_add' y y' := by
    ext τ i
    simp [mul_add]
  map_smul' r y := by
    ext τ i
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul, RingHom.id_apply]
    ring

theorem vec_smul (a : 𝓞 E) (x : Λ) : C.vec (a • x) = mulPt (F := F) a (C.vec x) := by
  ext τ i
  simp [LatEmb.vec, mulPt, C.e_smul, embOf_coe]

def vecHom : Λ →+ (Ψ → Fin (j + j') → ℂ) where
  toFun := C.vec
  map_zero' := by
    ext τ i
    simp [LatEmb.vec]
  map_add' x y := by
    ext τ i
    simp [LatEmb.vec]

theorem vec_lam (k : Fin (2 * g)) : C.vec (C.lam k) = C.bas k := by
  ext τ i
  exact (C.bas_eq k τ i).symm

theorem perExt_bas (k : Fin (2 * g)) : C.perExt R (C.bas k) = R.P (C.lam k) := by
  simp [LatEmb.perExt]

theorem perExt_vec (x : Λ) : C.perExt R (C.vec x) = R.P x := by
  have h : ((C.perExt R).toAddMonoidHom.comp (vecHom C)).toIntLinearMap = R.P.toIntLinearMap := by
    refine C.lam.ext fun k => ?_
    change C.perExt R (C.vec (C.lam k)) = R.P (C.lam k)
    rw [vec_lam, perExt_bas]
  exact congrArg (fun f : Λ →ₗ[ℤ] (Fin g → ℂ) => f x) h

theorem perExt_mulPt (a : 𝓞 E) (y : Ψ → Fin (j + j') → ℂ) :
    C.perExt R (mulPt (F := F) a y) = R.B a (C.perExt R y) := by
  have h : (C.perExt R).comp (mulPt (F := F) a) = ((R.B a).restrictScalars ℝ).comp (C.perExt R) := by
    refine C.bas.ext fun k => ?_
    change C.perExt R (mulPt (F := F) a (C.bas k)) = R.B a (C.perExt R (C.bas k))
    rw [← vec_lam, ← vec_smul, perExt_vec, perExt_vec, R.act]
  exact congrArg (fun f : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ) => f y) h

open Classical in
theorem perExt_single_smul (a : 𝓞 E) (τ : Ψ) (y : Fin (j + j') → ℂ) :
    C.perExt R (Pi.single τ (F.σ τ a • y)) = R.B a (C.perExt R (Pi.single τ y)) := by
  rw [← perExt_mulPt]
  congr 1
  ext τ' i
  by_cases h : τ' = τ
  · subst h
    simp [mulPt]
  · simp [mulPt, Pi.single_eq_of_ne h]

theorem B_pPart (a : 𝓞 E) (τ : Ψ) (y : Fin (j + j') → ℂ) :
    R.B a (C.pPart R τ y) = F.σ τ a • C.pPart R τ y := by
  classical
  have h : C.pPart R τ (F.σ τ a • y) = F.σ τ a • C.pPart R τ y := (pPartL C R τ).map_smul _ _
  rw [← h]
  simp only [LatEmb.pPart, map_smul, map_sub, perExt_single_smul]
  rw [smul_comm Complex.I (F.σ τ a) y, perExt_single_smul]

theorem pPart_mem_eigSp (τ : Ψ) (y : Fin (j + j') → ℂ) : C.pPart R τ y ∈ eigSp R.B (F.σ τ) := by
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker]
  intro a
  simp [B_pPart]

end

theorem pPart_mem_eigSp_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (τ : Ψ) (y : Fin (j + j') → ℂ), C.pPart R τ y ∈ eigSp R.B (F.σ τ) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R τ y
  exact pPart_mem_eigSp C R τ y

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

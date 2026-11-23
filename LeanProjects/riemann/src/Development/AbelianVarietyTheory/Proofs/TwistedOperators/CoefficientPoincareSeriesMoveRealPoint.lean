import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesCoefficientsCuspidalIffOneSided
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TprodEqZeroOfKFinOff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultRealElt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveTopMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PoinConj

variable {D : D7}

theorem cmp_mul' (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (a b : GA D V) :
    cmp θ τ (a * b) = cmp θ τ a * cmp θ τ b := by
  have e : ∀ h : GA D V, infMat D.sp.cm.sig V.gram (θ τ) h = (infHom V h).1.map (θ τ) := fun _ => rfl
  show infMat D.sp.cm.sig V.gram (θ τ) (a * b) = infMat D.sp.cm.sig V.gram (θ τ) a * infMat D.sp.cm.sig V.gram (θ τ) b
  rw [e, e, e, map_mul, Units.val_mul, Matrix.map_mul]

theorem cmp_one' (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) : cmp θ τ (1 : GA D V) = 1 := by
  have e : ∀ h : GA D V, infMat D.sp.cm.sig V.gram (θ τ) h = (infHom V h).1.map (θ τ) := fun _ => rfl
  show infMat D.sp.cm.sig V.gram (θ τ) 1 = 1
  rw [e, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

variable {V : HSp D} {S : D.what₂.Tau → SPar}

theorem frConj_mem (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  rw [← M.fr_gram τ] at hg'
  change _ * _ * _ = _
  calc _ = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, mul_assoc]
    _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        rw [hg']; simp only [Matrix.conjTranspose_mul, mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp

theorem rep_one' (M : DSModel V S) (τ : D.what₂.Tau) (w : M.H τ) : M.rep τ 1 w = w := by
  have h1 : M.σ τ 1 = 1 := (M.ds τ).2.2.1.1.1
  rw [DSModel.rep, mul_one, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), h1]
  rfl

theorem rep_mul'' (M : DSModel V S) (τ : D.what₂.Tau) {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (w : M.H τ) :
    M.rep τ (g * g') w = M.rep τ g (M.rep τ g' w) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h := (M.ds τ).2.2.1.1.2 _ (frConj_mem M τ hg) _ (frConj_mem M τ hg')
  have e : M.fr τ * (g * g') * (M.fr τ)⁻¹ = (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * g' * (M.fr τ)⁻¹) := by
    simp only [mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  rw [DSModel.rep, e, h]
  rfl

theorem rep_inner' (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (a b : M.H τ) : ⟪M.rep τ g a, M.rep τ g b⟫_ℂ = ⟪a, b⟫_ℂ :=
  (⟨(M.rep τ g : M.H τ →ₗ[ℂ] M.H τ), fun v => (M.ds τ).2.2.1.2.1 _ (frConj_mem M τ hg) v⟩ :
    M.H τ →ₗᵢ[ℂ] M.H τ).inner_map_map a b

end GlobalTheory.PoinConj

namespace GlobalTheory.PoinConj

variable {D : D7}

theorem poin_conj : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v₀ : ∀ τ, M.H τ) (g₀ : GA D V), g₀ ∈ GinfC V → ∀ c g : GA D V, poin θ M K v₀ (g₀⁻¹ * c) v₀ (g * g₀) = poin θ M K (fun τ => M.rep τ (cmp θ τ g₀) (v₀ τ)) c (fun τ => M.rep τ (cmp θ τ g₀) (v₀ τ)) g := by
  intro D θ hθ V S M K v₀ g₀ hg₀ c g
  unfold poin
  congr 1
  funext γ
  have ez : g₀⁻¹ * c * γ * (g * g₀) = g₀⁻¹ * (c * γ * g) * g₀ := by group
  rw [ez]
  set z := c * γ * g
  have h1 : Lev.finE V g₀ = 1 := by
    simp only [Lev.finE, MonoidHom.comp_apply]
    rw [show finHom V g₀ = 1 from hg₀, map_one]
  have hf : Lev.finE V (g₀⁻¹ * z * g₀) = Lev.finE V z := by
    rw [map_mul, map_mul, map_inv, h1, inv_one, one_mul, mul_one]
  unfold coef
  rw [hf]
  split_ifs with hK
  · unfold coefR
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hU : ∀ x : GA D V, cmp θ τ x ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
      fun x => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ
    rw [cmp_mul', cmp_mul', rep_mul'' M τ (by rw [← cmp_mul']; exact hU _) (hU _),
      rep_mul'' M τ (hU _) (hU _), ← rep_inner' M τ (hU g₀), ← rep_mul'' M τ (hU g₀) (hU g₀⁻¹), ← cmp_mul',
      mul_inv_cancel, cmp_one', rep_one']
  · rfl

end GlobalTheory.PoinConj

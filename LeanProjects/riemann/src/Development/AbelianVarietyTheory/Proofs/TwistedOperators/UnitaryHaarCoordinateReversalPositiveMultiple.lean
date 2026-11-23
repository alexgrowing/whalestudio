import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Adapted
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbLEqEmbOptL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HaarRev

theorem haar_rev : ∀ (m : ℕ) (ε : Fin m → Bool), ∃ lam : ℝ, 0 < lam ∧
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Matrix (Fin m) (Fin m) ℂ → E),
    (Integrable (fun u : Formalism.REAL.UJ ε => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG ε) ↔
      Integrable (fun h : Formalism.REAL.UJ (fun a => ε a.rev) => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG (fun a => ε a.rev))) ∧
    ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG ε) =
      lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG (fun a => ε a.rev)) := by
  intro m ε
  set ε' : Fin m → Bool := fun a => ε a.rev with hε'
  have he : ∀ a, ε' a = ε a.rev := fun a => rfl
  let φ : Formalism.REAL.UJ ε ≃* Formalism.REAL.UJ ε' := GlobalTheory.ConjDS.rvU (GlobalTheory.ConjDS.sg_symm he)
  have hφ : Continuous φ := GlobalTheory.ConjDS.rvU_cont _
  have hφs : Continuous φ.symm := GlobalTheory.ConjDS.rvU_cont he
  haveI : ((Formalism.REAL.muG ε).map φ).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map _ φ hφ hφs
  set c := Measure.haarScalarFactor ((Formalism.REAL.muG ε).map φ) (Formalism.REAL.muG ε') with hc
  have hmap : (Formalism.REAL.muG ε).map φ = c • Formalism.REAL.muG ε' :=
    Measure.isMulLeftInvariant_eq_smul _ _
  have hc0 : c ≠ 0 := by
    intro h0
    have : (Formalism.REAL.muG ε).map φ = 0 := by rw [hmap, h0, zero_smul]
    exact (Measure.IsHaarMeasure.toIsOpenPosMeasure (μ := (Formalism.REAL.muG ε).map φ)).open_pos _ isOpen_univ
      Set.univ_nonempty (by rw [this]; rfl)
  let e : Formalism.REAL.UJ ε ≃ᵐ Formalism.REAL.UJ ε' :=
    { toEquiv := φ.toEquiv, measurable_toFun := hφ.measurable, measurable_invFun := hφs.measurable }
  have he' : ⇑e = ⇑φ := rfl
  refine ⟨(c : ℝ), by positivity, ?_⟩
  intro E _ _ F
  have hcomp : (fun u : Formalism.REAL.UJ ε => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) =
      (fun h : Formalism.REAL.UJ ε' => F (Formalism.MainNotions.S.umat h)) ∘ e := rfl
  constructor
  · rw [hcomp, ← integrable_map_equiv e, he', hmap, ENNReal.smul_def]
    exact integrable_smul_measure (by simpa using hc0) ENNReal.coe_ne_top
  · show ∫ u, F (Formalism.MainNotions.S.umat (e u)) ∂(Formalism.REAL.muG ε) = _
    rw [← integral_map_equiv e (fun h : Formalism.REAL.UJ ε' => F (Formalism.MainNotions.S.umat h)), he', hmap, integral_smul_nnreal_measure, NNReal.smul_def]

end GlobalTheory.HaarRev

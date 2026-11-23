import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensMu
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FourierSD

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

theorem selfDual_transport {V W : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [MeasurableSpace W] [BorelSpace W] (μ : Measure V) (χ : V → V → ℂ) (e : V ≃ₜ W)
    (he : ∀ x y, e (x + y) = e x + e y) (h : SelfDual μ χ) :
    SelfDual (μ.map e) (fun x y => χ (e.symm x) (e.symm y)) := by
  haveI := h.1
  let ea : V ≃+ W := AddEquiv.mk' e.toEquiv he
  let em : V ≃ᵐ W := e.toMeasurableEquiv
  have hm : μ.map e = μ.map em := rfl
  refine ⟨ea.isAddHaarMeasure_map μ e.continuous e.symm.continuous, fun Φ hc hs hI z => ?_⟩
  rw [hm] at hI ⊢
  have hT : ∀ y, ∫ x, Φ x * χ (e.symm x) (e.symm y) ∂(μ.map em) = ∫ x, Φ (e x) * χ x (e.symm y) ∂μ := by
    intro y
    rw [integral_map_equiv]
    simp [em]
  simp only [hT] at hI ⊢
  rw [integrable_map_equiv] at hI
  rw [integral_map_equiv]
  simp only [em, Function.comp_def, Homeomorph.toMeasurableEquiv_coe, Homeomorph.symm_apply_apply] at hI ⊢
  rw [h.2 (fun x => Φ (e x)) (hc.comp e.continuous) (hs.comp_homeomorph e) hI (e.symm z)]
  show Φ (e (-e.symm z)) = Φ (-z)
  rw [show e (-e.symm z) = -z from by
    have := ea.map_neg (e.symm z)
    change e (-e.symm z) = -e (e.symm z) at this
    rw [this, e.apply_symm_apply]]

section Beta

variable {D : D7} (X : HidaSetting D)

theorem tupCoord_symm_add (x y : EuclideanSpace ℝ (KapI X)) :
    (tupCoord X).symm (x + y) = (tupCoord X).symm x + (tupCoord X).symm y := by
  apply (tupCoord X).injective
  rw [tupCoord_add]
  simp

theorem betaI_add_left (x x' y : EuclideanSpace ℝ (KapI X)) : betaI X (x + x') y = betaI X x y + betaI X x' y := by
  simp only [betaI, tupCoord_symm_add, BR_add_leftP]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) +
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x') ((tupCoord X).symm y)) w =
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) w +
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x') ((tupCoord X).symm y) w from rfl,
    map_add, Complex.add_re]

theorem betaI_add_right (x y y' : EuclideanSpace ℝ (KapI X)) : betaI X x (y + y') = betaI X x y + betaI X x y' := by
  simp only [betaI, tupCoord_symm_add, BR_add_rightP]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) +
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y')) w =
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) w +
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y') w from rfl,
    map_add, Complex.add_re]

theorem continuous_betaI_left (y : EuclideanSpace ℝ (KapI X)) : Continuous fun x => betaI X x y :=
  continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding (v := w)).continuous.comp
      ((continuous_apply w).comp ((continuous_BR_leftP X _).comp (tupCoord X).symm.continuous)))

theorem continuous_betaI_right (x : EuclideanSpace ℝ (KapI X)) : Continuous fun y => betaI X x y :=
  continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding (v := w)).continuous.comp
      ((continuous_apply w).comp ((continuous_BR_rightP X _).comp (tupCoord X).symm.continuous)))

theorem betaI_smul_left (r : ℝ) (x y : EuclideanSpace ℝ (KapI X)) : betaI X (r • x) y = r * betaI X x y :=
  map_real_smul (AddMonoidHom.mk' (fun x => betaI X x y) fun a b => betaI_add_left X a b y)
    (continuous_betaI_left X y) r x

theorem betaI_smul_right (r : ℝ) (x y : EuclideanSpace ℝ (KapI X)) : betaI X x (r • y) = r * betaI X x y :=
  map_real_smul (AddMonoidHom.mk' (fun y => betaI X x y) fun a b => betaI_add_right X x a b)
    (continuous_betaI_right X x) r y

def betaL : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (betaI X) (betaI_add_left X) (fun r x y => betaI_smul_left X r x y) (betaI_add_right X)
    (fun r x y => betaI_smul_right X r x y)

open Classical in
theorem betaI_expand (x y : EuclideanSpace ℝ (KapI X)) : betaI X x y = ∑ i, ∑ j, x i * matI X i j * y j := by
  have h : betaI X x y = betaL X x y := rfl
  rw [h]
  conv_lhs => rw [← (EuclideanSpace.basisFun (KapI X) ℝ).sum_repr x, ← (EuclideanSpace.basisFun (KapI X) ℝ).sum_repr y]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [betaL, LinearMap.mk₂_apply, matI]
  ring

end Beta

end PI.AprimeInfW

import Formalism.HermitianCurvature.CompositeFormulaOfDensities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne

open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem measurable_of_continuousOn_zero {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {s : Set X} (hs : MeasurableSet s) {f : X → ℂ} (hf : ContinuousOn f s) (h0 : ∀ x ∉ s, f x = 0) : Measurable f := by
  classical
  have e : f = s.piecewise f (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ s <;> simp [Set.piecewise, hx, h0]
  rw [e]
  exact hf.measurable_piecewise continuousOn_const hs

example (k r : ℕ) : OpensMeasurableSpace (Cf r 0 × Mt k r) := inferInstance

section Meas

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem radSp_continuousOn (Φ : RadSp k r z z' π π') :
    ContinuousOn (fun x : (Fin r → ℂ) × Mx k r => (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2) (DomR k r z z') := by
  obtain ⟨-, hs, -⟩ := Φ.2
  intro x₀ hx₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs x₀ hx₀
  have hFc : ContinuousAt F x₀ := hF.continuousOn.continuousAt (hU.mem_nhds hxU)
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hΦ x₀ hxU hx₀.2.1)
  filter_upwards [inter_mem_nhdsWithin (DomR k r z z') (hU.mem_nhds hxU)] with x hx
  exact hΦ x hx.2 hx.1.2.1

theorem radSp_zero_off (Φ : RadSp k r z z' π π') {x : (Fin r → ℂ) × Mx k r} (hx : x ∉ DomR k r z z') :
    (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = 0 :=
  Φ.2.1 x hx

def glueMap (c : Fin r → ℂ) (q : Cf r 0 × Mt k r) : (Fin r → ℂ) × Mx k r := (glue 0 c q.1, Matrix.of q.2)

theorem glueMap_continuous (c : Fin r → ℂ) : Continuous (glueMap (k := k) c) := by
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun l => ?_
    have : (fun q : Cf r 0 × Mt k r => glue 0 c q.1 l) = fun q => q.1 ⟨l, Nat.zero_le _⟩ := by
      funext q
      simp [glue]
    rw [this]
    exact (continuous_apply _).comp continuous_fst
  · exact continuous_snd

theorem DomR_eq : DomR k r z z' = P.Qx5.OpR k r z z' ∩ (Prod.snd ⁻¹' Glev k r (Fin.last r)) := by
  ext x
  simp only [DomR, P.Qx5.OpR, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
  tauto

theorem measurableSet_glueMap_DomR (c : Fin r → ℂ) :
    MeasurableSet (glueMap (k := k) c ⁻¹' DomR k r z z') := by
  rw [DomR_eq, Set.preimage_inter]
  exact ((P.Qx5.isOpen_OpR k r z z').preimage (glueMap_continuous c)).measurableSet.inter
    (((P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage (glueMap_continuous c)).measurableSet

theorem pair_measurable (c : Fin r → ℂ) (Φ Ψ : RadSp k r z z' π π') :
    Measurable (fun q : Cf r 0 × Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue 0 c q.1) (Matrix.of q.2))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (glue 0 c q.1) (Matrix.of q.2))) := by
  have hmaps : Set.MapsTo (glueMap (k := k) c) (glueMap (k := k) c ⁻¹' DomR k r z z') (DomR k r z z') :=
    fun q hq => hq
  have hΦc := (radSp_continuousOn Φ).comp (glueMap_continuous c).continuousOn hmaps
  have hΨc := (radSp_continuousOn Ψ).comp (glueMap_continuous c).continuousOn hmaps
  refine measurable_of_continuousOn_zero (measurableSet_glueMap_DomR c)
    ((P.B6.hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn (hΦc.prodMk hΨc)) ?_
  intro q hq
  have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) (glue 0 c q.1) (Matrix.of q.2) = 0 := radSp_zero_off Φ hq
  show B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue 0 c q.1) (Matrix.of q.2)) _ = 0
  rw [h0, P.B6.hilbert_schmidt_inner_basis_sum]
  simp

end Meas

theorem topDensMeasAll : TopDensMeasAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' μ L st K w u v _ _ c
  refine Measurable.stronglyMeasurable ?_
  unfold topDens
  exact Finset.measurable_sum _ fun e _ => pair_measurable c _ _

end Formalism.FourierDecayAlt.P5

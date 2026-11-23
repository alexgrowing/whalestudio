import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.RestrProdSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensAll

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology
open scoped TensorProduct

namespace RestrictedProductFiber

theorem finite_on_compacts {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [OpensMeasurableSpace V] [LocallyCompactSpace V] [T2Space V] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure V) (f : V → Y) (ι : X → Y) (U : Set V) (hU : IsOpen U)
    (ν : Measure X) (B : Set X) (fib : X → Measure V) (h : IsFibreFamily μ f ι U ν B fib)
    (b : X) (hb : b ∈ B) (hC : IsClosed (f ⁻¹' {ι b})) (hCU : f ⁻¹' {ι b} ⊆ U) :
    IsFiniteMeasureOnCompacts (fib b) := by
  refine ⟨fun K hK => ?_⟩
  have hK' : IsCompact (K ∩ f ⁻¹' {ι b}) := hK.inter_right hC
  obtain ⟨φ, h1, hφc, hφU, _h01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK' hU (Set.inter_subset_right.trans hCU)
  have hint : Integrable φ (fib b) :=
    (h.2.2 φ φ.continuous hφc hφU).1 b hb
  have hnull : fib b (f ⁻¹' {ι b} ∩ U)ᶜ = 0 := h.1 b
  have hM : fib b (K ∩ f ⁻¹' {ι b}) ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂(fib b) := by
    have hm : AEMeasurable (fun x => ENNReal.ofReal (φ x)) (fib b) :=
      (ENNReal.continuous_ofReal.comp φ.continuous).measurable.aemeasurable
    calc fib b (K ∩ f ⁻¹' {ι b}) ≤ fib b {x | 1 ≤ ENNReal.ofReal (φ x)} := by
          refine measure_mono fun x hx => ?_
          simp only [Set.mem_ofPred_eq, h1 hx, Pi.one_apply, ENNReal.ofReal_one, le_refl]
      _ = 1 * fib b {x | 1 ≤ ENNReal.ofReal (φ x)} := (one_mul _).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂(fib b) := mul_meas_ge_le_lintegral₀ hm 1
  calc fib b K ≤ fib b ((K ∩ f ⁻¹' {ι b}) ∪ (f ⁻¹' {ι b} ∩ U)ᶜ) := by
        refine measure_mono fun x hx => ?_
        by_cases hx2 : x ∈ f ⁻¹' {ι b} ∩ U
        · exact Or.inl ⟨hx, hx2.1⟩
        · exact Or.inr hx2
    _ ≤ fib b (K ∩ f ⁻¹' {ι b}) + fib b (f ⁻¹' {ι b} ∩ U)ᶜ := measure_union_le _ _
    _ = fib b (K ∩ f ⁻¹' {ι b}) := by rw [hnull, add_zero]
    _ < ⊤ := lt_of_le_of_lt hM hint.lintegral_lt_top

theorem fib_props {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] (hTF : TensFacts F E σ M J a R)
    (T : Matrix (Fin a) (Fin a) E) (hT : ∀ i j, σ (T j i) = T i j) (hdet : T.det ≠ 0)
    (μ : Measure (Fin a → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ a))
    (fib : HermR R σ a → Measure (Fin a → Fin M → R ⊗[F] E))
    (h : IsFibreFamily μ (gramR R σ J) Subtype.val
      {X | LinearIndependent (R ⊗[F] E) X} ν Set.univ fib) :
    SigmaFinite (fib (hermOf R σ T hT)) ∧
    ∀ Φ : (Fin a → Fin M → R ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable Φ (fib (hermOf R σ T hT)) := by
  obtain ⟨h1, h2, h3, _h4, h5, _h6, h7⟩ := hTF
  have : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have : T2Space (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → R ⊗[F] E))
  have hC : IsClosed (gramR R σ J ⁻¹' {((hermOf R σ T hT : HermR R σ a) :
      Matrix (Fin a) (Fin a) (R ⊗[F] E))}) := isClosed_singleton.preimage h5
  have hCU : gramR R σ J ⁻¹' {((hermOf R σ T hT : HermR R σ a) :
      Matrix (Fin a) (Fin a) (R ⊗[F] E))} ⊆ {X | LinearIndependent (R ⊗[F] E) X} := by
    intro X hX
    have hX' : gramR R σ J X = ((hermOf R σ T hT : HermR R σ a) :
        Matrix (Fin a) (Fin a) (R ⊗[F] E)) := hX
    have hu := isUnit_det_hermOf R σ T hT hdet
    rw [← hX'] at hu
    exact linIndep_of_isUnit_det R σ J X hu
  have hfin := finite_on_compacts μ (gramR R σ J) Subtype.val _ h7 ν Set.univ fib h
    (hermOf R σ T hT) (Set.mem_univ _) hC hCU
  have : SigmaCompactSpace (Fin a → Fin M → R ⊗[F] E) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  exact ⟨inferInstance, fun Φ hc hs => hc.integrable_of_hasCompactSupport hs⟩

end RestrictedProductFiber

theorem rpFib_holds : RPFib := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨hI, hV⟩ := tensAll_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  refine ⟨fun μ ν fib h => RestrictedProductFiber.fib_props σ J a (Ainf F) hI _ hT hdet μ ν fib h,
    fun v μ ν fib h => RestrictedProductFiber.fib_props σ J a (Fv F v) (hV v) _ hT hdet μ ν fib h⟩

end PI.VolStabSW

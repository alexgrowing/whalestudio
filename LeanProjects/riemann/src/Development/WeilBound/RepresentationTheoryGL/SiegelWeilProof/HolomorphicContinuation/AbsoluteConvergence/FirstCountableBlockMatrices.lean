import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BasisA

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.BasisPf

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

theorem flatEq_of (hI : Iwa) : FlatEq := by
  intro m n ε c t p q e sL ρ hL Q Q' hQ y
  obtain ⟨pp, k, hp, hk, rfl⟩ := hI n y
  rw [hL.law Q pp k hp, hL.law Q' pp k hp, hQ k hk]

variable {m n : ℕ}

def secK (sL : PX m n →ₗ[ℂ] (GR n → ℂ)) (hc : ∀ Q, Continuous (sL Q)) : PX m n →ₗ[ℂ] C(KR n, ℂ) where
  toFun Q := ⟨fun k => sL Q (k : GR n), (hc Q).comp continuous_subtype_val⟩
  map_add' Q Q' := by ext k; simp
  map_smul' a Q := by ext k; simp

theorem secK_apply (sL : PX m n →ₗ[ℂ] (GR n → ℂ)) (hc : ∀ Q, Continuous (sL Q)) (Q : PX m n) (k : KR n) :
    secK sL hc Q k = sL Q (k : GR n) := rfl

theorem bij_toK : Function.Bijective (toK (n := n)) := by
  constructor
  · intro u v h
    apply Subtype.ext
    have := congrArg (fun k : KR n => ((k : GR n) : GL (Fin n ⊕ Fin n) ℂ).1) h
    exact this
  · intro k
    refine ⟨⟨mR (k : GR n), ⟨k.2.2, k.2.1⟩⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext; apply Units.ext; rfl

instance t2KR : T2Space (KR n) := inferInstance

def homeoK : uSet n ≃ₜ KR n :=
  haveI : CompactSpace (uSet n) := isCompact_iff_compactSpace.1 (isCompact_uSet n)
  continuous_toK.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ bij_toK)

instance firstCountableBlockMatrices : FirstCountableTopology (M2 n) := by
  show FirstCountableTopology (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ); infer_instance

instance fcKR : FirstCountableTopology (KR n) :=
  (homeoK (n := n)).symm.isInducing.firstCountableTopology

section Op

variable [MeasurableSpace (KR n)] [BorelSpace (KR n)] (ν : Measure (KR n)) [IsFiniteMeasure ν]

theorem integrable_of_cont {f : KR n → ℂ} (hf : Continuous f) : Integrable f ν :=
  integrableOn_univ.1 (hf.continuousOn.integrableOn_compact isCompact_univ)

def piFun (κ : C(KR n, ℂ)) (h : C(KR n, ℂ)) : C(KR n, ℂ) :=
  ⟨fun k' => ∫ k, κ k * h (k' * k) ∂ν, by
    refine continuous_of_dominated (bound := fun _ => ‖κ‖ * ‖h‖) (fun k' => ?_) (fun k' => ?_)
      (integrable_const _) (Filter.Eventually.of_forall fun k => ?_)
    · exact (κ.continuous.mul (h.continuous.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun k => ?_
      rw [norm_mul]
      exact mul_le_mul (κ.norm_coe_le_norm k) (h.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
    exact continuous_const.mul (h.continuous.comp (continuous_id.mul continuous_const))⟩

theorem piFun_apply (κ h : C(KR n, ℂ)) (k' : KR n) : piFun ν κ h k' = ∫ k, κ k * h (k' * k) ∂ν := rfl

def piL (κ : C(KR n, ℂ)) : C(KR n, ℂ) →L[ℂ] C(KR n, ℂ) :=
  LinearMap.mkContinuous
    { toFun := piFun ν κ
      map_add' := fun h h' => by
        ext k'
        simp only [piFun_apply, ContinuousMap.add_apply, mul_add]
        exact integral_add (integrable_of_cont ν (κ.continuous.mul (h.continuous.comp (continuous_const.mul continuous_id))))
          (integrable_of_cont ν (κ.continuous.mul (h'.continuous.comp (continuous_const.mul continuous_id))))
      map_smul' := fun a h => by
        ext k'
        simp only [piFun_apply, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext k; ring }
    (‖κ‖ * ν.real univ) fun h => by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun k' => ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, piFun_apply]
      calc ‖∫ k, κ k * h (k' * k) ∂ν‖ ≤ (‖κ‖ * ‖h‖) * ν.real univ := by
            refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k => ?_)
            rw [norm_mul]
            exact mul_le_mul (κ.norm_coe_le_norm k) (h.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
        _ = ‖κ‖ * ν.real univ * ‖h‖ := by ring

theorem piL_apply (κ h : C(KR n, ℂ)) (k' : KR n) : piL ν κ h k' = ∫ k, κ k * h (k' * k) ∂ν := rfl

end Op

end PositivityTheory.Rg.Sw.AbsSt.BasisPf

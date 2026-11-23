import Mathlib
import Formalism.PeriodIntegrals.LocJacTyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMulAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ContinuousTrESymm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensFibV

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem oev_one : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  unfold OEv
  rw [SetLike.mem_coe]
  apply Submodule.subset_span
  refine ⟨1, Set.mem_univ _, ?_⟩
  first
    | exact map_one _
    | simp

theorem sc_mul (t : Fv F v) (x : Fv F v ⊗[F] E) : sc (E := E) v t * x = t • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sc, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => rw [mul_add, smul_add, hx, hy]

theorem oev_mul {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  unfold OEv at hx hy ⊢
  rw [SetLike.mem_coe] at hx hy ⊢
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨a', -, rfl⟩ := ha
      obtain ⟨b', -, rfl⟩ := hb
      apply Submodule.subset_span
      refine ⟨a' * b', Set.mem_univ _, ?_⟩
      first
        | exact map_mul _ _ _
        | simp
    | zero => simp
    | add y z _ _ hy hz =>
      rw [mul_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      first
        | rw [mul_smul_comm]
        | rw [← algebraMap_smul (Fv F v) c y, mul_smul_comm, algebraMap_smul]
      exact Submodule.smul_mem _ c hy
  | zero => simp
  | add x z _ _ hx hz =>
    rw [add_mul]
    exact Submodule.add_mem _ hx hz
  | smul c x _ hx =>
    first
      | rw [smul_mul_assoc]
      | rw [← algebraMap_smul (Fv F v) c x, smul_mul_assoc, algebraMap_smul]
    exact Submodule.smul_mem _ c hx

theorem sigR_smul (σ : E →ₐ[F] E) (c : Fv F v) (x : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private theorem sigR_smulO_lemma (σ : E →ₐ[F] E) (c : v.adicCompletionIntegers F)
    (x : Fv F v ⊗[F] E) : sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  first
    | rw [← algebraMap_smul (Fv F v) c x, sigR_smul, algebraMap_smul]
    | (induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [sigR, TensorProduct.smul_tmul']
        | add y z hy hz => simp only [smul_add, map_add, hy, hz])

theorem oev_sigR (σ : E →ₐ[F] E) {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) :
    sigR (Fv F v) σ x ∈ OEv (E := E) v := by
  unfold OEv at hx ⊢
  rw [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a', -, rfl⟩ := ha
    apply Submodule.subset_span
    first
      | exact ⟨NumberField.RingOfIntegers.mapRingHom (σ : E →+* E) a', Set.mem_univ _,
          by simp [sigR, inclR]⟩
      | exact ⟨⟨σ a', (a'.isIntegral_coe.map (σ : E →+* E).toIntAlgHom)⟩, Set.mem_univ _,
          by simp [sigR, inclR]⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [sigR_smulO_lemma]
    exact Submodule.smul_mem _ c hx

theorem integer_ring_topology : OTop (E := E) v :=
  ⟨Sd.isCompact_oev v, Sd.isOpen_oev v, oev_one v, fun _ hx _ hy => oev_mul v hx hy,
    fun _ hx _ hy => Sd.oev_add v hx hy, fun _ hx => Sd.oev_neg v hx,
    fun t ht x hx => by rw [sc_mul]; exact Sd.oev_smul v ht hx,
    fun σ _ hx => oev_sigR v σ hx⟩

theorem ring_topology_instances : RTop (E := E) v :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end PI.UnitaryGroupMassFormula.LocJacTyp

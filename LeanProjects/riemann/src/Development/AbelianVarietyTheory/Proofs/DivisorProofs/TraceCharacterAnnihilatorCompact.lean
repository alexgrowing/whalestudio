import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct GlobalTheory.VacAny
open Matrix

namespace GlobalTheory.TraceAnnCompact

theorem exists_bound {K : Type} [NormedField K] (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) {V : Set K} (hV : V ∈ nhds (0 : K)) :
    ∃ C : ℝ, ∀ x : K, (∀ a ∈ V, ψ (a * x) = 1) → ‖x‖ ≤ C := by
  obtain ⟨y, hy⟩ := AddChar.ne_one_iff.1 hψ
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨‖y‖ / ε, fun x hx => ?_⟩
  by_contra hlt
  push Not at hlt
  have hx0 : 0 < ‖x‖ := lt_of_le_of_lt (div_nonneg (norm_nonneg _) hε.le) hlt
  have hx1 : x ≠ 0 := norm_pos_iff.1 hx0
  have hmem : y / x ∈ V := by
    apply hb
    rw [mem_ball_zero_iff, norm_div, div_lt_iff₀ hx0]
    rw [div_lt_iff₀ hε] at hlt
    linarith [mul_comm ε ‖x‖]
  have h := hx _ hmem
  rw [div_mul_cancel₀ _ hx1] at h
  exact hy h

theorem isCompact_ann {K A ι : Type} [NormedField K] [ProperSpace K] [AddCommGroup A] [Module K A]
    [TopologicalSpace A] [IsModuleTopology K A] [Fintype ι] (b : Module.Basis ι K A) (c : ι → A)
    (B : A →ₗ[K] A →ₗ[K] K) (hB : ∀ i l, B (c i) l = b.repr l i) (ψ : AddChar K ℂ) (hc : Continuous ψ)
    (hψ : ψ ≠ 1) {U : Set A} (hU : U ∈ nhds (0 : A)) :
    IsCompact {l : A | ∀ t ∈ U, ψ (B t l) = 1} := by
  haveI : ContinuousAdd A := IsModuleTopology.toContinuousAdd K A
  have hclosed : IsClosed {l : A | ∀ t ∈ U, ψ (B t l) = 1} := by
    have : {l : A | ∀ t ∈ U, ψ (B t l) = 1} = ⋂ t ∈ U, {l : A | ψ (B t l) = 1} := by
      ext l; simp
    rw [this]
    exact isClosed_biInter fun t _ =>
      isClosed_eq (hc.comp (IsModuleTopology.continuous_of_linearMap (B t))) continuous_const
  have hV : ∀ i, (fun a : K => a • c i) ⁻¹' U ∈ nhds (0 : K) := fun i => by
    have h : Continuous fun a : K => a • c i := continuous_id.smul continuous_const
    exact h.continuousAt.preimage_mem_nhds (by simpa using hU)
  choose C hC using fun i => exists_bound ψ hψ (hV i)
  have hK : IsCompact (b.equivFun.symm '' Set.univ.pi fun i => Metric.closedBall (0 : K) (C i)) :=
    (isCompact_univ_pi fun i => isCompact_closedBall _ _).image
      (IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap)
  refine hK.of_isClosed_subset hclosed fun l hl => ⟨b.equivFun l, fun i _ => ?_, by simp⟩
  rw [mem_closedBall_zero_iff]
  refine hC i _ fun a ha => ?_
  have h := hl _ ha
  rwa [map_smul, LinearMap.smul_apply, hB, smul_eq_mul] at h

theorem trace_one_tmul {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem trace_traceDual_mul {F E ι : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    [Algebra.IsSeparable F E] [Fintype ι] [DecidableEq ι] (R : Type) [CommRing R] [Algebra F R]
    (b : Module.Basis ι F E) (i : ι) (l : R ⊗[F] E) :
    Algebra.traceForm R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] b.traceDual i) l =
      (Algebra.TensorProduct.basis R b).repr l i := by
  have : Algebra.traceForm R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] b.traceDual i) = (Algebra.TensorProduct.basis R b).coord i := by
    refine (Algebra.TensorProduct.basis R b).ext fun j => ?_
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Algebra.TensorProduct.basis_apply, Algebra.traceForm_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul, Module.Basis.trace_traceDual_mul,
      Finsupp.single_apply]
    split_ifs <;> simp
  rw [this, Module.Basis.coord_apply]

theorem isCompact_trace_ann : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ U ∈ nhds (0 : Fv F v ⊗[F] E),
      IsCompact {l : Fv F v ⊗[F] E | ∀ t ∈ U, ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * l)) = 1} := by
  intro F E _ _ _ _ _ v ψ hc hψ U hU
  classical
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  let b := Module.finBasis F E
  exact isCompact_ann (Algebra.TensorProduct.basis (Fv F v) b) (fun i => (1 : Fv F v) ⊗ₜ[F] b.traceDual i)
    (Algebra.traceForm (Fv F v) (Fv F v ⊗[F] E)) (trace_traceDual_mul (Fv F v) b) ψ hc hψ hU

end GlobalTheory.TraceAnnCompact

import Mathlib
import Formalism.PeriodIntegrals.SSAscent
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.TraceNilStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.IsSemisimpleOfIsSSRep

namespace PI.SSAscent.UnitaryGroupMassFormula

open PI.SSAscent
open Matrix

private theorem isSemisimpleModule_self_of_vectors {k : Type} [Field k] {a : ℕ}
    (A : Subalgebra k (Matrix (Fin a) (Fin a) k)) [IsSemisimpleModule A (Fin a → k)] :
    IsSemisimpleModule A A := by
  refine IsSemisimpleModule.of_injective
    (LinearMap.pi fun j : Fin a => LinearMap.toSpanSingleton A (Fin a → k) (Pi.single j 1)) ?_
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  apply Subtype.ext
  ext i j
  have h1 := congrFun (congrFun hx j) i
  simp only [LinearMap.pi_apply, LinearMap.toSpanSingleton_apply, smul_sub_def,
    Pi.zero_apply] at h1
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h1

private theorem eq_zero_of_trace_mul_eq_zero' {K : Type} [Field K] [CharZero K] {a : ℕ}
    (hT : TraceNilStep) (A : Subalgebra K (Matrix (Fin a) (Fin a) K))
    [IsSemisimpleModule A A] (x : A)
    (hx : ∀ y ∈ A, Matrix.trace ((x : Matrix (Fin a) (Fin a) K) * y) = 0) : x = 0 := by
  have hnil : ∀ z : A, (∀ y ∈ A, Matrix.trace ((z : Matrix (Fin a) (Fin a) K) * y) = 0) →
      IsNilpotent z := by
    intro z hz
    have hM : IsNilpotent (z : Matrix (Fin a) (Fin a) K) := by
      refine hT K a _ fun m hm => ?_
      cases m with
      | zero => exact absurd hm (lt_irrefl 0)
      | succ m =>
        rw [pow_succ']
        exact hz _ (pow_mem z.2 m)
    obtain ⟨n, hn⟩ := hM
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hspan : ∀ e ∈ Ideal.span ({x} : Set A), IsNilpotent e := by
    intro e he
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp he
    apply hnil
    intro y hy
    have hc : ((c * x : A) : Matrix (Fin a) (Fin a) K) =
        (c : Matrix (Fin a) (Fin a) K) * (x : Matrix (Fin a) (Fin a) K) := rfl
    rw [hc, mul_assoc, Matrix.trace_mul_comm, mul_assoc]
    exact hx _ (A.mul_mem hy c.2)
  obtain ⟨L, hc⟩ := exists_isCompl (Ideal.span ({x} : Set A))
  have h1 : (1 : A) ∈ Ideal.span ({x} : Set A) ⊔ L := by
    rw [hc.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp h1
  have hdis := Submodule.disjoint_def.mp hc.disjoint
  have hee : e * e = e := by
    have h2 : e - e * e ∈ Ideal.span ({x} : Set A) := sub_mem he (Ideal.mul_mem_left _ e he)
    have h3 : e - e * e ∈ L := by
      have h4 : e - e * e = e * f := by
        calc e - e * e = e * (e + f) - e * e := by rw [hef, mul_one]
          _ = e * f := by rw [mul_add]; abel
      rw [h4]
      exact Ideal.mul_mem_left _ e hf
    exact (sub_eq_zero.mp (hdis _ h2 h3)).symm
  have he0 : e = 0 := by
    obtain ⟨n, hn⟩ := hspan e he
    have key : ∀ m : ℕ, e ^ (m + 1) = e := by
      intro m
      induction m with
      | zero => rw [zero_add, pow_one]
      | succ m ih => rw [pow_succ, ih, hee]
    rw [← key n, pow_succ, hn, zero_mul]
  have hxf : x = x * f := by
    calc x = x * (e + f) := by rw [hef, mul_one]
      _ = x * f := by rw [he0, zero_add]
  refine hdis x (Ideal.subset_span (Set.mem_singleton x)) ?_
  rw [hxf]
  exact Ideal.mul_mem_left _ x hf

theorem downStep_of (hT : TraceNilStep) : DownStep := by
  intro K _ _ Γ _ a ρ hρ
  haveI := isSemisimple_of_isSSRep ρ hρ
  haveI := isSemisimpleModule_self_of_vectors (imAlg ρ)
  intro x hx hxy
  have h := eq_zero_of_trace_mul_eq_zero' hT (imAlg ρ) ⟨x, hx⟩ hxy
  simpa using congrArg Subtype.val h

private theorem isNilpotent_of_mem_jacobson_of_artinian {R : Type} [Ring R] [IsArtinianRing R] (x : R)
    (hx : x ∈ Ring.jacobson R) : IsNilpotent x := by
  obtain ⟨n, hn⟩ := IsSemiprimaryRing.isNilpotent (R := R)
  refine ⟨n, ?_⟩
  have h : x ^ n ∈ Ring.jacobson R ^ n := Submodule.pow_mem_pow (Ring.jacobson R) hx n
  rw [hn] at h
  simpa using h

private theorem isSemisimpleRing_of_trNondeg {k : Type} [Field k] {a : ℕ}
    (A : Subalgebra k (Matrix (Fin a) (Fin a) k)) (h : TrNondeg A) :
    IsSemisimpleRing A := by
  haveI : Module.Finite k A := Module.Finite.of_injective (A.val.toLinearMap) Subtype.val_injective
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  refine IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr ?_
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  have hx0 : (x : Matrix (Fin a) (Fin a) k) = 0 := by
    refine h x x.2 fun y hy => ?_
    have hyx : ((⟨y, hy⟩ : A) * x) ∈ Ring.jacobson A := Ideal.mul_mem_left _ _ hx
    have hn : IsNilpotent (((⟨y, hy⟩ : A) * x : A) : Matrix (Fin a) (Fin a) k) :=
      (isNilpotent_of_mem_jacobson_of_artinian _ hyx).map A.val
    rw [Matrix.trace_mul_comm]
    exact (Matrix.isNilpotent_trace_of_isNilpotent hn).eq_zero
  exact Subtype.ext hx0

theorem semisimpleOfTraceFormNondegenerate : UpStep := by
  intro k _ Γ _ a ρ h
  apply isSSRep_of_isSemisimple
  haveI := isSemisimpleRing_of_trNondeg (imAlg ρ) h
  infer_instance

end PI.SSAscent.UnitaryGroupMassFormula

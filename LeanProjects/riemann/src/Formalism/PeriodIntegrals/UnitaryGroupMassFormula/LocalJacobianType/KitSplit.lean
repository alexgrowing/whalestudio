import Mathlib
import Formalism.PeriodIntegrals.LocJacTyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.RingTopologyInstances
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.EpSelfDualSplit
import Formalism.PeriodIntegrals.SplitIntLoc
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitIntLoc

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

structure SD where
  e : Fv F v ⊗[F] E
  he : IsIdempotentElem e
  h0 : e ≠ 0
  h1 : e ≠ 1
  hr : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2
  hσ : sigR (Fv F v) σ e = 1 - e

namespace SD

variable {σ v} (D : SD σ v)

def p (i : Fin 2) : (Fv F v ⊗[F] E) →ₐ[Fv F v] Fv F v := PI.LocDualGen.EpS.pr D.hr D.e D.he D.h0 D.h1 i

theorem decomp (z : Fv F v ⊗[F] E) : z = D.p 0 z • D.e + D.p 1 z • (1 - D.e) :=
  PI.LocDualGen.EpS.decomp D.hr D.e D.he D.h0 D.h1 z

theorem p_pair (s t : Fv F v) : D.p 0 (s • D.e + t • (1 - D.e)) = s ∧ D.p 1 (s • D.e + t • (1 - D.e)) = t :=
  PI.LocDualGen.EpS.repr_pair D.hr D.e D.he D.h0 D.h1 s t

theorem ext {z w : Fv F v ⊗[F] E} (h0 : D.p 0 z = D.p 0 w) (h1 : D.p 1 z = D.p 1 w) : z = w := by
  rw [D.decomp z, D.decomp w, h0, h1]

theorem p_e : D.p 0 D.e = 1 ∧ D.p 1 D.e = 0 := PI.LocDualGen.EpS.pr_e D.hr D.e D.he D.h0 D.h1

theorem p_f : D.p 0 (1 - D.e) = 0 ∧ D.p 1 (1 - D.e) = 1 := PI.LocDualGen.EpS.pr_f D.hr D.e D.he D.h0 D.h1

theorem p_sc (i : Fin 2) (t : Fv F v) : D.p i (sc (E := E) v t) = t := by
  have : sc (E := E) v t = algebraMap (Fv F v) (Fv F v ⊗[F] E) t := rfl
  rw [this, AlgHom.commutes]; rfl

theorem p_sig (z : Fv F v ⊗[F] E) :
    D.p 0 (sigR (Fv F v) σ z) = D.p 1 z ∧ D.p 1 (sigR (Fv F v) σ z) = D.p 0 z := by
  have h : sigR (Fv F v) σ z = D.p 1 z • D.e + D.p 0 z • (1 - D.e) := by
    conv_lhs => rw [D.decomp z]
    rw [map_add, sigR_smul, sigR_smul, map_sub, map_one, D.hσ, sub_sub_cancel, add_comm]
  rw [h]
  exact D.p_pair _ _

theorem norm_eq (z : Fv F v ⊗[F] E) : Algebra.norm (Fv F v) z = D.p 0 z * D.p 1 z := by
  rw [Algebra.norm_eq_matrix_det (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1) z, Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    PI.LocDualGen.EpS.bas0, PI.LocDualGen.EpS.bas1]
  have h0 := congrArg (fun w => (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1).repr w 0) (PI.LocDualGen.EpS.mul_decomp D.hr D.e D.he D.h0 D.h1 z D.e)
  have h1 := congrArg (fun w => (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1).repr w 1) (PI.LocDualGen.EpS.mul_decomp D.hr D.e D.he D.h0 D.h1 z D.e)
  have h2 := congrArg (fun w => (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1).repr w 0)
    (PI.LocDualGen.EpS.mul_decomp D.hr D.e D.he D.h0 D.h1 z (1 - D.e))
  have h3 := congrArg (fun w => (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1).repr w 1)
    (PI.LocDualGen.EpS.mul_decomp D.hr D.e D.he D.h0 D.h1 z (1 - D.e))
  rw [h0, h1, h2, h3]
  simp only [(PI.LocDualGen.EpS.repr_pair D.hr D.e D.he D.h0 D.h1 _ _).1,
    (PI.LocDualGen.EpS.repr_pair D.hr D.e D.he D.h0 D.h1 _ _).2]
  have pe := D.p_e
  have pf := D.p_f
  simp only [p, PI.LocDualGen.EpS.pr_apply] at pe pf
  rw [pe.1, pe.2, pf.1, pf.2]
  simp only [p, PI.LocDualGen.EpS.pr_apply]
  ring

end SD

def oevSub : Subring (Fv F v ⊗[F] E) where
  carrier := OEv (E := E) v
  mul_mem' := fun hx hy => oev_mul v hx hy
  one_mem' := oev_one v
  add_mem' := fun hx hy => Sd.oev_add v hx hy
  zero_mem' := Sd.oev_zero v
  neg_mem' := fun hx => Sd.oev_neg v hx

theorem tens_iff (x : Fv F v ⊗[F] E) :
    (Algebra.TensorProduct.comm F E (Fv F v)).symm x ∈
        PI.SplitIntLoc.tensInt (F := F) (Fv F v) (PI.SplitIntLoc.intOE E)
          (v.adicCompletionIntegers F).toSubring ↔ x ∈ OEv (E := E) v := by
  constructor
  · intro h
    have hle : PI.SplitIntLoc.tensInt (F := F) (Fv F v) (PI.SplitIntLoc.intOE E)
        (v.adicCompletionIntegers F).toSubring ≤
        (oevSub v).comap (Algebra.TensorProduct.comm F E (Fv F v)).toRingEquiv.toRingHom := by
      apply Subring.closure_le.2
      rintro y (⟨⟨a, ha⟩, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩)
      · obtain ⟨b, rfl⟩ := ha
        show Algebra.TensorProduct.comm F E (Fv F v) (((algebraMap (𝓞 E) E) b) ⊗ₜ[F] (1 : Fv F v)) ∈
          OEv (E := E) v
        simp only [Algebra.TensorProduct.comm_tmul]
        exact Sd.inclR_mem (F := F) v b
      · show Algebra.TensorProduct.comm F E (Fv F v) ((1 : E) ⊗ₜ[F] t) ∈ OEv (E := E) v
        have h1 : Algebra.TensorProduct.comm F E (Fv F v) ((1 : E) ⊗ₜ[F] t) = t • (1 : Fv F v ⊗[F] E) := by
          simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
        rw [h1]
        exact Sd.oev_smul v ht (oev_one v)
    have h2 := Subring.mem_comap.1 (hle h)
    have h3 : (Algebra.TensorProduct.comm F E (Fv F v)).toRingEquiv.toRingHom
        ((Algebra.TensorProduct.comm F E (Fv F v)).symm x) = x := by simp
    rw [h3] at h2
    exact h2
  · intro hx
    change x ∈ Submodule.span _ _ at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, -, rfl⟩ := hy
      apply Subring.subset_closure
      left
      exact ⟨⟨(a : E), ⟨a, rfl⟩⟩, by simp [inclR]⟩
    | zero => simpa using zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul t y _ hy =>
      have h1 : t • y = ((t : Fv F v) ⊗ₜ[F] (1 : E)) * y := by
        rw [show t • y = (t : Fv F v) • y from rfl, Algebra.smul_def]
        rfl
      rw [h1, map_mul]
      refine mul_mem ?_ hy
      apply Subring.subset_closure
      right
      exact ⟨⟨t, t.2⟩, by simp⟩

variable {σ v}

namespace SD

variable (D : SD σ v)

theorem mem_iff (x : Fv F v ⊗[F] E) :
    x ∈ OEv (E := E) v ↔ D.p 0 x ∈ v.adicCompletionIntegers F ∧ D.p 1 x ∈ v.adicCompletionIntegers F := by
  let f : (Fv F v ⊗[F] E) →ₐ[Fv F v] Fv F v × Fv F v := (D.p 0).prod (D.p 1)
  have hinj : Function.Injective f := fun z w h => D.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hsurj : Function.Surjective f := fun ab =>
    ⟨ab.1 • D.e + ab.2 • (1 - D.e), Prod.ext (D.p_pair _ _).1 (D.p_pair _ _).2⟩
  let spl : E ⊗[F] Fv F v ≃+* Fv F v × Fv F v :=
    (Algebra.TensorProduct.comm F E (Fv F v)).toRingEquiv.trans (RingEquiv.ofBijective f ⟨hinj, hsurj⟩)
  have hspl : ∀ a : Fv F v, spl ((1 : E) ⊗ₜ[F] a) = (a, a) := by
    intro a
    have h1 : spl ((1 : E) ⊗ₜ[F] a) = f (Algebra.TensorProduct.comm F E (Fv F v) ((1 : E) ⊗ₜ[F] a)) := rfl
    rw [h1, Algebra.TensorProduct.comm_tmul,
      show (a ⊗ₜ[F] (1 : E) : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) a from rfl,
      AlgHom.commutes]
    rfl
  have key := split_integral_local F E v spl hspl ((Algebra.TensorProduct.comm F E (Fv F v)).symm x)
  have hx : spl ((Algebra.TensorProduct.comm F E (Fv F v)).symm x) = f x := by
    show f (Algebra.TensorProduct.comm F E (Fv F v) ((Algebra.TensorProduct.comm F E (Fv F v)).symm x)) = f x
    rw [AlgEquiv.apply_symm_apply]
  rw [hx, tens_iff] at key
  exact key

end SD

theorem sigR_eq_congr (hfin : Module.finrank F E = 2) :
    ∃ τ : E ≃ₐ[F] E, ∀ z, sigR (Fv F v) σ z =
      Algebra.TensorProduct.congr (AlgEquiv.refl : Fv F v ≃ₐ[F] Fv F v) τ z := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  refine ⟨AlgEquiv.ofBijective σ (AlgHom.bijective σ), fun z => rfl⟩

theorem exists_SD (hS : SplitHyp σ v) : Nonempty (SD σ v) := by
  obtain ⟨hfin, hσ, e, hee, he0, he1⟩ := hS
  have hr : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hfin
  have he : IsIdempotentElem e := hee
  let P := PI.LocDualGen.EpS.pr hr e he he0 he1
  have dec := PI.LocDualGen.EpS.decomp hr e he he0 he1
  have pair := PI.LocDualGen.EpS.repr_pair hr e he he0 he1
  obtain ⟨τ, hτ⟩ := sigR_eq_congr (σ := σ) (v := v) hfin
  have hinj : Function.Injective (sigR (Fv F v) σ) := by
    intro z w h
    rw [hτ, hτ] at h
    exact (Algebra.TensorProduct.congr (AlgEquiv.refl : Fv F v ≃ₐ[F] Fv F v) τ).injective h
  set f := sigR (Fv F v) σ e with hfdef
  have hfi : f * f = f := by rw [hfdef, ← map_mul, hee]
  have h01 : ∀ i, P i f = 0 ∨ P i f = 1 := by
    intro i
    have : P i f * P i f = P i f := by rw [← map_mul, hfi]
    have h2 : P i f * (P i f - 1) = 0 := by rw [mul_sub, this, mul_one, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have hfdec : f = P 0 f • e + P 1 f • (1 - e) := dec f
  refine ⟨⟨e, he, he0, he1, hr, ?_⟩⟩
  rcases h01 0 with a0 | a1 <;> rcases h01 1 with b0 | b1
  · exfalso
    apply he0
    apply hinj
    rw [map_zero, ← hfdef, hfdec, a0, b0]; simp
  · rw [← hfdef, hfdec, a0, b1]; simp
  · exfalso
    apply hσ
    have hfe : f = e := by rw [hfdec, a1, b0]; simp
    have hfix : ∀ z, sigR (Fv F v) σ z = z := by
      intro z
      conv_lhs => rw [dec z]
      rw [(sigR (Fv F v) σ).map_add, sigR_smul, sigR_smul, (sigR (Fv F v) σ).map_sub,
        (sigR (Fv F v) σ).map_one, ← hfdef, hfe, ← dec z]
    ext x
    have h1 := hfix ((1 : Fv F v) ⊗ₜ[F] x)
    have h2 : sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] x) = (1 : Fv F v) ⊗ₜ[F] (σ x) := by
      simp [sigR]
    rw [h2] at h1
    exact Algebra.TensorProduct.includeRight_injective (algebraMap F (Fv F v)).injective h1
  · exfalso
    apply he1
    apply hinj
    rw [map_one, ← hfdef, hfdec, a1, b1]; simp

end PI.UnitaryGroupMassFormula.LocJacTyp

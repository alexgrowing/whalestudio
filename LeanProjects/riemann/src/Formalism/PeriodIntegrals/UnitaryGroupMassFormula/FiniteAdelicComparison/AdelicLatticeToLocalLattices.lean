import Mathlib
import Formalism.PeriodIntegrals.AdBridgeSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.MemLocFrom

noncomputable section

namespace PI.FinKW.LocTo

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)

theorem psiV_tmul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (e : I.E) (a : Formalism.MainNotions.S.Af I.F) :
    psiV I v (e ⊗ₜ[I.F] a) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v a ⊗ₜ[I.F] e := by
  first
    | rfl
    | simp [psiV]

theorem psiV_inclE (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (e : I.E) :
    psiV I v (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) e) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) e := by
  show psiV I v (e ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F)) = _
  rw [psiV_tmul, map_one]
  rfl

theorem ov_smul_eq (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : v.adicCompletionIntegers I.F)
    (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) :
    c • t = ((c : v.adicCompletion I.F) ⊗ₜ[I.F] (1 : I.E)) * t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  | add a b ha hb => rw [smul_add, ha, hb, mul_add]

theorem ov_smul_vec (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : v.adicCompletionIntegers I.F)
    (z : Fin I.n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) :
    c • z = ((c : v.adicCompletion I.F) ⊗ₜ[I.F] (1 : I.E)) • z := by
  funext i
  exact ov_smul_eq I v c (z i)

def mulSet (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : Subring (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) where
  carrier := {c | ∀ z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
    psiV I v c • z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))}
  mul_mem' := fun {a b} ha hb z hz => by
    rw [map_mul, mul_smul]
    exact ha _ (hb z hz)
  one_mem' := fun z hz => by
    rw [map_one, one_smul]
    exact hz
  add_mem' := fun {a b} ha hb z hz => by
    rw [map_add, add_smul]
    exact add_mem (ha z hz) (hb z hz)
  zero_mem' := fun z _ => by
    rw [map_zero, zero_smul]
    exact zero_mem _
  neg_mem' := fun {a} ha z hz => by
    rw [map_neg, neg_smul]
    exact neg_mem (ha z hz)

theorem inclR_smul_mem (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (o : 𝓞 I.E)
    (z : Fin I.n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)
    (hz : z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ⊗ₜ[I.F] (algebraMap (𝓞 I.E) I.E o)) • z ∈
      Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have heq : ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ⊗ₜ[I.F] (algebraMap (𝓞 I.E) I.E o)) •
        Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l =
        Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (o • l) := by
      funext i
      simp only [Formalism.L2.SG.Sub.ratV, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Pi.smul_apply, smul_eq_mul]
      show _ * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ⊗ₜ[I.F] l i) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ⊗ₜ[I.F] (o • l) i
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Pi.smul_apply, Algebra.smul_def]
    rw [heq]
    exact Submodule.subset_span ⟨o • l, I.L.smul_mem o hl, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [ov_smul_vec I v c x, smul_smul, mul_comm, ← smul_smul, ← ov_smul_vec I v c]
    exact Submodule.smul_mem _ c hx

theorem intAf_le_mulSet (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Formalism.MainNotions.S.IntAf I.F I.E ≤ mulSet I v := by
  rw [Formalism.MainNotions.S.IntAf, Formalism.UG.tensInt, Subring.closure_le]
  rintro _ (⟨⟨e, he⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
  · obtain ⟨o, rfl⟩ := he
    intro z hz
    rw [psiV_tmul, map_one]
    exact inclR_smul_mem I v o z hz
  · intro z hz
    rw [psiV_tmul]
    have h := Submodule.smul_mem _ (⟨a v, ha v⟩ : v.adicCompletionIntegers I.F) hz
    rw [ov_smul_vec] at h
    exact h

theorem mem_local_lattice_iff : PI.FinKW.MemLocTo := by
  intro I x hx v
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    have heq : PI.FinKW.vecV I v (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((l : Fin I.n → I.E) i)) =
        Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (l : Fin I.n → I.E) := by
      funext i
      exact psiV_inclE I v _
    rw [heq]
    exact Submodule.subset_span ⟨l, l.2, rfl⟩
  | zero =>
    have h0 : PI.FinKW.vecV I v 0 = 0 := by
      funext i
      exact map_zero _
    rw [h0]
    exact zero_mem _
  | add a b _ _ ha hb =>
    have h0 : PI.FinKW.vecV I v (a + b) = PI.FinKW.vecV I v a + PI.FinKW.vecV I v b := by
      funext i
      exact map_add _ _ _
    rw [h0]
    exact add_mem ha hb
  | smul c y _ hy =>
    have h0 : PI.FinKW.vecV I v (c • y) = psiV I v (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • PI.FinKW.vecV I v y := by
      funext i
      exact map_mul _ _ _
    rw [h0]
    exact intAf_le_mulSet I v c.2 _ hy

end PI.FinKW.LocTo

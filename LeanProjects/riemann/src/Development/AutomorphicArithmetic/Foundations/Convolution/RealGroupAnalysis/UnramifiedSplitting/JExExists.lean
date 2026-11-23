import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem sg_zero' {K : Type} [Field K] [NumberField K] (v : P K) : sg v 0 = 0 := by
  have h := (sgLaws K v).1 0 0
  simpa using h

private theorem sg_mul' {K : Type} [Field K] [NumberField K] (v : P K) (x y : Kv v) :
    sg v x * sg v y = sg v (x * y) := by
  have h := (sgLaws K v).2.1 (sg v x) y
  rw [(sgLaws K v).2.2.1] at h
  exact h

private theorem lc_entry {K : Type} [Field K] [NumberField K] (v : P K)
    (x : Matrix.SpecialLinearGroup (Fin 2) (Kv v)) (i k : Fin 2) :
    (lc v (Matrix.SpecialLinearGroup.toGL x)).val i k =
      (1 : Matrix (Fin 2) (Fin 2) (A K)) i k + sg v (x i k - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i k) :=
  (sgLaws K v).2.2.2.2.1 _ i k

private theorem lc_det {K : Type} [Field K] [NumberField K] (v : P K)
    (x : Matrix.SpecialLinearGroup (Fin 2) (Kv v)) :
    ((lc v (Matrix.SpecialLinearGroup.toGL x)).val).det = 1 := by
  have hadd := (sgLaws K v).1
  have hd := x.det_coe
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.det_fin_two]
  simp only [lc_entry]
  simp only [Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, Matrix.one_apply_ne, zero_add, sub_zero]
  have e : ∀ a b : Kv v, sg v (a - b) = sg v a - sg v b := fun a b => by
    have := hadd (a - b) b
    rw [sub_add_cancel] at this
    rw [this]; ring
  have key : sg v (x 0 0 - 1) + sg v (x 1 1 - 1) + sg v (x 0 0 - 1) * sg v (x 1 1 - 1) - sg v (x 0 1) * sg v (x 1 0) = 0 := by
    simp only [sg_mul', ← hadd, ← e]
    have : x 0 0 - 1 + (x 1 1 - 1) + (x 0 0 - 1) * (x 1 1 - 1) - x 0 1 * x 1 0 = 0 := by
      have hd' : x 0 0 * x 1 1 - x 0 1 * x 1 0 = 1 := hd
      linear_combination hd'
    rw [this, sg_zero']
  linear_combination key

private theorem jEx_exists {K : Type} [Field K] [NumberField K] (v : P K) : ∃ j, IsJ v j := by
  refine ⟨{ toFun := fun x => ⟨(lc v (Matrix.SpecialLinearGroup.toGL x)).val, lc_det v x⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply Subtype.ext
    simp
  · intro x y
    apply Subtype.ext
    simp
    rfl
  · intro x
    apply Units.ext
    rfl

theorem UpperTheory.ConvolutionTheory.R2.H.jEx :
    ∀ (K : Type) [Field K] [NumberField K] (v : P K), (∃ j, IsJ v j) ∧ ∀ j, IsJ v j → Continuous j ∧ (∀ x, At v (j x)) ∧ (∀ x, (∀ i k, IsInt (x i k)) → IntAt v (j x)) ∧
      (∀ x i k, (j x) i k = (1 : Matrix (Fin 2) (Fin 2) (A K)) i k + sg v (x i k - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i k)) := by
  intro K _ _ v
  refine ⟨jEx_exists v, fun j hj => ?_⟩
  have hent : ∀ x i k, (j x) i k = (1 : Matrix (Fin 2) (Fin 2) (A K)) i k + sg v (x i k - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i k) := by
    intro x i k
    have h := congrArg (fun g : GL (Fin 2) (A K) => g.val i k) (hj x)
    exact h.trans (lc_entry v x i k)
  have hsg := (sgLaws K v).2.2.2.2.2.2.2.1
  have hcsg := (sgLaws K v).2.2.2.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, hent⟩
  · have hv : Continuous fun x : Matrix.SpecialLinearGroup (Fin 2) (Kv v) => (j x).1 := by
      refine continuous_matrix fun i k => ?_
      have he : (fun x : Matrix.SpecialLinearGroup (Fin 2) (Kv v) => (j x).1 i k) = fun x =>
          (1 : Matrix (Fin 2) (Fin 2) (A K)) i k + sg v (x i k - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i k) :=
        funext fun x => hent x i k
      rw [he]
      have hx : Continuous fun x : Matrix.SpecialLinearGroup (Fin 2) (Kv v) => x i k :=
        continuous_subtype_val.matrix_elem i k
      exact continuous_const.add (hcsg.comp (hx.sub continuous_const))
    exact Continuous.subtype_mk hv fun x => (j x).2
  · intro x
    refine ⟨fun i k => ?_, fun v' hv' i k => ?_⟩
    · rw [hent]
      show _ + (sg v _).1 = _
      rw [(hsg _).1, add_zero]
    · rw [hent]
      show _ + (sg v _).2 v' = _
      rw [(hsg _).2 v' hv', add_zero]
      rfl
  · intro x hx i k
    have : (j x i k).2 v = x i k := by
      have h1 : cp v (j x i k) = x i k := by
        rw [hent, map_add, (sgLaws K v).2.2.1]
        fin_cases i <;> fin_cases k <;> simp
      exact h1
    rw [this]
    exact hx i k

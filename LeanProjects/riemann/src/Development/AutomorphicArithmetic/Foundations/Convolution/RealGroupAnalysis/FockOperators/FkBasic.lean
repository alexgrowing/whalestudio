import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.fkBasic :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (O : Ops F), (∀ N N' : Submodule ℂ (S4 F), N ≤ N' → ∀ m m', m ≤ m' → O.Fk N m ≤ O.Fk N' m') ∧
    (∀ N m w i, ∀ φ ∈ O.Fk N m, O.x w i φ ∈ O.Fk N (m + 1)) ∧
    ∀ N : Submodule ℂ (S4 F), FiniteDimensional ℂ N → ∀ m, FiniteDimensional ℂ (O.Fk N m) := by
  intro F _ _ _ O
  have hs : ∀ (N : Submodule ℂ (S4 F)) (m : ℕ),
      O.Fk N (m + 1) = O.Fk N m ⊔ ⨆ w, ⨆ i, (O.Fk N m).map (O.x w i) := fun _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro N N' h m m' hm
    have h1 : ∀ k, O.Fk N k ≤ O.Fk N' k := by
      intro k
      induction k with
      | zero => exact h
      | succ k ih =>
        rw [hs, hs]
        exact sup_le_sup ih (iSup_mono fun w => iSup_mono fun i => Submodule.map_mono ih)
    have h2 : Monotone (O.Fk N') := monotone_nat_of_le_succ fun k => by
      rw [hs]; exact le_sup_left
    exact (h1 m).trans (h2 hm)
  · intro N m w i φ hφ
    rw [hs]
    refine Submodule.mem_sup_right ?_
    refine Submodule.mem_iSup_of_mem w ?_
    refine Submodule.mem_iSup_of_mem i ?_
    exact Submodule.mem_map_of_mem hφ
  · intro N hN m
    induction m with
    | zero => exact hN
    | succ k ih =>
      rw [hs]
      haveI := ih
      haveI : ∀ w : InfinitePlace F, FiniteDimensional ℂ
          (⨆ i, (O.Fk N k).map (O.x w i) : Submodule ℂ (S4 F)) := fun w =>
        Submodule.finiteDimensional_iSup _
      haveI : FiniteDimensional ℂ
          (⨆ w, ⨆ i, (O.Fk N k).map (O.x w i) : Submodule ℂ (S4 F)) :=
        Submodule.finiteDimensional_iSup _
      exact Submodule.finiteDimensional_sup _ _

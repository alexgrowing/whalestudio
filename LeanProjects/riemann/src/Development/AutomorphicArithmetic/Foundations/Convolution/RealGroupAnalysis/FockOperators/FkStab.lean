import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkD

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.fkStab :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F) (T : Module.End ℂ (S4 F)) (N N' : Submodule ℂ (S4 F)), N' ≤ Vac δ → (∀ φ ∈ N, T φ ∈ N') →
    (∀ w i φ, T (O.x w i φ) ∈ Submodule.span ℂ {χ : S4 F | ∃ w' j, χ = O.x w' j (T φ) ∨ χ = O.d w' j (T φ)}) → ∀ m, ∀ φ ∈ O.Fk N m, T φ ∈ O.Fk N' m := by
  intro F _ _ _ δ O T N N' hN' hN hT m
  induction m with
  | zero => exact hN
  | succ m ih =>
    have hb := fkBasic F O
    have hmono : O.Fk N' m ≤ O.Fk N' (m + 1) := hb.1 N' N' le_rfl m (m + 1) (Nat.le_succ m)
    have key : O.Fk N (m + 1) ≤ (O.Fk N' (m + 1)).comap T := by
      have hu : O.Fk N (m + 1) = O.Fk N m ⊔ ⨆ w, ⨆ i, (O.Fk N m).map (O.x w i) := rfl
      rw [hu]
      refine sup_le (fun φ hφ => hmono (ih φ hφ)) (iSup_le fun w => iSup_le fun i => ?_)
      rintro _ ⟨φ, hφ, rfl⟩
      have hs : Submodule.span ℂ {χ : S4 F | ∃ w' j, χ = O.x w' j (T φ) ∨ χ = O.d w' j (T φ)} ≤ O.Fk N' (m + 1) := by
        refine Submodule.span_le.2 ?_
        rintro χ ⟨w', j, rfl | rfl⟩
        · exact hb.2.1 N' m w' j _ (ih φ hφ)
        · exact fkD F δ O N' hN' m w' j _ (ih φ hφ)
      exact hs (hT w i φ)
    exact fun φ hφ => key hφ

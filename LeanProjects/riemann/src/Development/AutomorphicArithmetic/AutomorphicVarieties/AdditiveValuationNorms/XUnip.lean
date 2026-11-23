import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DinfNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.DualUnip

open UpperTheory.V UpperTheory.V.PropA NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.PropA.xUnip :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (N : ℕ)
      (U : Subgroup (G k Ω)) [U.Normal], IsClosed (U : Set (G k Ω)) → Module.Finite ℤ_[l] (Xinf l N U) →
      ∀ γ ∈ levU l U 1, Unip (xRep l N U γ) := by
  intro k Ω _ _ _ _ _ l _ N U _ hU hfin γ hγ
  refine dualUnip l (Dinf l N U) (dRep l N U γ⁻¹) (xRep l N U γ) hfin (fun x φ => xRep_apply l N U γ x φ) fun φ => ?_
  obtain ⟨n, -, hn⟩ := (dinfNil k Ω l N U hU φ.1 φ.2).2 γ⁻¹ (inv_mem hγ)
  refine ⟨n, Subtype.ext ?_⟩
  have key : ∀ (m : ℕ) (ψ : Dinf l N U), (((dRep l N U γ⁻¹ - 1) ^ m) ψ).1 =
      ((funRep ℤ_[l] (QZ l) (cycU l U) γ⁻¹ - 1) ^ m) ψ.1 := by
    intro m
    induction m with
    | zero => intro ψ; rfl
    | succ m ih =>
      intro ψ
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      rfl
  rw [key, hn]
  rfl

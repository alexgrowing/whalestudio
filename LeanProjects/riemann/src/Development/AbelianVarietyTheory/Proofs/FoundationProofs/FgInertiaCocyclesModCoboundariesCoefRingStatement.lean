import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FgInertiaCocyclesModCoboundariesCoefRing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCoc
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fg_inertiaCocycles_mod_coboundaries_coefRing : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (I : Subgroup (G ℚ Ω)) (P : Set (G ℚ Ω)) (γ : G ℚ Ω), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ z ∈ coc W c I, ∃ v : Fin 2 → Qbar l, (∀ i, v i ∈ c.O) ∧ ∀ σ ∈ P, z σ = mat W σ *ᵥ v - v) → (∀ z ∈ coc W c I, (∀ σ ∈ P, z σ = 0) → z γ = 0 → ∀ s ∈ I, z s = 0) → ((coc W c I).map (cob W c I).mkQ).FG := by
  first | exact @GlobalTheory.InertCoh.fg_coc_mod_cob | exact GlobalTheory.InertCoh.fg_coc_mod_cob | (intros; apply GlobalTheory.InertCoh.fg_coc_mod_cob <;> assumption)

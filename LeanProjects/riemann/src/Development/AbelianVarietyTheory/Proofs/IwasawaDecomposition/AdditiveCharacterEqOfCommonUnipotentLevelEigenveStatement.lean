import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdditiveCharacterEqOfCommonUnipotentLevelEigenve
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveCharacter_eq_of_common_unipotentLevel_eigenvector : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (p m : ℕ) (θ : GAf L n ≃* GAf L n) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (F : GAf L n → V) (F' : GAf L n → V') (J J' : Subgroup (GAf L n)) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (ψ₀ ψ₀' : AddChar (s.v.adicCompletion (maximalRealSubfield L)) ℂ) (ξ ξ' : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), p.Prime → s.Above p → m.Coprime p → 2 ≤ r → r ≤ n → FrameAut θ → F ≠ 0 → F' ≠ 0 → NG.IsPsi0 s ψ₀ → NG.IsPsi0 s ψ₀' → NG.LevelUni J χ s r ψ₀ ξ → NG.LevelUni J' χ' s r ψ₀' ξ' → (∀ κ : J, Eig F κ (χ κ : ℂˣ)) → (∀ κ : J', Eig F' κ (χ' κ : ℂˣ)) → (∀ κ, TrivOutside {s.v} κ → NG.UniRT s r (s.loc n κ) → ∃ c c' : ℂ, Eig F (θ κ) c ∧ Eig F' (θ κ) c' ∧ c ^ m = c' ^ m) → ∀ y, Valued.v y ≤ 1 → ψ₀ y = ψ₀' y := by
  first | exact @GlobalTheory.PsiCmp.fractionFieldToGenericStalk_algebraMap_eq | exact GlobalTheory.PsiCmp.fractionFieldToGenericStalk_algebraMap_eq | (intros; apply GlobalTheory.PsiCmp.fractionFieldToGenericStalk_algebraMap_eq <;> assumption)

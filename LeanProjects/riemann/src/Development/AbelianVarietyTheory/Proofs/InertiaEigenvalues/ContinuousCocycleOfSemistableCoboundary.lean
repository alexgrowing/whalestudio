import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCochainOfDeRhamCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryDeRhamOfCoboundarySemistableStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.CocycStLemma

theorem tmul_one_injective {F V B : Type} [Field F] [AddCommGroup V] [Module F V] [Ring B] [Algebra F B]
    [Nontrivial B] : Function.Injective (fun v : V => v ⊗ₜ[F] (1 : B)) := by
  have hinj : Function.Injective (Algebra.linearMap F B) := (algebraMap F B).injective
  obtain ⟨f, hf⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F B)
    (LinearMap.ker_eq_bot.mpr hinj)
  intro v w h
  have h2 := congrArg (fun x => TensorProduct.rid F V (LinearMap.lTensor V f x)) h
  have h1 : f 1 = 1 := by
    have := LinearMap.congr_fun hf 1
    simpa using this
  simpa [h1] using h2

end GlobalTheory.CocycStLemma

theorem GlobalTheory.cocycle_of_st_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ (z : V ⊗[ℚ_[l]] Bst P) (c : ↥(GK K) → V), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) → c ∈ continuousCocycles ρ := by
  intro l _ P AI T K V _ _ _ _ _ _ _ ρ hρ z c hc
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := GlobalTheory.T.coboundary_deRham_of_coboundary_semistable l P AI T K V ρ c z hc
    refine GlobalTheory.T.continuous_cochain_of_deRham_coboundary l P AI T K V ρ hρ 0 Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) b c ?_
    intro g
    simp [hb g]
  · intro g h
    haveI : Nontrivial P.R.B := nontrivial_B P
    haveI : Nontrivial (Bst P) := Polynomial.nontrivial
    apply GlobalTheory.CocycStLemma.tmul_one_injective (F := ℚ_[l]) (B := Bst P)
    simp only [add_tmul]
    rw [hc, hc g, map_mul, Module.End.mul_apply]
    have e : stRep P ρ g (c h ⊗ₜ[ℚ_[l]] (1 : Bst P)) = ρ g (c h) ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
      rw [stRep_tmul, map_one]
    rw [← e, hc h, map_sub]
    abel

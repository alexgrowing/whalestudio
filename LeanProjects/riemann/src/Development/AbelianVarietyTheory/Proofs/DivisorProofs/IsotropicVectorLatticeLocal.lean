import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionNonsplitPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

open IsDedekindDomain

namespace GlobalTheory.InertIwasawaUnram

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * x = 1 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ g : GLoc σ J v, ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧ ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := by
  intro F E _ _ _ _ _ σ hσ hU n J hJ x y hx hy L hL v hv hSD g
  haveI := hL
  obtain ⟨c, hc⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hσ inferInstance
  have hram : ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.ramificationIdx (𝓞 F) = 1 := fun P => by
    haveI := P.isPrime
    haveI : Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal := inferInstance
    exact Ideal.ramificationIdx_eq_one _ _
  have hUn : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v := fun P _ => hram P
  have hIU : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := fun P _ => hram P
  obtain ⟨w, hw⟩ := ((GlobalTheory.LFun.exists_isInertChart σ hσ v).1 hIU).resolve_left hv
  obtain ⟨q, k, hk, hg, β, hβ⟩ := GlobalTheory.InertIwasawaLoc.exists_loc hσ hc hJ hw hUn hSD
    (e := x) (p := cT (σ : E →+* E) y * J) (by rw [Matrix.mul_assoc] at hy ⊢; exact hy) hx g
  exact ⟨q, k, hk, hg, β, hβ⟩

end GlobalTheory.InertIwasawaUnram

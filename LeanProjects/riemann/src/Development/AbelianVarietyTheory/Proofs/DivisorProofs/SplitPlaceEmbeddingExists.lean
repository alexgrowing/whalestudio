import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinset
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology

namespace GlobalTheory.SplitEmbed

theorem exists_algHom_of_splitsFully : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : Pl F, SplitsFully E v → Nonempty (E →ₐ[F] Fv F v) := by
  intro F E _ _ _ _ _ σ h v hs
  classical
  haveI hprime : (v.asIdeal.under ℤ).IsPrime := Ideal.IsPrime.under ℤ v.asIdeal
  have hne : v.asIdeal.under ℤ ≠ ⊥ := by
    intro hb
    exact v.ne_bot (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) hb)
  obtain ⟨q, hq⟩ := (Submodule.IsPrincipal.principal (v.asIdeal.under ℤ))
  have hq' : v.asIdeal.under ℤ = Ideal.span {q} := hq
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hne (by rw [hq']; simp)
  have hqp : Prime q := by
    rw [← Ideal.span_singleton_prime hq0, ← hq']
    exact hprime
  set p := q.natAbs with hpdef
  have hp : p.Prime := Int.prime_iff_natAbs_prime.1 hqp
  have hspan : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [hq', hpdef, Int.span_natAbs]
  have hpv : (p : 𝓞 F) ∈ v.asIdeal := by
    have : (p : ℤ) ∈ v.asIdeal.under ℤ := by rw [hspan]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.under_def, Ideal.mem_comap] at this
    simpa using this
  have hcount : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
    have := hs
    unfold SplitsFully at this
    rw [hspan] at this
    exact this
  rw [GlobalTheory.AdelicU.nonempty_split_iff h]
  exact GlobalTheory.GoodPlace.ncard_primesOver_eq_two h.2.2.1 hp hcount v hpv

end GlobalTheory.SplitEmbed

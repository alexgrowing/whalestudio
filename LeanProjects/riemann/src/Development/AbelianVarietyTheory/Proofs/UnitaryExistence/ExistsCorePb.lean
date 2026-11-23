import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsParPinsCanon
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HeckeCharacterFamilyConductorStatement
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.CoreExist

theorem exists_prime_over (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  obtain ⟨P, hP, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := 𝓞 K) (Ideal.span {(p : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le)
  have hm : ((p : ℕ) : 𝓞 K) ∈ P := by
    have : (p : ℤ) ∈ P.comap (algebraMap ℤ (𝓞 K)) := hc ▸ Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  refine ⟨⟨P, hP, fun h => ?_⟩, hm⟩
  rw [h, Ideal.mem_bot] at hm
  exact hp.ne_zero (by exact_mod_cast hm)

theorem exists_core_pb (D : D7) (hO : OFull D) (hZ : OZeta D) (hV : VolTieG D)
    (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K))
    (hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) :
    ∃ T : CoreJ D, LawsJ T ∧ LawsCore T.toCore ∧ T.Q.Canon ∧ T.pb = pb := by
  obtain ⟨Q, hP, hC, hpq, hM⟩ := GlobalTheory.Member.ParExist.exists_par_pins_canon D hO hZ pb hg
  obtain ⟨T, h₁, h₂, h₃, h₄, -⟩ := GlobalTheory.T.hecke_character_family_conductor D Q hP hpq hV pb hg hM (fun _ _ => 1) (fun _ _ σ _ =>
    ⟨⟨continuous_const, fun _ => rfl⟩, fun _ => rfl, fun _ _ => ⟨1, by simp, by simp⟩⟩)
  exact ⟨T, h₁, h₂, h₄ ▸ hC, h₃⟩

theorem exists_core : ∀ (D : D7), OFull D → OZeta D → VolTieG D → (∃ T : CoreJ D, LawsJ T ∧ LawsCore T.toCore ∧ T.Q.Canon) ∧ ∀ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) → ∃ T : CoreJ D, LawsJ T ∧ LawsCore T.toCore ∧ T.Q.Canon ∧ T.pb = pb := by
  intro D hO hZ hV
  refine ⟨?_, exists_core_pb D hO hZ hV⟩
  choose pb hg using fun k => exists_prime_over D.host.K (D.host.g_prime k)
  obtain ⟨T, h₁, h₂, h₃, -⟩ := exists_core_pb D hO hZ hV pb hg
  exact ⟨T, h₁, h₂, h₃⟩

end GlobalTheory.Member.CoreExist

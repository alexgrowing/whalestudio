import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

section Compare

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

theorem HeightOneIntersection.coe_bot :
    ((Subalgebra.toSubmodule (⊥ : Subalgebra A K) : Submodule A K) : Set K) =
      Set.range (algebraMap A K) := by
  ext x
  exact Algebra.mem_bot

theorem HeightOneIntersection.coe_iInf :
    ((⨅ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1),
        GroundTheory.Heights₂.Heights.Model.localizedIn p.asIdeal
          (Subalgebra.toSubmodule (⊥ : Subalgebra A K)) : Submodule A K) : Set K) =
      ⋂ (p : Ideal A) (_ : p.IsPrime) (_ : p.height = 1), locIn A K p := by
  ext x
  simp only [SetLike.mem_coe, Submodule.mem_iInf, Set.mem_iInter]
  have key : ∀ (p : Ideal A) [p.IsPrime],
      x ∈ GroundTheory.Heights₂.Heights.Model.localizedIn p
          (Subalgebra.toSubmodule (⊥ : Subalgebra A K)) ↔ x ∈ locIn A K p := by
    intro p _
    change (∃ s : A, s ∉ p ∧ s • x ∈ (⊥ : Subalgebra A K)) ↔
      ∃ a s : A, s ∉ p ∧ algebraMap A K s * x = algebraMap A K a
    constructor
    · rintro ⟨s, hs, hsx⟩
      obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hsx
      exact ⟨a, s, hs, by rw [ha, Algebra.smul_def]⟩
    · rintro ⟨a, s, hs, h⟩
      refine ⟨s, hs, Algebra.mem_bot.mpr ⟨a, ?_⟩⟩
      rw [Algebra.smul_def, h]
  constructor
  · intro h p hp h1
    exact (key p).mp (h ⟨p, hp⟩ h1)
  · intro h p h1
    exact (key p.asIdeal).mpr (h p.asIdeal p.isPrime h1)

theorem HeightOneIntersection.equiv_at :
    (Subalgebra.toSubmodule (⊥ : Subalgebra A K) =
      ⨅ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1),
        GroundTheory.Heights₂.Heights.Model.localizedIn p.asIdeal
          (Subalgebra.toSubmodule (⊥ : Subalgebra A K))) ↔
      Set.range (algebraMap A K) =
        ⋂ (p : Ideal A) (_ : p.IsPrime) (_ : p.height = 1), locIn A K p := by
  rw [← HeightOneIntersection.coe_bot, ← HeightOneIntersection.coe_iInf]
  exact SetLike.coe_set_eq.symm

end Compare

theorem HeightOneIntersection.equiv :
    GroundTheory.Heights₂.Heights.Model.HeightOneIntersection.Statement ↔
      HeightOneIntersection.Statement := by
  constructor
  · intro h A K _ _ _ _ _ _ _
    exact (HeightOneIntersection.equiv_at A K).mp (h A K)
  · intro h A _ _ _ _ K _ _ _
    exact (HeightOneIntersection.equiv_at A K).mpr (h A K)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

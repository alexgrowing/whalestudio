import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjSlot

theorem resS_sigInt_eq_zero_iff (D : D7) (PP : Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resS D.host.F PP (sigInt (instOf D) s) = 0 ↔ resS D.host.F (conjPl PP) s = 0 :=
  resS_sigS_eq_zero_iff (instOf D).cm (isConjPl_conjPl PP).symm s

theorem mem_conjPl {E : Type} [Field E] [NumberField E] [StarRing E] (PP : Pl E) (a : 𝓞 E) :
    a ∈ (conjPl PP).asIdeal ↔ starO a ∈ PP.asIdeal := Iff.rfl

theorem natCast_mem_conjPl {E : Type} [Field E] [NumberField E] [StarRing E] (PP : Pl E) (N : ℕ) :
    (N : 𝓞 E) ∈ (conjPl PP).asIdeal ↔ (N : 𝓞 E) ∈ PP.asIdeal := by
  show starOHom (N : 𝓞 E) ∈ PP.asIdeal ↔ _
  rw [map_natCast]

theorem isConjPl_conjPl_lev (D : D7) (PP : Pl D.host.E) : Formalism.IndefR.Lev.IsConjPl (D := D) PP (conjPl PP) :=
  fun c hc => ⟨starO c, by rw [mem_conjPl, starO_starO]; exact hc, rfl⟩

theorem intersection_update_fsHerm_neg_one : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP') → ∀ R : Formalism.L2.Herm.intAf D.host.F D.host.E → Prop, (∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ Q' : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q'.asIdeal → Q' ≠ Q → resS D.host.F Q' s = 0) ∧ R s) → ∀ PP ∈ Pg, (∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ PP' ∈ Pg, (PP' ≠ PP → resS D.host.F PP' s = 0) ∧ resS D.host.F PP' (sigInt (instOf D) s) = 0) ∧ R s) ∧ ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ PP' ∈ Pg, resS D.host.F PP' s = 0 ∧ (PP' ≠ PP → resS D.host.F PP' (sigInt (instOf D) s) = 0)) ∧ R s := by
  intro D Pg hg hconj R hR PP hPP
  have hne : ∀ P ∈ Pg, ∀ P' ∈ Pg, conjPl P ≠ P' := fun P hP P' hP' h =>
    hconj P hP P' hP' (h ▸ isConjPl_conjPl_lev D P)
  constructor
  · obtain ⟨s, hs, hRs⟩ := hR PP (hg PP hPP)
    refine ⟨s, fun P hP => ⟨fun h => hs P (hg P hP) h, ?_⟩, hRs⟩
    rw [resS_sigInt_eq_zero_iff]
    exact hs _ ((natCast_mem_conjPl P _).2 (hg P hP)) (hne P hP PP hPP)
  · obtain ⟨s, hs, hRs⟩ := hR (conjPl PP) ((natCast_mem_conjPl PP _).2 (hg PP hPP))
    refine ⟨s, fun P hP => ⟨hs P (hg P hP) (hne PP hPP P hP).symm, fun h => ?_⟩, hRs⟩
    rw [resS_sigInt_eq_zero_iff]
    refine hs _ ((natCast_mem_conjPl P _).2 (hg P hP)) fun e => h ?_
    rw [← conjPl_conjPl P, e, conjPl_conjPl]

end GlobalTheory.ConjSlot

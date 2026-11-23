import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistRingsCharactersClassGroups
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistRings_characters_classGroups : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (J : ∀ (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 ↥D.LL0)), ((l : ℕ) : 𝓞 ↥D.LL0) ∈ w.asIdeal → (↥D.LL0 →+* PadicAlgCl l)), (∀ (l : ℕ) [Fact l.Prime] w h (x : 𝓞 ↥D.LL0), x ∈ w.asIdeal ↔ ‖J l w h x‖ < 1) → ValLL0 D cf → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → ∃ c0 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)), (∀ (l : ℕ) [Fact l.Prime] j, (c0 l j).1 ≤ (b0 l j).1) → ∃ (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T), ∀ i, Sp.j0 i = J (T.l i) (Sp.eTw i) (Sp.pl_emb i).1 ∧ Sp.K0 i = b0 (T.l i) (Sp.j0 i) ∧ Sp.Lw i = b1 (T.l i) (Sp.j0 i) := by
  first | exact @GlobalTheory.TwRing.exists_ringSpec | exact GlobalTheory.TwRing.exists_ringSpec | (intros; apply GlobalTheory.TwRing.exists_ringSpec <;> assumption)

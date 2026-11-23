import Formalism.LocalToGlobal.GlobalTheory.GL4.Statement

noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_E (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  have h1 : Module.finrank ℚ D.host.F = D.R.f := D.host.finrank_hostF
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  rw [← Module.finrank_mul_finrank ℚ D.host.F D.host.E, h1, h2]
  ring

theorem card_quot_nat (E : Type) [Field E] [NumberField E] (T : ℕ) :
    Nat.card (𝓞 E ⧸ Ideal.span {((T : ℕ) : 𝓞 E)}) = T ^ Module.finrank ℚ E := by
  have h := Ideal.absNorm_span_singleton (algebraMap ℤ (𝓞 E) (T : ℤ))
  rw [Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, map_natCast] at h
  simp only [Int.natAbs_pow, Int.natAbs_natCast] at h
  rw [← h, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem dualSub_eq {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (L : Submodule (𝓞 E) S.V) :
    Formalism.MainNotions.flipTwoThree.dualSub S L = (Formalism.HermitianLatticesTheory.dual S.hT L).toAddSubgroup := by
  ext x
  show (∀ y ∈ L, S.hT y x ∈ (algebraMap (𝓞 E) E).range) ↔ x ∈ Formalism.HermitianLatticesTheory.dual S.hT L
  rw [Formalism.L2.Herm.mem_dual]

theorem relIndex_of_equiv {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
    (L : Submodule (𝓞 E) S.V) (T : ℕ)
    (e : Nonempty ((Formalism.HermitianLatticesTheory.dual S.hT L ⧸ L.comap (Formalism.HermitianLatticesTheory.dual S.hT L).subtype) ≃ₗ[𝓞 E]
      (𝓞 E ⧸ Ideal.span {((T : ℕ) : 𝓞 E)}))) :
    L.toAddSubgroup.relIndex (Formalism.MainNotions.flipTwoThree.dualSub S L) = T ^ Module.finrank ℚ E := by
  obtain ⟨e⟩ := e
  rw [dualSub_eq, ← card_quot_nat E T, ← Nat.card_congr e.toEquiv]
  rfl

theorem clsLat_index {D : D7} (X : Formalism.L2.Herm.FullTied D) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m)
    (c : (D.mem u).C.cls i) :
    (D.clsLat u i c).toAddSubgroup.relIndex (Formalism.MainNotions.flipTwoThree.dualSub (D.sp.X i) (D.clsLat u i c)) =
      Formalism.MainNotions.flipTwoThree.Tu D u ^ (2 * D.R.f) := by
  rw [relIndex_of_equiv _ _ _ ((X.atT u).disc i hi c), finrank_E]
  rfl

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end

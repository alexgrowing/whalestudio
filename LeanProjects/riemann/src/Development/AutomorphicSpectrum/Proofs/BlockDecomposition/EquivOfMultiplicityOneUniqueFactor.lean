import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.FineStep

theorem isSubquotient_subQuot_self {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {J : Representation ℂ G V} (S R : Subrepresentation J) : IsSubquotient (subQuot S R) J := by
  refine GlobalTheory.SmGL.IsSubquotient.trans (σ := S.toRepresentation) ?_ ?_
  · refine GlobalTheory.SmGL.IsSubquotient.of_surjective
      ⟨(Submodule.comap S.toSubmodule.subtype R.toSubmodule).mkQ, fun g => ?_⟩ ?_
    · ext v
      rfl
    · exact Submodule.mkQ_surjective _
  · refine GlobalTheory.SmGL.IsSubquotient.of_injective ⟨S.toSubmodule.subtype, fun g => ?_⟩ ?_
    · ext v
      rfl
    · exact Subtype.val_injective

theorem nonempty_equiv_of_jhMult_eq_one :
    ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (T : Representation ℂ G W) (J : Representation ℂ G V), T.IsIrreducible → HasFiniteLength J →
      jhMult T J = 1 →
      (∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X), ρ.IsIrreducible →
        IsSubquotient ρ J → Nonempty (ρ.Equiv T)) → Nonempty (J.Equiv T) := by
  intro G V W _ _ _ _ _ T J hT hfin hJ hall
  have hstep : ∀ {P Q : Subrepresentation J}, Q ⋖ P → GlobalTheory.JHMult.Step T P Q := fun {P Q} h =>
    GlobalTheory.JHMult.step_iff.mp
      (hall _ (subQuot P Q) (GlobalTheory.SmGL.isIrreducible_subQuot h) (isSubquotient_subQuot_self P Q))
  have hwf : WellFounded ((· < ·) : Subrepresentation J → Subrepresentation J → Prop) := by
    haveI : IsArtinian (MonoidAlgebra ℂ G) J.asModule :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp
        (show IsFiniteLength (MonoidAlgebra ℂ G) J.asModule from hfin)).2
    exact (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := J)).toOrderEmbedding.ltEmbedding.wellFounded
      wellFounded_lt
  have hne : (⊥ : Subrepresentation J) ≠ ⊤ := by
    intro h
    haveI : Subsingleton V := ⟨fun a b => by
      have ha : a ∈ (⊤ : Subrepresentation J).toSubmodule := Submodule.mem_top
      have hb : b ∈ (⊤ : Subrepresentation J).toSubmodule := Submodule.mem_top
      rw [← h] at ha hb
      rw [(Submodule.mem_bot ℂ).mp ha, (Submodule.mem_bot ℂ).mp hb]⟩
    have h0 := GlobalTheory.SmGL.jhMult_of_subsingleton hT J
    rw [hJ] at h0
    exact one_ne_zero h0
  have hirr : J.IsIrreducible := by
    show IsSimpleOrder (Subrepresentation J)
    refine { exists_pair_ne := ⟨⊥, ⊤, hne⟩, eq_bot_or_eq_top := fun S => ?_ }
    by_contra hS
    obtain ⟨hS0, hS1⟩ := not_or.mp hS
    obtain ⟨A, ⟨hA0, hAS⟩, hAmin⟩ := hwf.has_min {A | ⊥ < A ∧ A ≤ S}
      ⟨S, show ⊥ < S ∧ S ≤ S from ⟨bot_lt_iff_ne_bot.mpr hS0, le_rfl⟩⟩
    obtain ⟨B, hB, hBmin⟩ := hwf.has_min {B | S < B}
      ⟨⊤, show S < ⊤ from lt_top_iff_ne_top.mpr hS1⟩
    have hcA : (⊥ : Subrepresentation J) ⋖ A := ⟨hA0, by
      intro c hc hcA
      exact hAmin c (show ⊥ < c ∧ c ≤ S from ⟨hc, hcA.le.trans hAS⟩) hcA⟩
    have hSB : S < B := hB
    have hcB : S ⋖ B := ⟨hSB, by
      intro c hc hcB
      exact hBmin c (show S < c from hc) hcB⟩
    have hocc : GlobalTheory.SmGL.OccursTimes T J 2 := by
      have := GlobalTheory.JHMult.occurs_of_finset (σ := T) (ρ := J) (r := 2) Finset.univ ![A, B] ![⊥, S]
        (by simp [Fin.forall_fin_two, hSB.le]) (by simp [Fin.forall_fin_two, hAS])
        (by simp [Fin.forall_fin_two, hstep hcA, hstep hcB])
      simpa using this
    have h2 : ((2 : ℕ) : ℕ∞) ≤ GlobalTheory.SmGL.jhMult T J := by
      unfold GlobalTheory.SmGL.jhMult
      exact le_iSup₂_of_le 2 hocc le_rfl
    rw [hJ] at h2
    have h21 : ¬ ((2 : ℕ) : ℕ∞) ≤ ((1 : ℕ) : ℕ∞) := by
      rw [ENat.natCast_le_natCast]
      omega
    exact h21 (by simpa using h2)
  exact hall V J hirr (GlobalTheory.SmGL.IsSubquotient.refl J)

end GlobalTheory.CompanionTheory.FineStep

import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalCharSpreadCommutesWithRestriction
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem universalCharacter_admissibleConductor_inertia_surjective : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (hE : IsEmpty D.nd.Loc) (F : TwF T)
    (i : T.Tw) (Q : Finset (PlE D.host)) (M : ℕ), Formalism.MainNotions.NAdm.AdmQ (T.ntw hE F (TwL.empty T)) i Q M →
    ∀ P (hP : P ∈ Q),
      (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
        Function.Surjective fun σ : Ine (F := D.host.E) A =>
          Multiplicative.toAdd (GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M σ) ⟨P, hP⟩) ∧
      ∀ P' ∈ Q, P' ≠ P → ¬ IsConjPl D.host P P' → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' →
        ∀ σ ∈ Ine (F := D.host.E) A, Multiplicative.toAdd (GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M σ) ⟨P, hP⟩ = 0 := by
  intro _ D cf b0 b1 Sx T Sp hE F i Q M hQ P hP
  obtain ⟨-, hadm⟩ := hQ
  have hcl : ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q := fun P hP P' h => by
    obtain ⟨⟨P'', hP'', h''⟩, -⟩ := hadm P hP
    rw [GlobalTheory.GalChar.isConjPl_unique h h'']
    exact hP''
  obtain ⟨-, χ, h1, h2, h3, h4, h5⟩ := hadm P hP
  have hsP : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
      ∀ b, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := fun A hA b => by
    obtain ⟨σ, hσ⟩ := h5 A hA (Multiplicative.toAdd b)
    exact ⟨σ.1, σ.2, Multiplicative.toAdd.injective hσ⟩
  have hDel : GlobalTheory.GalChar.IsDel D.host T.cc (T.l i) M (GlobalTheory.GalChar.pair D.host P) χ := by
    refine ⟨h1, h2, h3, fun w hw => h4 w (fun e => hw (Or.inl e)) (fun e => hw (Or.inr e)), fun w hw A hA b => ?_⟩
    rcases hw with rfl | hw
    · exact hsP A hA b
    · exact GlobalTheory.SpreadRestrict.surj_conj (X := T.ntw hE F (TwL.empty T)) χ h2 hw hsP A hA b
  have hD := GlobalTheory.GalChar.isDel_delOf D.host T.cc (T.l i) ⟨χ, hDel⟩
  have hcoord := (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host T.cc (T.l i)).2.2.2.2.2.2.1 Q M hcl P hP
  refine ⟨fun A hA c => ?_, fun P' _ hne hnc A hA σ hσ => ?_⟩
  · obtain ⟨σ, hσ, e⟩ := hD.2.2.2.2 P (Or.inl rfl) A hA (Multiplicative.ofAdd c)
    refine ⟨⟨σ, hσ⟩, ?_⟩
    show Multiplicative.toAdd (GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M σ) ⟨P, hP⟩ = c
    rw [hcoord, e, toAdd_ofAdd]
  · rw [hcoord, hD.2.2.2.1 P' (fun h => h.elim (fun e => hne e) (fun e => hnc e)) A hA σ hσ]
    rfl

end GlobalTheory.HeightCounting.FormsStep

end

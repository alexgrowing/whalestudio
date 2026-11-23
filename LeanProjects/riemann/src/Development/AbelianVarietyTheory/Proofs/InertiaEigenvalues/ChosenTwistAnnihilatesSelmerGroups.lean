import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Development.AutomorphicArithmetic.CyclotomicBounds.CyclotomicOrders.NuHost
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem twist_kills_selmer : ∀ (D : D7) (C : NChoice D) (I : TwIn D) (ρ : FamilyRepresentationConstants.RhoFam D), NChTie D C → TwGoodAt D C I →
    KillingConditions.SignatureChoiceCondition ρ C → KillingConditions.KillAt ρ := by
  intro D C I ρ hT hG hA i hi
  have hw : D.what₂.muAt (D.nd.w i) ≠ D.what₂.mu0 := hi
  obtain ⟨-, hg⟩ := hG (D.nd.w i) hw
  obtain ⟨hA1, hA2⟩ := hA i hi
  obtain ⟨-, -, -, ⟨epsT, hT0, hTs, hTle⟩, -, hD⟩ := hg
  have hl : D.ntw.l (C.twI (D.nd.w i)) = D.nd.l i := by rw [← hT.twOf_eq]; exact D.ntw.twOf_l i
  have heps : twEps D (C.twI (D.nd.w i)) = Formalism.MainNotions.TwistedPlaces.epsL (D.nd.l i) := by
    rw [twEps, Formalism.MainNotions.TwistedPlaces.epsL, hl, one_div]
  refine ⟨fun π hπ => ?_, ?_⟩
  · obtain ⟨s, hs, hfin, hle⟩ := hA1 π hπ
    have h1 := hTle s hs
    have hsum : epsT s ≤ twEps D (C.twI (D.nd.w i)) :=
      le_trans (Finset.single_le_sum (fun s _ => hT0 s) ((Formalism.MainNotions.BlochKatoReduction.Gen.mem_SigG _ _ s).2 hs)) hTs
    have h0 : 0 ≤ (Formalism.MainNotions.BlochKatoReduction.Gen.nu D.ntw (C.twI (D.nd.w i)) : ℝ) + epsT s :=
      add_nonneg (Nat.cast_nonneg _) (hT0 s)
    have h2 := le_trans hle h1
    refine ⟨hfin (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1), ?_⟩
    rw [ENNReal.ofReal_le_ofReal_iff h0] at h2
    rw [← heps]
    rw [UpperTheory.KStar.nu_eq_nuL, hl] at h2
    linarith
  · rw [← heps]
    exact le_trans (mul_le_mul_of_nonneg_left hA2 (Nat.cast_nonneg _)) hD

end GlobalTheory.NLink

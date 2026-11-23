import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfHeckeCharUnramifi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotTripleUnr

theorem unramAt_mul {D : D7} {ε : AF D.host.F} {χ₁ χ₂ : (AE D)ˣ →* Circle}
    (h₁ : GlobalTheory.WeilParts.UnramAt ε χ₁) (h₂ : GlobalTheory.WeilParts.UnramAt ε χ₂) : GlobalTheory.WeilParts.UnramAt ε (χ₁ * χ₂) := by
  intro x hx h1 h2
  rw [MonoidHom.mul_apply, h₁ x hx h1 h2, h₂ x hx h1 h2, one_mul]

theorem under_eq_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
  refine HeightOneSpectrum.ext ((P.under (𝓞 D.host.F)).isMaximal.eq_of_le (P'.under (𝓞 D.host.F)).isPrime.ne_top
    fun a ha => ?_)
  obtain ⟨c', h1, h2⟩ := h (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ha
  have hfix : star (algebraMap D.host.F D.host.E (a : D.host.F)) = algebraMap D.host.F D.host.E (a : D.host.F) :=
    (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = c' := RingOfIntegers.ext (h2.trans hfix).symm
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P'.asIdeal
  rwa [e]

theorem unramAt_mu : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → (∀ PP ∈ Lc.Q t, PP.under (𝓞 D.host.F) ≠ v) → ∀ j : Fin D.R.m, GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1)) := by
  intro D T Lc sc G μ₀ hL t v e he hv hQ j
  have hmu : Lc.mu t (j + 1) = Lc.mu0 ((j : ℕ) + 1) * Lc.xi t := rfl
  rw [hmu]
  refine unramAt_mul ?_ ?_
  · refine GlobalTheory.UnramOver.unramAt_of_unrAt D _ (Lc.C.mu0 j) (hL.mu0 j) v e he fun P hP => ?_
    refine (Lc.C.isMu0 j).unr P fun k hk => hv ?_
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
      rw [← hP]
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal
      rw [map_natCast]
      exact hk
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl hk'
    · exact Or.inr (Or.inl hk')
  · refine GlobalTheory.UnramOver.unramAt_of_unrAt D _ (Lc.xiH t) (hL.xi t) v e he fun P hP => ?_
    by_contra hn
    rcases (hL.Q_ram t P).1 hn with hq | ⟨P', hq, hc⟩
    · exact hQ P hq hP
    · exact hQ P' hq ((under_eq_of_isConjPl hc).trans hP)

end GlobalTheory.BotTripleUnr

end

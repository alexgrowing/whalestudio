import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
open NumberField IsDedekindDomain
open Classical

noncomputable section

namespace GlobalTheory.SqTop.TwVal

open Formalism.BasicNotions Formalism.IndefR.Links
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

variable {D : D7}

theorem under_eq_of_conj {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
  refine HeightOneSpectrum.ext ((P.under (𝓞 D.host.F)).isMaximal.eq_of_le (P'.under (𝓞 D.host.F)).isPrime.ne_top
    fun a ha => ?_)
  obtain ⟨c', h1, h2⟩ := h (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ha
  have hfix : star (algebraMap D.host.F D.host.E (a : D.host.F)) = algebraMap D.host.F D.host.E (a : D.host.F) :=
    (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = c' := RingOfIntegers.ext (h2.trans hfix).symm
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P'.asIdeal
  rwa [e]

theorem expAt_mul_unr {χ ξ : HChar D.host.E} {P : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (h : GlobalTheory.CMVal.ExpAt χ P n) (hξ : ξ.UnrAt P) : GlobalTheory.CMVal.ExpAt (χ * ξ) P n := by
  intro m
  have hm : ξ.LevelLe P m := hξ.levelLe m
  refine ⟨fun hx => (h m).1 ?_, fun hn => ((h m).2 hn).mul hm⟩
  have := hx.mul hm.inv
  rwa [mul_inv_cancel_right] at this

theorem expAt_mul_low {χ ξ : HChar D.host.E} {P : HeightOneSpectrum (𝓞 D.host.E)} {n k : ℕ}
    (h : GlobalTheory.CMVal.ExpAt χ P n) (hξ : ξ.LevelLe P k) (hk : k < n) : GlobalTheory.CMVal.ExpAt (χ * ξ) P n := by
  intro m
  refine ⟨fun hx => ?_, fun hn => ((h m).2 hn).mul (Model.levelLe_mono hξ (by omega))⟩
  by_contra c
  have a := Model.levelLe_mono hx (le_max_left m k)
  have b := Model.levelLe_mono hξ (le_max_right m k)
  have := a.mul b.inv
  rw [mul_inv_cancel_right] at this
  have := (h _).1 this
  omega

theorem isValChar_nu_twist {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) {s : ℕ} (hs : s ≤ halfRank D i j) :
    GlobalTheory.CMVal.IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl)
      ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) (nuH G t i j) := by
  have e : nuH G t i j = nuH G μ₀ i j * L.xiH t := by
    simp only [nuH, hL.xi_base, mul_one]
    rw [div_mul_eq_mul_div]
  obtain ⟨n, hn, hf⟩ := hL.xi_fin t
  obtain ⟨hu0, htr0, hinf0, hloc0⟩ := (Model.isValChar_nu hL G i j hs).1
  have unipotent_character_trivial_off_S0 : ∀ PP ∈ GlobalTheory.SqTop.twPl G t, PP.under (𝓞 D.host.F) ∉ G.pl.S0 := fun PP hPP hS => by
    simp only [GlobalTheory.SqTop.twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hPP
    have hQ : PP ∈ L.Q t := hPP.1.resolve_left hPP.2
    rcases G.pl.mem_S0_of_sum_eq.1 hS with h | h
    · exact G.pl.levelPlace_ne_basePlace t PP hQ h
    · exact hPP.2 (by rw [G.pl.w_Q t PP hQ h]; exact Finset.mem_image_of_mem _ hS)
  have ram : ∀ PP : HeightOneSpectrum (𝓞 D.host.E), ¬ (L.xiH t).UnrAt PP →
      PP.under (𝓞 D.host.F) ∈ S1 D ∨
        PP.under (𝓞 D.host.F) ∈ (GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F) := by
    intro PP hPP
    obtain ⟨P', hP', hu⟩ : ∃ P' ∈ L.Q t, P'.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) := by
      rcases (hL.Q_ram t PP).1 hPP with h | ⟨P', h, hc⟩
      · exact ⟨PP, h, rfl⟩
      · exact ⟨P', h, under_eq_of_conj hc⟩
    by_cases hW : P' ∈ G.pl.W0
    · left
      obtain ⟨u, hu', rfl⟩ := Finset.mem_image.1 hW
      rw [← hu, G.pl.under_w hu']
      exact (G.pl.mem_S0_of_sum_eq.1 hu').resolve_left fun h => G.pl.levelPlace_ne_basePlace t _ hP' ((G.pl.under_w hu').trans h)
    · right
      exact Finset.mem_image.2 ⟨P', by
        simp only [GlobalTheory.SqTop.twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union]; exact ⟨Or.inr hP', hW⟩, hu⟩
  rw [e]
  refine ⟨hu0.mul (HChar.isUnitary_of_order hn hf), htr0.mul (hL.xi_triv t), fun k => ?_,
    fun v P hP => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · rw [HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one (L.xiH t) hn hf k, mul_one]
    exact hinf0 k
  · obtain rfl : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hP
    obtain ⟨PP, hPP, hu⟩ := Finset.mem_image.1 hv
    have h0 := (hloc0 _ P hP).2 (Finset.notMem_empty _)
    rw [Model.expIn_condF, if_neg (hu ▸ unipotent_character_trivial_off_S0 PP hPP)] at h0
    exact (Model.levelLe_mono ((h0 0).2 le_rfl) (Nat.zero_le 1)).mul (hL.xi_tame t P)
  · obtain rfl : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hP
    have h0 := (hloc0 _ P hP).2 (Finset.notMem_empty _)
    by_cases hr : (L.xiH t).UnrAt P
    · exact expAt_mul_unr h0 hr
    · have hS1 := (ram P hr).resolve_right hv
      refine expAt_mul_low h0 (hL.xi_tame t P) ?_
      rw [Model.expIn_condF, if_pos (G.pl.mem_S0_of_sum_eq.2 (Or.inr hS1)), condExp,
        if_neg fun (e : P.under (𝓞 D.host.F) = G.pl.v0) => G.ch.basePlace_not_mem_chiGridBadPlaces (e ▸ hS1)]
      norm_num

end GlobalTheory.SqTop.TwVal

import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GalRepRankTwo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGaloisCharacterOfAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm7OfAutomorphicCsdTemperedPurity
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfRankOneUnitary
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GalClose

open GlobalTheory.CuspRep

theorem isSSRep_rankOne {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 1) k) : IsSSRep ρ := by
  intro W _
  by_cases h : W = ⊥
  · refine ⟨⊤, fun g v _ => Submodule.mem_top, ?_⟩
    rw [h]; exact isCompl_bot_top
  · have hW : W = ⊤ := by
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      have h0 : v 0 ≠ 0 := fun e => hv0 (funext fun j => by rw [Subsingleton.elim j 0, e]; rfl)
      refine eq_top_iff.2 fun u _ => ?_
      have : u = (u 0 / v 0) • v := funext fun j => by
        rw [Subsingleton.elim j 0, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h0]
      rw [this]; exact W.smul_mem _ hv
    refine ⟨⊥, fun g v hv => ?_, ?_⟩
    · rw [Submodule.mem_bot] at hv ⊢; rw [hv]; exact Matrix.mulVec_zero _
    · rw [hW]; exact isCompl_top_bot

theorem purity (hRP : GlobalTheory.Published.RegularAlgebraicPurity) (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D)
    (a : ℕ) (π : D.naut.CG a) (hr : D.naut.ralg π) : ∃ w₀ : ℂ, ∀ τ : D.host.E →+* ℂ,
      D.naut.infG π (τ.comp (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E).toRingEquiv.toRingHom) =
        (D.naut.infG π τ).map (w₀ - ·) := by
  have := host_isCMField D.host
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · haveI := P.cg.zero
    exact isEmptyElim π
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (P.cg.e a π).1
  have hmk : CG.mk π₀ = (P.cg.e a π).1 := hπ₀
  have hinf : ∀ τ, D.naut.infG π τ = (CG.mk π₀).infChar τ := fun τ => by
    rw [P.cg.inf, CGu.infChar, ← hmk]
  have hr₀ : (CG.mk π₀).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [hinf] at this
  obtain ⟨w₀, hw⟩ := (hRP D.host.E a ha1 π₀ hr₀).1
  refine ⟨(w₀ : ℂ), fun τ => ?_⟩
  have hc : τ.comp (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E).toRingEquiv.toRingHom = (starRingEnd ℂ).comp τ :=
    RingHom.ext fun x => GlobalTheory.SplitRowProbe.conj_sqrt D.host τ x
  rw [hc, hinf, hinf, hw]

theorem rankOne (hPr : GlobalTheory.NRows.Hypotheses₂) (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc)
    (π : D.naut.CG 1) (hr : D.naut.ralg π) :
    ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i)),
      Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i)))) ∧ IsSSRep ρ ∧
      (∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
        D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG π w) ((1 - ((1 : ℕ) : ℝ)) / 2) ∧ D.naut.tempered (D.naut.locG π w)) ∧
      (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧
        (∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.jumpsInf i π τ) ∧
        D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG π w) ((1 - ((1 : ℕ) : ℝ)) / 2)) := by
  have h0 : (1 - ((1 : ℕ) : ℝ)) / 2 = 0 := by norm_num
  obtain ⟨ρ, hc, h1, h2⟩ := GlobalTheory.T.exists_galois_character_of_algebraic hPr.fin hPr.art hPr.chA hPr.chP hL D P i π 0 (fun τ z hz => by
    obtain ⟨n, hn⟩ := ((D.naut.ralg_def π).1 hr τ).2 z hz
    exact ⟨n, by rw [hn]; simp⟩)
  refine ⟨ρ, hc, isSSRep_rankOne ρ, fun w hw => ⟨by rw [h0]; exact h1 w hw, ?_⟩, fun w hw => ⟨(h2 w hw).1, fun τ hτ => ?_, by rw [h0]; exact (h2 w hw).2.1⟩⟩
  · exact GlobalTheory.RowTie.tempered_of_rank_le_one D P.T (GlobalTheory.TempClose.rankOneUnitary hPr.fin hL D P) 1 π le_rfl w
  · apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [(h2 w hw).2.2 τ hτ, D.naut.jumpsInf_def i π τ hr]
    simp

theorem main : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), Formalism.MainNotions.SumRepresentations.adm2 D := by
  intro hPr hL D P i
  refine ⟨fun a ha π hc hr => ?_, fun a π hr => purity hPr.clo hL D P a π hr, fun χ s hs => ?_⟩
  · rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · obtain rfl : a = 1 := by omega
      exact rankOne hPr hL D P i π hr
    · exact GlobalTheory.GalFirstClause.galRep_rankTwo hPr.fin hPr.gal hPr.car hPr.clo hL D P i a ha2 π hc hr
  · exact GlobalTheory.T.exists_galois_character_of_algebraic hPr.fin hPr.art hPr.chA hPr.chP hL D P i χ s hs

end GlobalTheory.GalClose

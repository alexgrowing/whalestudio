import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiscreteSeriesModelOfOrthonormalBasisCarta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPermOfCardFalse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridParamRegularCardMinusCount

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SignedHC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepRows

theorem exists_dsModel_cart {D : D7} (hDS : GlobalTheory.Published.DiscreteSeriesUpqExists) {V : HSp D} (hV : V.SigOK)
    (S : D.what₂.Tau → SPar) (O C : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hS : ∀ τ, SignedHC.IsRegular (S τ)) (hc : ∀ τ, (S τ).card = V.rank)
    (hm : ∀ τ, SignedHC.nMinus (S τ) = (V.sig (tauE D τ)).2)
    (hP : ∀ τ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam)
    (h : ∀ τ, ∃ ε : Fin V.rank → Bool, (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε ∧ C τ * O τ = O τ * Formalism.REAL.Jm ε) :
    ∃ M : DSModel V S, cart M = C := by

  have hperm : ∀ τ, ∃ σ : Equiv.Perm (Fin V.rank), ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε ∧
      ((O τ).submatrix id σ)ᴴ * gramAt D V τ * (O τ).submatrix id σ = Formalism.REAL.Jm ε ∧
      C τ * (O τ).submatrix id σ = (O τ).submatrix id σ * Formalism.REAL.Jm ε :=
    fun τ => GlobalTheory.GridJoin.exists_perm_onb hV τ (hS τ) (hc τ) (hm τ) (h τ)
  choose σ lam ε hEn hGr hCa using hperm
  obtain ⟨M, hMc, -⟩ := GlobalTheory.dsModel_of_onb_cart D hDS V S (fun τ => (O τ).submatrix id (σ τ)) C
    (fun τ => ⟨lam τ, ε τ, hEn τ, hP τ (lam τ) (ε τ) (hEn τ), hGr τ⟩) (fun τ => ⟨ε τ, hGr τ, hCa τ⟩)
  exact ⟨M, hMc⟩

private theorem exists_int_eq_half_add_of_mem_parPi (G : GlobalTheory.SignedHC.GridData) (hs : Odd G.s) (i : ℕ) (x : ℚ) (b : Bool)
    (hx : (x, b) ∈ G.parPi i) : ∃ z : ℤ, x = 1 / 2 + z := by
  rcases GlobalTheory.SignedHC.GridData.mem_parPi.1 hx with ⟨l, -, hl⟩ | ⟨hc, -⟩ | ⟨l, -, -, hl, -⟩
  · simp only [Prod.mk.injEq] at hl
    refine ⟨G.v 2 + ((G.m : ℤ) + 1 - l) * G.ga, ?_⟩
    rw [hl.1, GlobalTheory.SignedHC.GridData.a]
    push_cast
    ring
  · dsimp only at hc
    obtain ⟨j, -, -, hj⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 hc
    refine ⟨G.v j - 1, ?_⟩
    rw [hj, GlobalTheory.SignedHC.GridData.vHalf]
    push_cast
    ring
  · dsimp only at hl
    obtain ⟨w, hw⟩ := hs
    obtain ⟨z, hz⟩ := GlobalTheory.SignedHC.inCoset_block _ _ x hl
    refine ⟨G.cen l + w + z, ?_⟩
    have hlen : ((G.s - 1 : ℕ) : ℚ) = 2 * w := by
      rw [hw, Nat.add_sub_cancel]; push_cast; ring
    rw [hz, hlen]
    push_cast
    ring

theorem isHCParam_parPi (D : D7) (C : ℝ) (i : ℕ) (τ : D.what₂.Tau) {n : ℕ} (lam : Fin n → ℝ) (ε : Fin n → Bool)
    (hn : n = rankP D i) (hE : IsEnum ((num D C τ).parPi i) lam ε) : Formalism.QuantumDeterminants.IsHCParam lam := by
  obtain ⟨hanti, q, hq, hS⟩ := hE
  refine ⟨hanti, fun a => ?_⟩
  have hmem : (q a, ε a) ∈ (num D C τ).parPi i := by
    rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
  obtain ⟨z, hz⟩ := exists_int_eq_half_add_of_mem_parPi (num D C τ) (odd_sLen D) i (q a) (ε a) hmem
  obtain ⟨k, hk⟩ := even_rankP D i
  refine ⟨z - k + 1, ?_⟩
  rw [hq a, hz, hn, hk]
  push_cast
  ring

theorem coreModels_of_upq (hDS : GlobalTheory.Published.DiscreteSeriesUpqExists) : CoreModels := by
  intro D _ T L μ0 _ sc G W M _ i hi
  have hin : (Node.core i).InRange D.R.m := hi
  obtain ⟨hrank, hsig, hsg, -⟩ := G.isV hin (fun j h => by cases h)
  have hg : 0 < (gap D sc.cGap) := lt_of_le_of_lt (Nat.zero_le _) (sLen_lt_gap D sc.cGap)
  have hs1 : 1 ≤ sLen D := by unfold sLen; omega
  refine exists_dsModel_cart hDS hsig (Node.par D sc.cGap (.core i)) (W.onb (.core i)) (W.cart (.core i))
    (fun τ => ?_) (fun τ => ?_) (fun τ => ?_) (fun τ lam ε hE => ?_) (W.onb_is (.core i) hin)
  · exact GlobalTheory.PiCounts.isRegular_parPi (num_nearMid D sc.cGap τ) hs1 (sLen_lt_gap D sc.cGap) hi
  · exact (GlobalTheory.PiCounts.card_parPi (num_nearMid D sc.cGap τ) hs1 (sLen_lt_gap D sc.cGap) hi).trans
      ((num_ranks D sc.cGap τ i 0).2.1.trans hrank.symm)
  · show nMinus ((num D sc.cGap τ).parPi i) = _
    rw [GlobalTheory.PiCounts.nMinus_parPi hg i, hsg (tauE D τ)]
    rfl
  · exact isHCParam_parPi D sc.cGap i τ lam ε hrank hE

theorem coreModels : GlobalTheory.FunPr.Hypotheses₂ → CoreModels := by
  intro hPr
  exact coreModels_of_upq hPr.discreteSeriesUpqExists

end GlobalTheory.SepRows

end

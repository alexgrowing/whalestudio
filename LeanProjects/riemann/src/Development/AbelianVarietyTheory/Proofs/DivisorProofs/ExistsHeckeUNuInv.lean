import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHCharN
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatHeckeCharacterTrivialCongruentUnitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterTrivialSubfieldKillsIdeleNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterUnramifiedInertKillsUnitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRanksSumLeTwoExponentAddCentreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuInvHasInfinityTypeCmTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuInvUnramifiedOverInertPrimeStatement

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.BottomNu

theorem exists_heckeU_nu_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m), ∃ χ : HeckeU D (botBig D i j + botSmall D i j), (∀ x, χ.f x = (nuH G μ₀ i j)⁻¹.1 (finIdl D x)) ∧ ∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χ.n τ := by
  intro D T L sc μ₀ hL G i j
  have hu : (nuH G μ₀ i j)⁻¹.IsUnitary := by
    have h := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (chrEq_nu G μ₀ i j hL)
    intro x
    have e : (((nuH G μ₀ i j)⁻¹).1 x : ℂˣ) = ((nuH G μ₀ i j).1 x)⁻¹ := rfl
    rw [e, Units.val_inv_eq_inv_val, norm_inv, h x, inv_one]
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have htriv : (nuH G μ₀ i j)⁻¹.TrivOn D.host.F := by
    have h1 := (L.C.isMu0 j).triv
    have h2 := G.ch.triv (D.R.m - i) hm.1 hm.2
    have h3 : (L.xiH μ₀).TrivOn D.host.F := hL.xi_triv μ₀
    exact (((h1.mul h3).mul h2.inv)).inv
  have hp : ∀ τ, Even (2 * ((GlobalTheory.ChiGrid.num D sc.cGap τ).e (j + 1) + GlobalTheory.ChiGrid.cen D sc.cGap τ (D.R.m - i)) -
      ((botBig D i j + botSmall D i j : ℕ) : ℤ)) := by
    intro τ
    obtain ⟨h1, h2, -⟩ := ranks_exact D i j
    obtain ⟨u, hu⟩ := D.R.t_odd
    obtain ⟨v, hv⟩ := odd_sLen D
    have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
    obtain ⟨w, hw⟩ : ∃ w : ℕ, botBig D i j + botSmall D i j = 2 * w := ⟨(botBig D i j + botSmall D i j) / 2, by omega⟩
    refine ⟨(GlobalTheory.ChiGrid.num D sc.cGap τ).e (j + 1) + GlobalTheory.ChiGrid.cen D sc.cGap τ (D.R.m - i) - w, ?_⟩
    rw [hw]; push_cast; ring
  have hc : ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) →
      (nuH G μ₀ i j)⁻¹.1 (finIdl D u) = 1 := by
    obtain ⟨M, hM, h⟩ := GlobalTheory.T.exists_nat_heckeCharacter_trivial_congruent_units D.host.E (nuH G μ₀ i j)⁻¹
    refine ⟨M, hM, fun u hu ⟨s, hs, e⟩ => h _ (GlobalTheory.Mem.Col2.SplitChar.finIdl_unit hu)
      (fun w => by rw [GlobalTheory.Mem.Col2.SplitChar.finIdl_fst]; rfl) fun P => ?_⟩
    rw [GlobalTheory.Mem.Col2.SplitChar.vl_sub_one, e, map_mul, GlobalTheory.Mem.Col2.SplitChar.vl_nat,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact mul_le_of_le_one_right' (GlobalTheory.Mem.Col2.SplitChar.vl_le hs P)
  exact ⟨GlobalTheory.SplitCharGen.ofHChar _ (nuH G μ₀ i j)⁻¹ _ hu (GlobalTheory.T.squareNu_inv_hasInfinityType_cmType hL G i j) hp hc
    (GlobalTheory.T.heckeCharacter_trivial_subfield_kills_idele_norms D _ htriv (GlobalTheory.T.exists_nat_heckeCharacter_trivial_congruent_units D.host.E _)) (GlobalTheory.T.heckeCharacter_unramified_inert_kills_units D _ fun P hP => GlobalTheory.T.squareNu_inv_unramified_over_inert_prime hL G i j P hP), fun x => rfl, fun τ => GlobalTheory.T.bottomRanks_sum_le_two_exponent_add_centre D sc.cGap i j τ⟩

end GlobalTheory.BottomNu

import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitPowTendstoZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterNormEqPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosOfSocleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormLtOneOfPowTendstoZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentLtOfPrecedesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdLeRevEqProdGeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetAntitoneEnumerationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AntitoneWeightedSumZeroStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.TemperedCore

theorem exists_lFactors_unitary : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSocleGL k → Zl.CasselmanNecTemp k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible → IsTemperedCoeff π → IsL 𝔪 π → ∃ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x ∧ ∀ (a : Fin h) (t : kˣ) (c : ℂ), Zl.ScalarBy (x a) t c → ‖c‖ = 1 := by
  intro k _ _ _ _ hSoc hCas hSeg 𝔪 N V _ _ π hN hsm hirr htemp hL
  have hy : ∀ Δ : Segment k, ∃ y : IrrGL k, IsLSeg Δ y.rep := fun Δ => by
    obtain ⟨ρ, hρ⟩ := hSeg Δ
    exact ⟨IrrGL.of ρ.ρ ρ.smooth ρ.irr, hρ.of_equiv (IrrGL.equivOf _ _ _)⟩
  choose y hyL using hy
  have hypos : ∀ Δ : Segment k, 0 < (y Δ).1 := fun Δ => by
    rw [← (hyL Δ).deg_eq]
    exact Nat.mul_pos Δ.len_pos Δ.d_pos
  have hs : ∀ Δ : Segment k, ∃ s : ℝ, ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy (y Δ) t c →
      ‖c‖ = nabs k t ^ (((y Δ).1 : ℝ) * s) := fun Δ => GlobalTheory.T.central_character_norm_eq_pow k (y Δ) (hypos Δ)
  choose f hf using hs
  obtain ⟨h, Δ, hΔ, hanti, hnp⟩ := GlobalTheory.T.multiset_antitone_enumeration 𝔪 f Segment.Precedes (fun a b hab =>
    GlobalTheory.T.exponent_lt_of_precedes_of_isLSeg k a b (y a) (y b) (f a) (f b) (hyL a) (hyL b) (hf a) (hf b) hab)
  let x : Fin h → IrrGL k := fun a => y (Δ a)
  have hLF : LFactors 𝔪 x := ⟨Δ, ⟨hΔ, hnp⟩, fun i => hyL _⟩
  have hsumdeg : ∀ {h' : ℕ} (Δ' : Fin h' → Segment k) (x' : Fin h' → IrrGL k),
      Finset.univ.val.map Δ' = 𝔪 → (∀ i, IsLSeg (Δ' i) (x' i).rep) →
      ∑ a, (x' a).1 = (𝔪.map Segment.deg).sum := by
    intro h' Δ' x' hm hx'
    rw [← hm, Multiset.map_map]
    exact Finset.sum_congr rfl fun a _ => ((hx' a).deg_eq).symm
  have hdeg : ∑ a, (x a).1 = N := by
    obtain ⟨h', x', hd', ⟨Δ', ⟨hΔ', -⟩, hx'⟩, -⟩ := hL
    rw [hsumdeg Δ x hΔ (fun i => hyL _), ← hsumdeg Δ' x' hΔ' hx', hd']
  have hdrev : ∑ a, (x (Fin.rev a)).1 = N := by
    rw [← hdeg]
    exact Equiv.sum_comp Fin.revPerm (fun a => (x a).1)
  have hsoc := hSoc 𝔪 h N x hdrev hLF π hL
  have hjm := GlobalTheory.T.jacquet_multiplicity_pos_of_socle k h N (x ∘ Fin.rev) hdrev π hsm (fun a => hypos _) hsoc
  have hW := hCas N π hN hsm hirr htemp h (x ∘ Fin.rev) hdrev (fun a => hypos _) hjm
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_unit_pow_tendsto_zero' k
  have ht1 : nabs k t < 1 := GlobalTheory.T.norm_lt_one_of_pow_tendsto_zero k t ht
  have ht0 : 0 < nabs k t := by
    have h0 : (MeasureTheory.distribHaarChar k t : NNReal) ≠ 0 := fun h0 => by
      have := map_mul (MeasureTheory.distribHaarChar k) t t⁻¹
      simp [h0] at this
    exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 h0)
  have hge : ∀ r : ℝ, nabs k t ^ r ≤ 1 → 0 ≤ r := fun r hr => by
    by_contra hneg
    exact absurd hr (not_le.2 (Real.one_lt_rpow_of_pos_of_lt_one_of_neg ht0 ht1 (not_le.1 hneg)))
  choose c hc using fun a => GlobalTheory.T.central_character_exists k (x a) t
  obtain ⟨hpart, htot⟩ := hW t ht (c ∘ Fin.rev) (fun i => hc _)
  let e : Fin h → ℝ := fun i => f (Δ i)
  let d : Fin h → ℝ := fun i => ((x i).1 : ℝ)
  have hnorm : ∀ i, ‖c i‖ = nabs k t ^ (d i * e i) := fun i => hf (Δ i) t (c i) (hc i)
  have hprod : ∀ S : Finset (Fin h), ∏ i ∈ S, ‖c i‖ = nabs k t ^ (∑ i ∈ S, d i * e i) := fun S => by
    rw [Real.rpow_sum_of_pos ht0]
    exact Finset.prod_congr rfl fun i _ => hnorm i
  have hsum : ∑ i, d i * e i = 0 := by
    have h1 : ∏ i, ‖c i‖ = 1 := by
      rw [← htot]
      exact (Equiv.prod_comp Fin.revPerm (fun i => ‖c i‖)).symm
    rw [hprod] at h1
    refine le_antisymm ?_ (hge _ h1.le)
    have := hge (-∑ i, d i * e i) (by rw [Real.rpow_neg ht0.le, h1, inv_one])
    linarith
  have htail : ∀ j : Fin h, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i := by
    intro j
    by_cases hj : (Fin.rev j).val + 1 < h
    · have h1 := hpart (Fin.rev j) hj
      have h2 := GlobalTheory.T.prod_le_rev_eq_prod_ge h (fun i => ‖c i‖) (Fin.rev j)
      rw [Fin.rev_rev] at h2
      have h3 : ∏ i ∈ Finset.univ.filter (fun i => i ≤ Fin.rev j), ‖(c ∘ Fin.rev) i‖ =
          ∏ i ∈ Finset.univ.filter (fun i => j ≤ i), ‖c i‖ := h2
      rw [h3, hprod] at h1
      exact hge _ h1
    · have hj0 : j.val = 0 := by
        have := j.isLt
        rw [Fin.val_rev] at hj
        omega
      have hf' : Finset.univ.filter (fun i => j ≤ i) = Finset.univ := by
        ext i
        simp [Fin.le_def, hj0]
      rw [hf', hsum]
  have he := GlobalTheory.T.antitone_weighted_sum_zero h d e (fun i => Nat.cast_pos.2 (hypos (Δ i))) hanti hsum htail
  refine ⟨h, x, hdeg, hLF, fun a t' c' hsc => ?_⟩
  have h1 := hf (Δ a) t' c' hsc
  have h2 : f (Δ a) = 0 := he a
  rw [h1, h2, mul_zero, Real.rpow_zero]

end GlobalTheory.CompanionTheory.TemperedCore

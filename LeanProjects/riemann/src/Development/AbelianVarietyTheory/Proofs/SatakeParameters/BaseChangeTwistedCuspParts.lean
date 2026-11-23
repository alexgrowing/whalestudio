import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowModelOfPointModels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TieAutAndSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularDefinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqOfMapEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.EigStrCalc

theorem odd_rank (R : Ranks) : Odd R.r := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have h2 := R.two_le_m
  exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩

theorem isSplitPl_of_under (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E))
    (h : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F))) : IsSplitPl D.host w := by
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := h
  rw [GlobalTheory.Mem.GoodPlace.isSplitPl_iff]
  by_cases hw : w = P
  · subst hw
    exact ⟨Q, hPQ, HeightOneSpectrum.ext (by simpa [HeightOneSpectrum.under, Ideal.under] using hQ)⟩
  · exact ⟨P, hw, HeightOneSpectrum.ext (by simpa [HeightOneSpectrum.under, Ideal.under] using hP)⟩

theorem normV_eq_absNorm {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) :
    normV w = Ideal.absNorm w.asIdeal := by
  simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.EigStrCalc

namespace GlobalTheory.EigStrCalc

theorem inv_block (q : ℕ) (z : ℂ) (t : ℕ) :
    (((List.range t : List ℕ) : Multiset ℕ).map
        fun k : ℕ => z⁻¹ * (q : ℂ) ^ (((((t : ℝ) - 1) / 2 - k : ℝ)) : ℂ)).map (fun a : ℂ => a⁻¹) =
      GlobalTheory.DownLift.str q z t := by
  unfold GlobalTheory.DownLift.str
  have hr : (Multiset.range t) = (Multiset.range t).map (fun k => t - 1 - k) := by
    rw [← Finset.range_val, ← Finset.image_val_of_injOn]
    · rw [show (Finset.range t).image (fun k => t - 1 - k) = Finset.range t from ?_]
      ext k; simp only [Finset.mem_image, Finset.mem_range]; constructor
      · rintro ⟨j, hj, rfl⟩; omega
      · intro hk; exact ⟨t - 1 - k, by omega, by omega⟩
    · intro a ha b hb h; simp only [Finset.coe_range, Set.mem_Iio] at ha hb; simp only at h; omega
  rw [Multiset.map_map]
  conv_rhs => rw [hr, Multiset.map_map]
  have hcoe : ((List.range t : List ℕ) : Multiset ℕ) = Multiset.range t := rfl
  rw [hcoe]
  refine Multiset.map_congr rfl fun k hk => ?_
  rw [Multiset.mem_range] at hk
  simp only [Function.comp_apply]
  rw [mul_inv, inv_inv, ← Complex.cpow_neg]
  congr 2
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

end GlobalTheory.EigStrCalc

namespace GlobalTheory.EigStrCalc

theorem unr_of_speh {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)
    (θ : A.CG 1) (t : ℕ) (ht : 1 ≤ t) (w : PlE H) (h : A.unr (spehLoc N A ⟨1, θ, t⟩ w)) :
    A.unr (A.locG θ w) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  unfold spehLoc at h
  simp only at h
  rw [List.range_succ_eq_map] at h
  exact (A.unr_tw _ _).1 ((A.unr_sum _ _).1 h).1

theorem strCalc : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (Q P0 : D.naut.AV i) (Sig : List (Part D.naut.CG)), D.naut.ptV i Q = some x → D.naut.ptV i P0 = some x → IsCuspIso D.nd D.naut Sig → IsBCV D.nd D.naut i P0 (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) → ∀ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → w ∉ D.nd.S i → w ∉ D.nd.Q i → D.naut.unr (D.naut.locV i Q w) → ∀ z : ℂ, D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {z⁻¹} → ∃ B' : Multiset ℂ, (D.naut.frobEig (D.naut.locV i Q w)).map (fun a : ℂ => a⁻¹) = B' + GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) z D.R.t ∧ ∀ a ∈ B', ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2) := by
  intro hAF hL D P h41 h7 _ i x Q P0 Sig hQ hP0 hSig hB w hsplit hS hQw hunr z hz
  have hsp : IsSplitPl D.host w := isSplitPl_of_under D w hsplit
  obtain ⟨π, rfl⟩ := hSig
  have e1 : D.naut.locV i Q w = D.naut.locV i P0 w :=
    (((h41 i).2.1 Q P0 (by rw [hQ]; exact Option.some_ne_none x) (hQ.trans hP0.symm)).2 w hS hQw).1 hsp
  have e2 := hB.2.2.2.1 w hsp
  have e3 : isoLoc D.nd D.naut (twistIso D.nd D.naut ([⟨D.R.r, π, 1⟩] ++ [muPart D.nd D.naut i]) D.naut.etaTinv) w =
      D.naut.lpSum (D.naut.locG (D.naut.tw π D.naut.etaTinv) w)
        (spehLoc D.nd D.naut ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ w) := by
    have : spehLoc D.nd D.naut ⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ w = D.naut.locG (D.naut.tw π D.naut.etaTinv) w := by
      simp [spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]
    rw [← this]
    exact congrArg _ (D.naut.lpSum_zero _)
  have eV : D.naut.locV i Q w = D.naut.lpSum (D.naut.locG (D.naut.tw π D.naut.etaTinv) w)
      (spehLoc D.nd D.naut ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ w) := by
    rw [e1, ← e2, e3]
  rw [eV] at hunr
  obtain ⟨ha, hb⟩ := (D.naut.unr_sum _ _).1 hunr
  have ht : 1 ≤ D.R.t := D.R.t_odd.pos
  have hθ := unr_of_speh D.naut _ D.R.t ht w hb
  obtain ⟨-, hblk⟩ := GlobalTheory.RowModelRoad.frobEig_block D.naut _ D.R.t w z⁻¹ hθ hz
  refine ⟨(D.naut.frobEig (D.naut.locG (D.naut.tw π D.naut.etaTinv) w)).map (fun a : ℂ => a⁻¹), ?_, ?_⟩
  · rw [eV, D.naut.frobEig_sum _ _ ha hb, Multiset.map_add, hblk, ← normV_eq_absNorm, inv_block]
  ·
    obtain ⟨hTie, -⟩ := GlobalTheory.AutomorphismSplitting.tieAut_and_split hAF hL D P
    have hEta : GlobalTheory.LocalInv.EtaType D.nd D.naut := by
      refine ⟨hTie.1.1, fun τ z hz => ?_⟩
      rcases (hTie.2.1 τ).1 with h | h <;> rw [h, Multiset.mem_singleton] at hz <;> subst hz
      · exact ⟨0, by push_cast; ring⟩
      · exact ⟨-1, by push_cast; ring⟩
    have hmem : (⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ : Part D.naut.CG) ∈
        twistIso D.nd D.naut ([⟨D.R.r, π, 1⟩] ++ [muPart D.nd D.naut i]) D.naut.etaTinv := by
      simp [twistIso]
    obtain ⟨hcsd, hralg⟩ := GlobalTheory.LocalInv.part_alg D.nd D.naut hEta (GlobalTheory.LocalInv.weightRegular_definite D) i P0 _ hB _ hmem
      (odd_rank D.R) odd_one
    have htemp := h7 D.R.r _ (odd_rank D.R).pos hcsd hralg w
    have hdE := D.naut.locG_dim D.naut.etaT w
    have huE := D.naut.etaT_unr w
    obtain ⟨c, hc⟩ := Multiset.card_eq_one.mp ((D.naut.frobEig_card _ huE).trans hdE)
    have hcn : ‖c‖ = 1 := (D.naut.tempered_unr _ huE).1 (hTie.2.2.1 w) c (by rw [hc]; exact Multiset.mem_singleton_self c)
    rw [D.naut.locG_tw] at htemp
    have hu2 := D.naut.unr_char _ _ hdE ha huE
    have h2 := (D.naut.tempered_unr _ hu2).1 htemp
    rw [D.naut.frobEig_char _ _ c ha huE hdE hc] at h2
    intro a haB
    obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.mp haB
    have h3 := h2 (α * c) (Multiset.mem_map_of_mem _ hα)
    rw [norm_mul, hcn, mul_one] at h3
    rw [norm_inv, h3, inv_one]
    have hq : (1 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := by
      have : Ideal.absNorm w.asIdeal ≠ 0 := fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
    refine Real.one_le_rpow hq ?_
    have : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (odd_rank D.R).pos
    linarith

end GlobalTheory.EigStrCalc

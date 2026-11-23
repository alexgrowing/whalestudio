import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsSeparateQuotientGenericFibreDescends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionsPolynomialGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivOfGlobalSectionPowNumEquivMultiple
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KodairaLemma

theorem lineBundleGlobalSectionsDim_eq_zero_of_isEmpty (k : Type) [Field k] {Z : Scheme.{0}} [Algebra k Γ(Z, ⊤)] [IsEmpty Z]
    (L : LB Z) : lbH0 k L = 0 := by
  have e : (⊤ : Z.Opens) = ⊥ := Opens.ext (Set.eq_empty_of_isEmpty _)
  have : Subsingleton Γ(Z, ⊤) := by rw [e]; infer_instance
  have : Subsingleton L.Sec := Module.subsingleton Γ(Z, ⊤) _
  have : Subsingleton (coh (twist (structureModule Z) L) 0) := (cohZeroTwistEquiv L).toEquiv.subsingleton
  exact Module.finrank_zero_of_subsingleton

theorem isEmpty_zeroScheme {X : Scheme.{0}} [IsIntegral X] (hd : topologicalKrullDim X ≤ 0) {L : LB X}
    (hL : L.IsLB) (t : L.Sec) (ht : genericPoint X ∈ nonzeroLocus t) :
    IsEmpty (GlobalTheory.ThickeningDetermines.secIdeal hL t).subscheme := by
  refine ⟨fun z => ?_⟩
  have hx : (GlobalTheory.ThickeningDetermines.secIdeal hL t).subschemeι z ∈
      ((GlobalTheory.ThickeningDetermines.secIdeal hL t).support : Set X) := by
    rw [← (GlobalTheory.ThickeningDetermines.secIdeal hL t).range_subschemeι]; exact ⟨z, rfl⟩
  rw [coe_support_secIdeal] at hx
  set x := (GlobalTheory.ThickeningDetermines.secIdeal hL t).subschemeι z
  have hmax := Order.krullDim_nonpos_iff_forall_isMax.1
    (show Order.krullDim (IrreducibleCloseds X) ≤ 0 from hd)
  have hst : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  let A : IrreducibleCloseds X := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let B : IrreducibleCloseds X := ⟨closure {genericPoint X}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hAB : A ≤ B := specializes_iff_closure_subset.1 hst
  have hBA : B ≤ A := hmax A hAB
  have hts : x ⤳ genericPoint X := specializes_iff_closure_subset.2 hBA
  exact hx (hts.mem_open (nonzeroLocus t).isOpen ht)

open GlobalTheory.ThickeningDetermines (secIdeal)
open GlobalTheory.QuotSep

theorem exists_nsmul_cls_eq_add_toPic_of_isBig : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), IsProjOver p → ∀ (M A : LB X) (hM : letI := algebraΓOfHom p; IsBig k M) (hA : IsAmpleLB A), ∃ (a : ℕ) (D : CartierDiv X), 0 < a ∧ D.Eff ∧ a • cls M (letI := algebraΓOfHom p; hM.isLB) = cls A hA.isLB + toPic D := by
  intro k _ _ X _ p hp M A hM hA
  letI := algebraΓOfHom p
  have hp' : IsProjOver (strHom k X) := by rwa [strHom_eq (f := p) fun _ => rfl]
  have := isNoetherian_of_isProjOver hp'
  suffices h : ∃ a : ℕ, 0 < a ∧ ∃ (N : LB X) (hN : N.IsLB),
      cls N hN = a • cls M hM.isLB - cls A hA.isLB ∧ HasNonzeroSec N by
    obtain ⟨a, ha, N, hN, e, hs⟩ := h
    obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 hs
    refine ⟨a, divOfSec hN s hs, ha, GlobalTheory.PairStep.eff_divOfSec_of_sec hN s hs, ?_⟩
    rw [(presents_divOfRatSec hN (isRatSec_ratOfSec s hs)).toPic_eq, e]
    abel
  obtain ⟨q, hq, hq'⟩ := hA.exists_hasNonzeroSec (LB.isLB_triv X)
  have hAq : IsAmpleLB (lbPow A q) := (isAmpleLB_pow_iff hA.isLB hq).2 hA
  obtain ⟨r, -, hr'⟩ := hAq.exists_hasNonzeroSec (isLB_dual hA.isLB)
  have hP : (lbPow (lbPow A q) r).IsLB := isLB_lbPow hAq.isLB r
  have hPs : HasNonzeroSec (lbPow (lbPow A q) r) :=
    (hq' _ hAq.isLB (by rw [cls_triv, zero_add, cls_lbPow hA.isLB])).pow hAq.isLB r
  have hE := isLB_tens (isLB_dual hA.isLB) hP
  have hEs : HasNonzeroSec (tens (dual A) (lbPow (lbPow A q) r)) :=
    hr' _ hE (by rw [cls_tens (isLB_dual hA.isLB) hP, cls_lbPow hAq.isLB])
  obtain ⟨t, ht⟩ := hasNonzeroSec_iff.1 hPs
  have ht0 : t ≠ 0 := sec_ne_zero_of_mem ht
  letI := algebraΓAlong k (secIdeal hP t).subschemeι
  obtain ⟨m, hm, hlt⟩ : ∃ m : ℕ, 0 < m ∧
      lbH0 k ((lbPow M m).pull (secIdeal hP t).subschemeι) < lbH0 k (lbPow M m) := by
    obtain ⟨D, hD, c, hc, hfreq⟩ := hM.growth
    rcases D with _ | d
    · have hd0 : topologicalKrullDim X ≤ 0 := by rw [hD]; rfl
      haveI := isEmpty_zeroScheme hd0 hP t ht
      obtain ⟨m, hcm, hm⟩ := (hfreq.and_eventually (eventually_ge_atTop 1)).exists
      refine ⟨m, hm, ?_⟩
      rw [lineBundleGlobalSectionsDim_eq_zero_of_isEmpty]
      have h0 : (0 : ℝ) < lbH0 k (lbPow M m) := hc.trans_le (by simpa using hcm)
      exact_mod_cast h0
    · set ι := (secIdeal hP t).subschemeι
      have hMι := LB.isLB_pull hM.isLB ι
      obtain ⟨C, hC⟩ := GlobalTheory.exists_hdim_twist_lbPow_zero_le k _ (isProjOver_along hp' ι) d (M.pull ι) hMι
        (structureModule _) (by rw [QCoh.suppDim_structureModule]; exact dim_zeroScheme_le hP ht0 hD.le)
      have hev : ∀ᶠ m : ℕ in atTop, (C : ℝ) * 2 ^ d < c * m :=
        (tendsto_natCast_atTop_atTop.const_mul_atTop hc).eventually_gt_atTop _
      obtain ⟨m, h₁, h₂, h₃⟩ := (hfreq.and_eventually (hev.and (eventually_ge_atTop 1))).exists
      refine ⟨m, h₃, ?_⟩
      have e₂ : lbH0 k ((lbPow M m).pull ι) = lbH0 k (lbPow (M.pull ι) m) :=
        lineBundleGlobalSectionsDim_congr_picardClass (LB.isLB_pull (isLB_lbPow hM.isLB m) ι) (isLB_lbPow hMι m)
          ((cls_eq_iff _ _).2 (lbIso_lbPow_pull hM.isLB ι m)).symm
      rw [e₂]
      by_contra hle
      push_neg at hle
      have hb : (lbH0 k (lbPow (M.pull ι) m) : ℝ) ≤ C * ((m : ℝ) + 1) ^ d := by exact_mod_cast hC m
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h₃
      have hm2 : ((m : ℝ) + 1) ^ d ≤ 2 ^ d * (m : ℝ) ^ d := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) d
      have hle' : (lbH0 k (lbPow M m) : ℝ) ≤ lbH0 k (lbPow (M.pull ι) m) := by exact_mod_cast hle
      have hmd : (0 : ℝ) < (m : ℝ) ^ d := pow_pos (by linarith) d
      have h₄ := mul_lt_mul_of_pos_right h₂ hmd
      have h₅ := mul_le_mul_of_nonneg_left hm2 (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
      push_cast at h₁
      rw [pow_succ] at h₁
      nlinarith
  have hB := isLB_lbPow hM.isLB m
  have e₁ := globalSections_dim_le_div_add_restriction hp' hP hB ht0
  have hpos : 0 < lbH0 k (LB.div (lbPow M m) (lbPow (lbPow A q) r)) := by omega
  have hD := LB.isLB_div hB hP
  refine ⟨m, hm, _, isLB_tens hD hE, ?_, (lineBundleHasNonzeroSection_of_globalSectionsDim_pos hpos).tens hEs hD hE⟩
  rw [cls_tens hD hE, cls_div hB hP, cls_lbPow hM.isLB, cls_tens (isLB_dual hA.isLB) hP,
    cls_dual hA.isLB, cls_lbPow hAq.isLB, cls_lbPow hA.isLB]
  abel

end GlobalTheory.KodairaLemma

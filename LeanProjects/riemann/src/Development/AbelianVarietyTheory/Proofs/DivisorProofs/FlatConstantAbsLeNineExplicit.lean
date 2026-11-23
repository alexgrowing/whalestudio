import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodWeightAntitoneGapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortLatticeSpanningSetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortGeneratorsOfShortSpanningFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormComponentAddLeOfGramFrameStatement
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.ShortGenComp

set_option maxHeartbeats 1000000 in

theorem short_gen_comp : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 10 * Lb → ∀ Z, ∃ (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) (abelian₂ : ℝ), CompHt.IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) w abelian₂ ∧ Real.log abelian₂ ≤ C * (((D.R.f : ℝ) * D.R.r * Lb) ^ 3 * (∑ τ, ∑ k, |(la τ k : ℝ)|) + ((D.R.f : ℝ) * D.R.r * Lb) ^ 5) ∧ Real.log n ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
  intro hP
  obtain ⟨C2, hC2, h2⟩ := GlobalTheory.T.flat_constant_abs_le_nine_deep hP
  obtain ⟨Cb, hCb, hb⟩ := GlobalTheory.T.antitone_weight_log_bound hP
  refine ⟨2000 + Cb + C2, by positivity, ?_⟩
  intro D T hT j hp hq hE hj Y e o hY Lb hLb hM hfs hfr ho c₁ hc₁ hc₁b la hla hgap hsz Z
  have hgood := (GlobalTheory.T.good_weight_antitone_gap hP D T hT j hp hq hE hj Y e o hY la hla fun τ =>
    le_trans (by exact_mod_cast (by omega : 1 ≤ 8 * D.R.f * D.R.r + 10)) (hgap τ)).2 Z
  obtain ⟨s, hsL, hsp, hsn⟩ := h2 D T hT j hp hq hE hj Y e o hY Lb hLb hM hfs hfr ho c₁ hc₁ hc₁b la hla hgap hsz Z
  haveI : FiniteDimensional Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) :=
    hgood.1.some.2.1.1.finiteDimensional_of_finite
  obtain ⟨n, w, abelian₂, hsg, hLam, hn⟩ := GlobalTheory.T.exists_short_generators_of_short_spanning_family Y.d.c₂.F _
    (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) s _
    hgood.2.1 (fun σ f => AllWt.petAt_nonneg _ _ _ _ _ _ _)
    (fun σ a f => AllWt.petOn_smul _ _ _ _ Z _ σ a f) (GlobalTheory.T.petersson_norm_component_add_le_of_gramFrame _ _ _ _ Z _ hgood) hsL hsp hsn
  refine ⟨n, w, abelian₂, hsg, ?_⟩

  have hf1 : 1 ≤ D.R.f ∧ 1 ≤ D.R.r := by
    have hn : 1 ≤ D.R.ord := D.R.ord_pos
    have hf : D.R.f = 2 * D.R.ord := rfl
    have hk := D.R.f_le_k
    have ht := D.R.rank_add_five_le
    exact ⟨by omega, by unfold Ranks.r; omega⟩
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1.1
  have hrR : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hf1.2
  set X : ℝ := (D.R.f : ℝ) * D.R.r * Lb with hXdef
  set S : ℝ := ∑ τ, ∑ k, |(la τ k : ℝ)| with hSdef
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hfR hrR) hLb
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hX2 : X ^ 2 ≤ X ^ 5 := pow_le_pow_right₀ hX (by norm_num)
  have hX3 : X ^ 3 ≤ X ^ 5 := pow_le_pow_right₀ hX (by norm_num)
  have hX23 : X ^ 2 ≤ X ^ 3 := pow_le_pow_right₀ hX (by norm_num)
  have hX1 : 1 ≤ X ^ 3 := one_le_pow₀ hX
  have hXS : 0 ≤ X ^ 3 * S := mul_nonneg (by positivity) hS
  have hrhs : 0 ≤ (2000 + Cb + C2) * (X ^ 3 * S + X ^ 5) := by positivity
  have hlogd : Real.log (Module.finrank ℚ Y.d.c₂.F : ℝ) ≤ o := hY.deg
  have hdpos : (0 : ℝ) < Module.finrank ℚ Y.d.c₂.F := by exact_mod_cast Module.finrank_pos
  have hdisc : (0 : ℝ) < |((NumberField.discr Y.d.c₂.F : ℤ) : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero Y.d.c₂.F)
  have hlrd : Real.log (|((NumberField.discr Y.d.c₂.F : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ Y.d.c₂.F : ℝ))) ≤ o := by
    rw [Real.log_rpow hdisc, one_div, inv_mul_le_iff₀ hdpos, mul_comm]
    exact hY.rd
  have hberg := (hb D T hT j hp hq hE hj Y e o hY Lb hLb hM hfs hfr ho la hla (by linarith) Z).2.2
  have hm : Real.log (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) ≤ Cb * X ^ 3 := hberg
  have ho' : o ≤ 391 * X ^ 2 := ho
  have hCbX : Cb * X ^ 3 ≤ Cb * X ^ 5 := mul_le_mul_of_nonneg_left hX3 hCb
  constructor
  · have hL1 : 1 ≤ abelian₂ := hsg.one_le
    rcases le_or_gt ((Module.finrank ℚ Y.d.c₂.F : ℝ) ^ 4 * (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) *
        |((NumberField.discr Y.d.c₂.F : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ Y.d.c₂.F : ℝ)) *
        Real.exp (C2 * (X ^ 3 * S + X ^ 5))) 1 with hB | hB
    · have : abelian₂ = 1 := le_antisymm (hLam.trans (max_le le_rfl hB)) hL1
      rw [this, Real.log_one]; exact hrhs
    · have hLB := hLam.trans (le_of_eq (max_eq_right hB.le))
      have hmpos : (0 : ℝ) < (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) := by
        rcases (Nat.cast_nonneg (α := ℝ) (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)))).lt_or_eq with h | h
        · exact h
        · rw [← h] at hB; simp at hB; linarith
      have hrd : 0 < |((NumberField.discr Y.d.c₂.F : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ Y.d.c₂.F : ℝ)) :=
        Real.rpow_pos_of_pos hdisc _
      have hlog := Real.log_le_log (by linarith) hLB
      rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul (by positivity) hrd.ne',
        Real.log_mul (by positivity) hmpos.ne', Real.log_pow, Real.log_exp] at hlog
      have hC2X : C2 * (X ^ 3 * S + X ^ 5) ≤ C2 * (X ^ 3 * S + X ^ 5) := le_rfl
      nlinarith
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; positivity
    · have hnR : (n : ℝ) ≤ 2 * (Module.finrank ℚ Y.d.c₂.F : ℝ) * (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) := by
        exact_mod_cast hn
      have hmpos : (0 : ℝ) < (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) := by
        have : 0 < Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) := by
          rcases Nat.eq_zero_or_pos (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0))) with h | h
          · rw [h] at hn; omega
          · exact h
        exact_mod_cast this
      have hlog := Real.log_le_log (by exact_mod_cast hpos) hnR
      rw [Real.log_mul (by positivity) hmpos.ne', Real.log_mul (by norm_num) hdpos.ne'] at hlog
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9; linarith
      have hC2X3 : 0 ≤ C2 * X ^ 3 := by positivity
      nlinarith

end GlobalTheory.ShortGenComp

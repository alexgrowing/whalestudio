import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.UnfoldLoss.MovedChosen

section Local

variable {k : Type} [Field k] {G : Grid k}

theorem gdet_stair (hs : 1 ≤ G.s) (ϖ : kˣ) (e j : ℕ) :
    ∃ a : ℕ, gdet (stair G ϖ e j) = ϖ ^ a ∧ a ≤ G.rank (G.m, j) * (e * G.m) := by
  refine ⟨∑ a : Fin (G.rank (G.m, j)), e * (a.val + 1 - topRank G j), ?_, ?_⟩
  · rw [stair, gdet, det_diagGL, Finset.prod_pow_eq_pow_sum]
  · calc ∑ a : Fin (G.rank (G.m, j)), e * (a.val + 1 - topRank G j) ≤ ∑ _a : Fin (G.rank (G.m, j)), e * G.m :=
          Finset.sum_le_sum fun a _ => Nat.mul_le_mul_left _ (by have := topRank_add hs j; have := a.2; omega)
      _ = _ := by simp

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gdet_elt (hs : 1 ≤ G.s) (J : G.Level) (ϖ : kˣ) (e : ℕ) (X : ℕ × ℕ) :
    ∃ a : ℕ, gdet ((Reps.through hs J (stair G ϖ e)).elt (fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) X) = ϖ ^ a ∧
      a ≤ G.rank X * (e * G.m) := by
  obtain ⟨i, j⟩ := X
  by_cases hi : i = G.m
  · subst hi
    by_cases hj : j + 2 ≤ G.m
    · borelize k
      rw [through_elt _ hj]
      exact gdet_stair hs ϖ e j
    · cases j with
      | zero =>
        rw [Reps.elt, onColumn_apply]
        exact gdet_stair hs ϖ e 0
      | succ i =>
        refine ⟨0, ?_, Nat.zero_le _⟩
        rw [Reps.elt, onColumn_apply]
        simp [show ¬ i < G.m - 2 by omega]
  · refine ⟨0, ?_, Nat.zero_le _⟩
    simp [Reps.elt, onColumn, hi]

theorem apow_half {ϖ : kˣ} (hϖ : IsUnif ϖ) (a n : ℕ) :
    apow (ϖ ^ a)⁻¹ ((n : ℂ) / 2) = ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (a * n) := by
  rw [apow_inv, apow_pow, hϖ.apow_eq, neg_neg, mul_comm a n, pow_mul]
  congr 1
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.cpow_mul_nat]
  push_cast
  congr 1
  ring

end Local

section Val

variable {D : D7}

theorem lossLe_mul {w : PlL D} {z z' : ℂ} {a a' : ℝ} (h : LossLe w z a) (h' : LossLe w z' a') :
    LossLe w (z * z') (a + a') := by
  obtain ⟨y, rfl, hy⟩ := h
  obtain ⟨y', rfl, hy'⟩ := h'
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases h0 : y = 0
  · exact Or.inl (by simp [h0])
  by_cases h0' : y' = 0
  · exact Or.inl (by simp [h0'])
  refine Or.inr ?_
  have h1 := hy.resolve_left h0
  have h2 := hy'.resolve_left h0'
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ h0 h0', Int.cast_add]
  linarith

theorem lossLe_list_prod {w : PlL D} {ι : Type} (f : ι → ℂ) (a : ℝ) (l : List ι) (h : ∀ b ∈ l, LossLe w (f b) a) :
    LossLe w (l.map f).prod (l.length * a) := by
  induction l with
  | nil => exact ⟨1, by simp, Or.inr (by simp [Formalism.DivisionValues.ValuationRepresentative.vw_one])⟩
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons]
    refine (lossLe_mul (h b (by simp)) (ih fun c hc => h c (by simp [hc]))).mono (le_of_eq ?_)
    simp only [List.length_cons]
    push_cast
    ring

theorem lossLe_sqrt {w : PlL D} {q : ℕ} (hq : q ≠ 0) (hs : ((Real.sqrt q : ℝ) : ℂ) ∈ Set.range D.what₂.embLL) (n n' : ℕ) :
    LossLe w (((Real.sqrt q : ℝ) : ℂ) ^ n * (((Real.sqrt q : ℝ) : ℂ) ^ n')⁻¹) (n' * (vw w (q : D.what₂.LL) : ℝ) / 2) := by
  obtain ⟨y, hy⟩ := hs
  have h2 : y ^ 2 = (q : D.what₂.LL) := D.what₂.embLL.injective (by
    rw [map_pow, hy, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast])
  have hy0 : y ≠ 0 := by
    rintro rfl
    have : (q : D.what₂.LL) = 0 := by rw [← h2]; simp
    exact hq (by exact_mod_cast this)
  have hv : (vw w (q : D.what₂.LL) : ℝ) = 2 * vw w y := by
    rw [← h2, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_npow w hy0]
    push_cast
    ring
  have hv0 : (0 : ℝ) ≤ (vw w (q : D.what₂.LL) : ℝ) := by exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w q
  refine ⟨y ^ n * (y ^ n')⁻¹, by rw [map_mul, map_inv₀, map_pow, map_pow, hy], Or.inr ?_⟩
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero _ hy0) (inv_ne_zero (pow_ne_zero _ hy0)), Formalism.DivisionValues.ValuationRepresentative.vw_inv,
    ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_npow w hy0, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_npow w hy0, hv]
  rw [hv] at hv0
  have : (0 : ℝ) ≤ (n : ℝ) * vw w y := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  push_cast
  linarith

theorem rank_le {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (P : Pl D.host.E) {i j : ℕ}
    (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : (locGrid G t P).rank (i, j) ≤ bigN D := by
  have h1 := Nat.mul_le_mul_right D.R.t hj
  have h2 := Nat.mul_le_mul_right (sLen D) hi
  have hr : D.R.r ≤ D.R.k + D.R.m := by
    have : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  change D.R.r + j * D.R.t + i * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
  nlinarith

end Val

theorem moved_loss : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t),
    (P : Pl D.host.E) ∈ ch.G.pl.W0 → ∀ (w : PlL D) (c : ℝ), 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
    ∀ z, LossLe w (moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) z)
      (c + (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (cosExp ch.G P : ℝ) * (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS _ _ hF t Φ β hβ P hW w c _ hT z
  classical
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := Test.pde_ne_q hS
  have hc' : ∀ Q ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal :=
    GlobalTheory.RowTest.guard_of_qGuard hS.guard t
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hTT := isTensor_Tflip hL ch.W ch.S.B t Φ hde hc' P.2
  have hcond : HasConductor (psiAt ch.W P.1) 1 :=
    (((Good.locGrid_isGood hL ch.G ch.W t hde hc').1 P.1 P.2).square 0 hm 0 hm).cond
  haveI := (isUnitVol_unitVol P.1).1
  set e := cosExp ch.G P with he
  have hdep : depthAt ch.G P = e := by
    obtain ⟨v, hv, hvP⟩ := Finset.mem_image.1 hW
    have := depthAt_w ch.G hv
    rw [he, ← hvP, this.1, this.2]
  rw [hdep] at hTT
  have hkeep : keepAt ch.G P = false := by simp [keepAt, hW]
  have hO := oneCoset one_le_sLen (psiAt ch.W P.1) (unitVol P.1) (givenLevel ch.G t P) (Tflip ch.W ch.S.B t Φ P) (unifAt P.1) e
    D.R.m_even (isUnif_unifAt P.1) hcond hTT (fun j hj _ => ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.givenLevel_KO ch.G t P hj)
  have hb : β P ∈ unfSupport (psiAt ch.W P.1) (unitVol P.1) false
      (Reps.through one_le_sLen (givenLevel ch.G t P) (stair (locGrid ch.G t P) (unifAt P.1) e)) (Tflip ch.W ch.S.B t Φ P) := by
    have := hβ P
    rw [hkeep] at this
    exact this
  have hβ' := funext (hO _ hb)
  have hdet : ∀ X, ∃ a : ℕ, gdet ((repsAt ch.G t P).elt (β P) X) = unifAt P.1 ^ a ∧
      a ≤ (locGrid ch.G t P).rank X * (e * D.R.m) := fun X => by
    rw [hβ']
    exact gdet_elt (G := locGrid ch.G t P) one_le_sLen _ _ _ X
  generalize (repsAt ch.G t P).elt (β P) = g at hdet ⊢
  have hq := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.resCard_ne P.1
  have hsq : ((Real.sqrt (resCard (Kw (P : Pl D.host.E)) : ℕ) : ℝ) : ℂ) ∈ Set.range D.what₂.embLL := by
    rw [ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw]
    exact hF.sqrt P.1 (Or.inr ⟨t, P.2⟩)
  set v : ℝ := (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ) with hv
  have hv0 : 0 ≤ v := by rw [hv]; exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w _
  rw [hkeep, moved_false]
  have hP := lossLe_list_prod (w := w) (fun b : Edge => apow (gdet (g b.src))⁻¹ (((locGrid ch.G t P).rank b.tgt : ℂ) / 2) *
      apow (gdet (g b.tgt))⁻¹ (-((locGrid ch.G t P).rank b.src : ℂ) / 2))
      ((bigN D * (e * D.R.m) * bigN D : ℕ) * v / 2) (oppositePath (locGrid ch.G t P).m) (fun b hb => by
    have hr : (locGrid ch.G t P).rank b.src ≤ bigN D ∧ (locGrid ch.G t P).rank b.tgt ≤ bigN D := by
      change b ∈ oppositePath D.R.m at hb
      simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
      rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
      · exact ⟨rank_le _ _ _ hi.le le_rfl, rank_le _ _ _ hi le_rfl⟩
      · exact ⟨rank_le _ _ _ le_rfl hj, rank_le _ _ _ le_rfl hj.le⟩
    obtain ⟨a, ha, -⟩ := hdet b.src
    obtain ⟨a', ha', hle⟩ := hdet b.tgt
    rw [ha, ha', neg_div, apow_neg, apow_half (isUnif_unifAt P.1), apow_half (isUnif_unifAt P.1)]
    refine (lossLe_sqrt hq hsq _ _).mono ?_
    have h1 : a' * (locGrid ch.G t P).rank b.src ≤ bigN D * (e * D.R.m) * bigN D :=
      Nat.mul_le_mul (hle.trans (Nat.mul_le_mul_right _ hr.2)) hr.1
    have h2 : ((a' * (locGrid ch.G t P).rank b.src : ℕ) : ℝ) ≤ (bigN D * (e * D.R.m) * bigN D : ℕ) := by exact_mod_cast h1
    have h3 := mul_le_mul_of_nonneg_right h2 hv0
    rw [← hv]
    linarith)
  refine (lossLe_mul hP (hT _)).mono (le_of_eq ?_)
  have hlen : (oppositePath (locGrid ch.G t P).m).length = 2 * D.R.m := by
    change (oppositePath D.R.m).length = _
    simp [oppositePath]; ring
  rw [hlen]
  push_cast
  ring

end GlobalTheory.UnfoldLoss.MovedChosen

end

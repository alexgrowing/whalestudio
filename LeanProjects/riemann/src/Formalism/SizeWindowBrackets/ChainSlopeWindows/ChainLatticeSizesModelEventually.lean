import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic
import Formalism.SizeWindowBrackets.ChainSlopeWindows.PChain
import Formalism.SizeWindowBrackets.ChainSlopeWindows.SlopeInequalityOfLattices
import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
import Formalism.SizeWindowBrackets.ChainSlopeWindows.AdmissibleSchurLemma
import Formalism.SizeWindowBrackets.ChainSlopeWindows.OneLeThresholdMulPowers
import Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ProjectiveLines
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu

open Module NumberField Matrix
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain2

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

section Places
variable {K : Type} [Field K] [NumberField K]

theorem ramE_pos (w : slopeLatticeData.FinPl K) : 0 < ramE w := by
  have := w.2.isPrime
  unfold ramE
  exact_mod_cast Ideal.ramificationIdx_pos w.1 ℤ

theorem ell_nonneg (w : slopeLatticeData.FinPl K) : 0 ≤ slopeLatticeData.ell w := by
  unfold slopeLatticeData.ell
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

theorem lE_nonneg (w : slopeLatticeData.FinPl K) : 0 ≤ lE w := mul_nonneg (ell_nonneg w) (ramE_pos w).le

theorem prBelow_iff (w : slopeLatticeData.FinPl K) (p : ℕ) :
    prBelow w = p ↔ w.1.LiesOver (Ideal.span {(p : ℤ)}) := by
  unfold prBelow
  constructor
  · intro h
    refine ⟨?_⟩
    rw [← h]
    exact Int.ideal_span_absNorm_eq_self _
  · intro h
    rw [← h.over]
    simp

theorem sum_log_norm_over_prime (S : Finset (slopeLatticeData.FinPl K)) (p : ℕ) (hp : p.Prime)
    (hS : ∀ w : slopeLatticeData.FinPl K, prBelow w = p → w ∈ S) :
    ∑ w ∈ S.filter (fun w => prBelow w = p), lE w = Real.log (p : ℝ) := by
  classical
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hP
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hPprime : P.IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hPne : P ≠ ⊥ := by simpa [hP] using hpZ.ne_zero
  have hPmax : P.IsMaximal := hPprime.isMaximal hPne
  have : Fintype (P.primesOver (𝓞 K)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 K)
  have hmax : ∀ q : P.primesOver (𝓞 K), q.1.IsMaximal := fun q => by
    have := q.2.1
    have := q.2.2
    exact Ideal.IsMaximal.of_liesOver_isMaximal q.1 P
  have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hterm : ∀ w : slopeLatticeData.FinPl K, prBelow w = p →
      lE w = Real.log p / (Module.finrank ℚ K : ℝ) * ((w.1.ramificationIdx ℤ * w.1.inertiaDeg ℤ : ℕ) : ℝ) := by
    intro w hw
    have := (prBelow_iff w p).1 hw
    have := w.2
    unfold lE slopeLatticeData.ell ramE
    rw [Ideal.absNorm_eq_pow_inertiaDeg' w.1 hp, Ideal.inertiaDeg'_eq_inertiaDeg]
    push_cast
    rw [Real.log_pow]
    ring
  have hbij : ∑ w ∈ S.filter (fun w => prBelow w = p), lE w
      = ∑ q : P.primesOver (𝓞 K), Real.log p / (Module.finrank ℚ K : ℝ) *
          ((q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ : ℕ) : ℝ) := by
    symm
    refine Finset.sum_bij (fun q _ => (⟨q.1, hmax q⟩ : slopeLatticeData.FinPl K)) ?_ ?_ ?_ ?_
    · intro q _
      have : prBelow (⟨q.1, hmax q⟩ : slopeLatticeData.FinPl K) = p := (prBelow_iff _ p).2 q.2.2
      exact Finset.mem_filter.2 ⟨hS _ this, this⟩
    · intro q _ q' _ h
      exact Subtype.ext (congrArg (fun w : slopeLatticeData.FinPl K => w.1) h)
    · intro w hw
      have hw' := (Finset.mem_filter.1 hw).2
      exact ⟨⟨w.1, w.2.isPrime, (prBelow_iff w p).1 hw'⟩, Finset.mem_univ _, rfl⟩
    · intro q _
      exact (hterm (⟨q.1, hmax q⟩ : slopeLatticeData.FinPl K) ((prBelow_iff _ p).2 q.2.2)).symm
  rw [hbij, ← Finset.mul_sum, ← Nat.cast_sum, hsum, NumberField.RingOfIntegers.rank]
  field_simp

theorem prBelow_prime (w : slopeLatticeData.FinPl K) : (prBelow w).Prime := by
  have := w.2.isPrime
  have : NeZero w.1 := ⟨Ring.ne_bot_of_isMaximal_of_not_isField w.2 (RingOfIntegers.not_isField K)⟩
  exact Nat.absNorm_under_prime w.1

end Places

theorem unit_rule_over_places : UnitRulePl := by
  intro K _ _
  exact ⟨fun w => ⟨prBelow_prime w, ramE_pos w⟩, fun S p hp hS => sum_log_norm_over_prime S p hp hS⟩

namespace Fam

variable {I : Type} {m : ℕ} (F : Fam I m)

def prim (u : I) : LatticeToWeightTransfer.PPrim (slopeLatticeData.FinPl F.K) m where
  S := F.S
  ST := F.ST u
  l := lE
  gain := F.gain
  F := F.Fj
  E := F.Ej u
  tau := F.tauR
  io := fun w => F.iop (prBelow w)
  len := F.lenR u
  sg' := F.sgR u
  dM := F.dM u
  du := F.du u
  muMu := muDef (F.b u) (F.X u) (F.M u)
  muMaxMu := muMaxDef (F.b u) (F.X u) (F.M u)
  Rd := F.Rd u
  lam := F.lam u
  Pr := F.Pr
  pr := prBelow
  iop := F.iop

theorem rk_M (u : I) (hspan : Submodule.span F.K (F.M u : Set (F.V u)) = ⊤) :
    (rkK (F.M u) : ℝ) = F.du u := by
  unfold rkK Fam.du
  rw [hspan, finrank_top, Module.finrank_eq_card_basis (F.b u)]

theorem slopeRel (u : I) (f : ℕ) (bb : ℝ) (hX : ∀ v, IsUnit (F.X u v).det) (hd : 0 < F.du u)
    (hP : F.PlaceHyp f bb) :
    muMaxDef (F.b u) (F.X u) (F.N' u) ≤
      muMaxDef (F.b u) (F.X u) (F.M u) + UnitWeightPartition.Sg F.S lE (F.sgR u) F.tauR ∧
    muDef (F.b u) (F.X u) (F.N' u) =
      muDef (F.b u) (F.X u) (F.M u) + UnitWeightPartition.Sg F.S lE (F.sgR u) F.tauR
        - UnitWeightPartition.BeSum F.S lE (F.du u) (F.lenR u) F.tauR := by
  obtain ⟨-, hτ0, -, -, -, hu⟩ := hP
  obtain ⟨hFG, hspan, -, -, hle, hrkN, hoff, -⟩ := hu u
  have hrk := F.rk_M u hspan
  have hne : F.M u ≠ ⊥ := by
    intro h0
    have h1 : rkK (F.M u) = 0 := by
      unfold rkK
      rw [h0]
      simp
    rw [h1] at hrk
    simp only [Nat.cast_zero] at hrk
    exact absurd hrk hd.ne
  have h := LatticeToWeightTransfer.slope_formula_transfer F.K (F.V u) (F.ι u) (F.b u) (F.X u) hX (F.σ u) F.τ (F.M u) (F.N0 u)
    (fun w => (F.lenN u w : ℝ) / F.du u) hFG hne hle hrkN
    (fun w => by
      rw [hrk]
      show (F.lenN u w : ℝ) = _
      field_simp)
    F.S ramE lE (F.sgR u) F.tauR (F.lenR u)
    (fun w hw => ⟨(hoff w hw).1, hτ0 w hw, by
      show (F.lenN u w : ℝ) / F.du u = 0
      rw [(hoff w hw).2]; simp⟩)
    (fun w _ => ramE_pos w) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun w _ => by
      rw [hrk]
      unfold Fam.lenR
      congr 1
      field_simp)
  rw [hrk] at h
  exact h

end Fam

def restr {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f) (u0 : U0) :
    Data Unit (fun _ => W u0) Top m f where
  x := D.x
  ε := D.ε
  a := D.a
  b := D.b
  b' := D.b'
  k := D.k
  L := D.L
  La := D.La
  B0 := D.B0
  Nc := D.Nc
  gam := D.gam
  LpL := D.LpL
  v := D.v
  lg := D.lg
  logGam := D.logGam
  aT := D.aT
  w := fun _ => D.w u0
  d := fun _ => D.d u0
  T := fun _ => D.T u0
  muN := fun _ => D.muN u0
  muMaxN := fun _ => D.muMaxN u0
  h := fun _ => D.h u0
  muM := fun _ => D.muM u0
  muMaxM := fun _ => D.muMaxM u0
  EeJ := fun _ => D.EeJ u0
  muCC := fun _ => D.muCC u0
  muMinCC := fun _ => D.muMinCC u0
  Fo := fun _ => D.Fo u0
  Ga := fun _ => D.Ga u0
  Ta := fun _ => D.Ta u0
  ASK := fun _ => D.ASK u0
  IO := fun _ => D.IO u0
  HH := fun _ => D.HH u0
  del := fun _ => D.del u0
  η := fun _ => D.η u0
  e := fun _ => D.e u0
  delBar := D.delBar
  etaBar := D.etaBar
  eBar := D.eBar

section Data
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

theorem phi_card_pos : 0 < (PhiSet (H := H)).card :=
  Finset.card_pos.2 ⟨0, by simp [PhiSet, InPhi]⟩

variable [∀ u0, Nonempty (W u0)]

theorem slopes_of_places : SlopesOfPlaces (H := H) (W := W) (m := m) := by
  intro G C cT D ell N TT T2 a w Fm hx hk hX hd hP hS u0 u
  obtain ⟨h4, hcT, hsz⟩ := hS
  have hf : (1 : ℝ) ≤ ((PhiSet (H := H)).card : ℝ) := by exact_mod_cast phi_card_pos (H := H)
  have hb : 0 < bTx G.x G.ε := Real.exp_pos _
  have hHyp : LatticeToWeightTransfer.HypPrim (restr (mkData G C.cHH D ell N TT T2 a w Fm) u0)
      (fun _ u => (Fm u0).prim u) := by
    intro _ u
    have hrel := (Fm u0).slopeRel u _ _ (hX u0 u) (hd u0 u) (hP u0)
    obtain ⟨hτ, hτ0, hio, hsat, hTa, hu⟩ := hP u0
    obtain ⟨hFG, hspan, -, -, hle, hrkN, hoff, hT4, hTPr, hτT, hrank, hoffT, hovT, hlam, hround, hMu, hMaxMu,
      hsmall⟩ := hu u
    have hunit : ∀ p ∈ (Fm u0).Pr,
        ∑ w ∈ (Fm u0).S.filter (fun w => prBelow w = p), lE w = Real.log (p : ℝ) := by
      intro p hp
      obtain ⟨w0, hw0, rfl⟩ := Finset.mem_image.1 hp
      exact sum_log_norm_over_prime _ _ (prBelow_prime w0) (fun w' hw' => hsat w0 hw0 w' hw')
    have hdM : 0 < (Fm u0).dM u := by
      have h0 : 0 ≤ (Fm u0).dM u := Nat.cast_nonneg _
      rcases h0.lt_or_eq with h | h
      · exact h
      · have := hd u0 u
        rw [hrank, ← h, zero_mul] at this
        exact absurd this (lt_irrefl _)
    refine ⟨fun w _ => lE_nonneg w, hdM, ?_, hT4, hrank, Finset.filter_subset _ _, ?_, ?_, hio, hoffT, hovT,
      hlam, hunit _ hTPr, hround, le_refl _, hrel.2, hrel.1, hMu, hMaxMu, hTa, hsmall, ?_, hunit,
      fun _ _ => rfl⟩
    · show (2 : ℝ) < ((Fm u0).T u : ℝ)
      linarith
    · intro w hw
      show ((Fm u0).τ w : ℝ) / ramE w = 0
      rw [hτT w hw]; simp
    · intro w hw
      exact div_nonneg (by exact_mod_cast hτ w hw) (ramE_pos w).le
    · intro w hw
      exact Finset.mem_image_of_mem _ hw
  have hId : LatticeToWeightTransfer.PlaceSumIdentities (restr (mkData G C.cHH D ell N TT T2 a w Fm) u0)
      (LatticeToWeightTransfer.toP (restr (mkData G C.cHH D ell N TT T2 a w Fm) u0) (fun _ u => (Fm u0).prim u)) :=
    fun _ _ => ⟨rfl, rfl, fun _ => rfl⟩
  have hSz : LatticeToWeightTransfer.SizesPrim (restr (mkData G C.cHH D ell N TT T2 a w Fm) u0) C (XppH H G) cT
      (fun _ u => (Fm u0).prim u) := by
    refine ⟨h4, hcT, ?_, ?_, fun _ u => ⟨le_refl _, ?_, (hsz u0 u).2⟩⟩
    · show 0 ≤ (m : ℝ) * ((2 * (Fintype.card H : ℝ)) * m * bTx G.x G.ε * G.x ^ G.ε)
      have := Real.rpow_nonneg hx.le G.ε
      positivity
    · show 0 ≤ aTx G.x G.ε / G.k + bpTx G.x G.ε
      have h1 : 0 < aTx G.x G.ε := mul_pos hx hb
      have h2 : 0 < XpTx G.x G.ε := Real.exp_pos _
      unfold bpTx
      positivity
    · have := (hsz u0 u).1
      show (Fm u0).lam u ≤ cT * ((Fintype.card TT : ℕ) : ℝ) * (m : ℝ) * (aTx G.x G.ε / G.k + bpTx G.x G.ε)
      rwa [Fintype.card_coe]
  exact LatticeToWeightTransfer.unit_weight_of_primitive _ C (XppH H G) cT _ hHyp hId hSz () u

theorem slope_inequality_of_family : SlopeIneqOfFam (H := H) (W := W) (m := m) := by
  intro G cHH D ell N TT T2 a w Fm hL hdu
  refine (LatticeToWeightTransfer.function_transfer _).2 fun u0 hSide => ?_
  obtain ⟨hG, hγ, hBV, hV, hD, hsg, hsg20, hR, h0, h0', h1, he0, hse, hS⟩ := hL u0
  have hRpos : 0 < MatrixLatticeEstimates.RsG (Fm u0).ιf := lt_of_lt_of_le (div_pos hD hsg) hR
  have hRle : MatrixLatticeEstimates.RsG (Fm u0).ι ≤ MatrixLatticeEstimates.RsG (Fm u0).ιf := Finset.sum_le_sum fun u _ => (hdu u0 u).2
  have hRge : 3 / 4 * MatrixLatticeEstimates.RsG (Fm u0).ιf ≤ MatrixLatticeEstimates.RsG (Fm u0).ι := by
    unfold MatrixLatticeEstimates.RsG
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun u _ => (hdu u0 u).1
  have hde4 : (Fm u0).deF ≤ 1 / 4 := by
    unfold Fam.deF
    have : 3 / 4 ≤ MatrixLatticeEstimates.RsG (Fm u0).ι / MatrixLatticeEstimates.RsG (Fm u0).ιf := by
      rw [le_div_iff₀ hRpos]; exact hRge
    linarith
  have hde0 : 0 ≤ (Fm u0).deF := by
    unfold Fam.deF
    rw [sub_nonneg, div_le_one hRpos]
    exact hRle
  have hcor : ∑ i, ((Fintype.card ((Fm u0).ιf i) : ℝ) - (Fintype.card ((Fm u0).ι i) : ℝ))
      ≤ (Fm u0).deF * MatrixLatticeEstimates.RsG (Fm u0).ιf := by
    unfold Fam.deF
    rw [Finset.sum_sub_distrib, sub_mul, one_mul, div_mul_cancel₀ _ hRpos.ne']
    exact le_refl _
  exact LatticeToWeightTransfer.function_slope_transfer _ u0 (Fm u0).K (Fm u0).Wd (Fm u0).κ (Fm u0).κ₁ (Fm u0).V (Fm u0).ι (Fm u0).b'
    (Fm u0).X' (Fm u0).cc (Fm u0).b (Fm u0).X (Fm u0).N' (Fm u0).B (Fm u0).v (Fm u0).Y (Fm u0).Y'
    (Fm u0).Ball (Fm u0).γ (Fm u0).ιf (Fm u0).Bf (Fm u0).Vr (Fm u0).Dstar (sgX G cHH) (Fm u0).η0
    (Fm u0).η1 (Fm u0).e0 (Fm u0).deF
    ⟨⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl⟩, hG, hγ, hBV, hV, hD, hsg, hsg20, hR, h0, h0',
      h1, he0, hse, hde0, hde4, hcor, hS, rfl, rfl⟩ hSide

theorem ranks_of_places : RanksOfPlaces (m := m) := by
  intro I F f bb hf hbb hd hP u
  obtain ⟨-, -, -, -, -, hu⟩ := hP
  obtain ⟨-, -, -, -, -, -, -, hT4, -, -, hrank, -, -, -, -, -, -, hsmall⟩ := hu u
  have hf' : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hT : (4 : ℝ) ≤ (F.T u : ℝ) := by linarith
  have hdM : 0 < F.dM u := by
    have h0 : 0 ≤ F.dM u := Nat.cast_nonneg _
    rcases h0.lt_or_eq with h | h
    · exact h
    · have := hd u
      rw [hrank, ← h, zero_mul] at this
      exact absurd this (lt_irrefl _)
  obtain ⟨-, d2, -, d4⟩ := UnitWeightPartition.deficit_bounds f (F.T u : ℝ) (F.dM u) (F.du u) hdM (by linarith) hrank
  have hlog : 0 ≤ (f : ℝ) * Real.log ((F.T u : ℝ) - 1) / ((F.T u : ℝ) - 2) :=
    div_nonneg (mul_nonneg (by linarith) (Real.log_nonneg (by linarith))) (by linarith)
  have hq : 0 ≤ 4 * (f : ℝ) / (F.T u : ℝ) := div_nonneg (by linarith) (by linarith)
  have h8 : 4 * (f : ℝ) / (F.T u : ℝ) * 2 ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hbb hq
    linarith
  have h14 : 2 * (f : ℝ) / (F.T u : ℝ) ≤ 1 / 4 := by
    have e1 : 4 * (f : ℝ) / (F.T u : ℝ) * 2 = 4 * (2 * (f : ℝ) / (F.T u : ℝ)) := by ring
    linarith
  have h34 : 3 / 4 ≤ F.du u / F.dM u := by linarith
  have h1 : F.du u / F.dM u ≤ 1 := by linarith
  exact ⟨(le_div_iff₀ hdM).1 h34, by simpa using (div_le_iff₀ hdM).1 h1⟩

theorem sizeConditions_of_split : HidaSettingOfHyp (H := H) (W := W) (m := m) := by
  intro D ell G C cT N TT T2 a w Fm η θ eK K CL
  rintro ⟨hLat, hPl, hSz, hv, hd, heB, hDIV, hE, hHC, hCnt, hSl, hHH, hFP, hWin, hRest, hCost, hSize⟩
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩ := hWin
  have hx1 : (1 : ℝ) ≤ G.x := w1
  have hx : 0 < G.x := by linarith
  have hε : 0 < G.ε := w2
  have hk : 0 < G.k := lt_of_lt_of_le one_pos w10
  have hb : 0 < bTx G.x G.ε := Real.exp_pos _
  have hb2 : 2 ≤ bTx G.x G.ε ^ 2 := by
    have h1 : 1 ≤ G.x ^ G.ε := Real.one_le_rpow hx1 hε.le
    have h2 : 2 ≤ bTx G.x G.ε := by
      have := Real.add_one_le_exp (G.x ^ G.ε)
      unfold bTx
      linarith
    nlinarith
  have hf : (1 : ℝ) ≤ ((PhiSet (H := H)).card : ℝ) := by exact_mod_cast phi_card_pos (H := H)
  have hSet : (mkData G C.cHH D ell N TT T2 a w Fm).HidaSetting C := by
    refine ⟨hx, hb, (mul_pos hx hb).le, w17, hk, hv, phi_card_pos, fun t => (w21 t).1, ?_, hd, ?_, ?_,
      by linarith [hSz.1], by linarith [show G.delBar ≤ 1 / 2 from w25], w26, w27, heB⟩
    · intro u0 j ρ
      exact hRest.1.2.2.2.2.2.2.1.1 u0 j _ (Finset.mem_filter.1 (ePhi ρ).2).2
    · intro u0 u
      have := (hPl u0).2.2.2.2.2 u
      have hT4 : 4 * ((PhiSet (H := H)).card : ℝ) ≤ ((Fm u0).T u : ℝ) := this.2.2.2.2.2.2.2.1
      show (0 : ℝ) < ((Fm u0).T u : ℝ)
      linarith
    · intro u0 u
      have hG := (hLat u0).1
      exact MatrixLatticeEstimates.slope_le_max_slope ((Fm u0).b u) ((Fm u0).X u) (hG.2.1 u) ((Fm u0).N' u)
        (hG.2.2.2.2.2.2.1 u) (hG.2.2.2.2.2.2.2.1 u) (Nat.cast_pos.1 (hd u0 u))
  refine ⟨hSet, ?_, ?_, ?_, ?_⟩
  · exact slopes_of_places G C cT D ell N TT T2 a w Fm hx hk (fun u0 u v => (hLat u0).1.2.1 u v) hd hPl hSz
  · exact slope_inequality_of_family G C.cHH D ell N TT T2 a w Fm hLat
      (fun u0 u => ranks_of_places _ (Fm u0) _ _ phi_card_pos hb2 (hd u0) (hPl u0) u)
  · intro u0
    exact ⟨hHH u0, mul_pos (Real.rpow_pos_of_pos hx _) hb, le_refl _⟩
  · intro u0
    obtain ⟨f1, f2, f3⟩ := hFP u0
    obtain ⟨hG, -, -, -, -, hsg, -, -, -, -, -, he0, -⟩ := hLat u0
    refine ⟨hG.2.2.2.2.2.2.2.2.2.2.2.1, f1, ?_, f2, ?_, f3⟩
    · show 0 ≤ 5 * sgX G C.cHH + 3 * Real.sqrt (Fm u0).deF
      have := Real.sqrt_nonneg (Fm u0).deF
      linarith
    · show 0 ≤ 2 * (Fm u0).e0
      linarith

end Data

theorem first_variant_reduction : Core2aToCore := by
  rintro eD eL K cHH eK CL ε x ⟨H, i1, i2, i3, W, i4, i5, m, D, ell, G, C, cT, N, TT, T2, a, w, Fm, η, θ,
    hx, hε, heD, heL, hcHH, hHost, hB, hLoss⟩
  obtain ⟨hSet, hN5, hSI, hHHB, hFPar⟩ := sizeConditions_of_split D ell G C cT N TT T2 a w Fm η θ eK K CL hB
  obtain ⟨hLat, hPl, hSz, hv, hd, heB, hDIV, hE, hHC, hCnt, hSl, hHH, hFP, hWin, hRest, hCost, hSize⟩ := hB
  exact ⟨H, i1, i2, i3, W, i4, i5, TT, inferInstance, m, _, mkData G C.cHH D ell N TT T2 a w Fm, C, XppH H G,
    D, ell, N, TT, T2, a, w, Equiv.refl _, ePhi, η, XpTx G.x G.ε, θ, hx, hε, heD, heL, hcHH, hHost,
    ⟨fun _ => rfl, fun _ _ _ => rfl, rfl, rfl, fun _ => rfl⟩,
    ⟨hSet, hDIV, hE, hHC, hCnt, hSl, hN5, hLoss, hSI, hHHB, hFPar⟩, hWin, ⟨le_refl _, le_refl _⟩,
    hx ▸ hε ▸ hRest, hx ▸ hCost, hx ▸ hε ▸ hSize⟩

theorem lattice_reduction_to_first_variant : Core2ToCore2a := by
  rintro eD eL K cHH eK CL ε x ⟨e, q, d, i1, i2, W, i3, i4, m, G, C, cT, N, TT, T2, a, w, Fm, η, θ,
    hHyp, hx, hε, heD, heL, hcHH, hIn⟩
  exact ⟨LHost.HA e, inferInstance, inferInstance, inferInstance, W, i3, i4, m, LHost.hostData e q d,
    hostEll e q d, G, C, cT, N, TT, T2, a, w, Fm, η, θ, hx, hε, heD, heL, hcHH,
    LHost.extension_facts e q d hHyp, hIn⟩

section Loss
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {Ω : Type} {W : Ω → H → Type} {m : ℕ}

theorem gD_spec (D : ArithData H) (hD : HostFacts D) (i : ℕ) :
    gD D i - i • D.frob D.d ∈ D.inertia D.d ∧ ¬ InPhi (gD D i) := by
  unfold gD
  split_ifs with h
  · refine ⟨(hD.inertia_d _).2 (Or.inr (by abel)), ?_⟩
    unfold InPhi at h ⊢
    show (i • D.frob D.d).1.1 + 1 ≠ 0
    rw [h]
    decide
  · exact ⟨(hD.inertia_d _).2 (Or.inl (by abel)), h⟩

theorem askD_eq (D : ArithData H) (hD : HostFacts D) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) :
    askD D N a t w = DeficitSplitLemmas.askAt (Finset.Icc 1 N) a (D.d : ℝ) (fun i => w (partner t (gD D i))) := by
  classical
  unfold askD DeficitSplitLemmas.askAt
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_eq_single (gD D i) (fun g hg hne => ?_) (fun hn => ?_)
  · rw [Finset.mem_filter] at hg
    exact absurd ((double_coset_singleton D hD i).unique hg.2 (gD_spec D hD i)) hne
  · rw [Finset.mem_filter] at hn
    exact absurd ⟨Finset.mem_univ _, gD_spec D hD i⟩ hn

theorem ASK_eq (D : ArithData H) (hD : HostFacts D) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) :
    ASK D N a t w = (∑ p ∈ inertPs D N, 2 * Real.log p *
        DeficitSplitLemmas.askAt ((Finset.Icc 1 N).filter (fun i => ¬ InPhi (i • D.frob p))) a (p : ℝ)
          (fun i => w (partner t (i • D.frob p))))
      + Real.log D.d * DeficitSplitLemmas.askAt (Finset.Icc 1 N) a (D.d : ℝ) (fun i => w (partner t (gD D i))) := by
  rw [← askD_eq D hD]
  rfl

theorem log_derivative_identity : LdIdent (H := H) (Ω := Ω) (W := W) (m := m) := by
  intro D hD N TT a w Fm Lp u0 o
  constructor
  · unfold PrimeWindowSizeBounds.LD.ASK DeficitSplitLemmas.ASK
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ASK_eq D hD]
    rfl
  · unfold PrimeWindowSizeBounds.LD.Ga DeficitSplitLemmas.GaW Fam.Ga UnitWeightPartition.Ga
    congr 1
    exact Finset.sum_map (Fm o u0).S (plEmb Fm o u0) _

variable [Fintype Ω] [∀ o u0, Fintype (W o u0)]

theorem losses_of_window : LossesOfWindow (H := H) (Ω := Ω) (W := W) (m := m) := by
  intro D hD ell G C N TT T2 a w Fm Lp P π s sB BAD Sig Cord eW KW o hL hx1 hC
  obtain ⟨px, pε, -, pd, -, hWin, -, hio, hc, he⟩ := hL
  obtain ⟨hε0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hC0, -⟩ := hWin
  have hId := fun u0 => log_derivative_identity D hD N TT a w Fm Lp u0 o
  have h := PrimeWindowSizeBounds.losses_of_setting P (PlAll Fm) (Fin m) H H H Ω (inertPs D N) s Finset.univ TT
    (fun u0 p o => (Fm o u0).iop p) (ldOf D N a w Fm Lp) o id
    ({ mkData G C.cHH D ell N TT T2 (a o) (w o) (Fm o) with
        IO := fun u0 => ∑ p ∈ s, Real.log (p : ℝ) * (Fm o u0).iop p }) C hC (px ▸ hx1) hε0.le hC0 px.symm pε.symm
    (by show bTx G.x G.ε = bTx P.x P.ε; rw [px, pε]) (Fintype.card_coe TT) (by simp)
    (fun u0 => by rw [pd]; exact ((hId u0).1).symm) (fun u0 => ((hId u0).2).symm) (fun _ => rfl) hc he
  intro u0
  refine ⟨(h u0).1, le_trans ?_ (h u0).2⟩
  show ∑ p ∈ (Fm o u0).Pr, Real.log (p : ℝ) * (Fm o u0).iop p ≤ ∑ p ∈ s, Real.log (p : ℝ) * (Fm o u0).iop p
  calc ∑ p ∈ (Fm o u0).Pr, Real.log (p : ℝ) * (Fm o u0).iop p
      = ∑ p ∈ (Fm o u0).Pr.filter (fun p => p ∈ s), Real.log (p : ℝ) * (Fm o u0).iop p := by
        refine (Finset.sum_filter_of_ne fun p hp hne => ?_).symm
        by_contra hps
        exact hne (by rw [(hio o u0).1 p hp hps, mul_zero])
    _ ≤ ∑ p ∈ s, Real.log (p : ℝ) * (Fm o u0).iop p :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.1 hp).2)
          (fun p hp _ => mul_nonneg (Real.log_natCast_nonneg p) ((hio o u0).2 p hp))

end Loss

theorem lattice_complete_reduction : Core2cToCore2 := by
  obtain ⟨Cord, h0, h⟩ := PrimeWindowSizeBounds.joint_bound_eventually
  refine ⟨Cord, h0, fun ε eW KW hε hε4 => ?_⟩
  obtain ⟨x₁, hx₁⟩ := h ε eW KW hε hε4
  refine ⟨x₁, ?_⟩
  rintro eD eL K cHH eK CL x hxx ⟨e, q, d, i1, i2, Ω, i3, W, i4, i5, m, G, C, cT, N, TT, T2, a, w, Fm, Lp, P, π,
    s, sB, BAD, Sig, η, θ, hHyp, hx, hεG, heD, heL, hcHH, -, hL, hB⟩
  have hL' := hL
  obtain ⟨px, pε, -, -, pC, hWin, hSet, -⟩ := hL'
  obtain ⟨o, hπ, hC⟩ := hx₁ P (pε.trans hεG) pC (by rw [px, hx]; exact hxx) hWin _ _ _ _ Ω π _ s sB _ TT BAD Sig _ _
    hSet
  have hBo := hB o hπ
  have hx1 : 1 ≤ G.x := hBo.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.1
  exact ⟨e, q, d, i1, i2, W o, i4 o, i5 o, m, G, C, cT, N, TT, T2, a o, w o, Fm o, η, θ, hHyp, hx, hεG, heD, heL,
    hcHH, hBo, losses_of_window _ (LHost.extension_facts e q d hHyp) _ G C N TT T2 a w Fm Lp P π s sB BAD
      Sig Cord eW KW o hL hx1 hC⟩

theorem hostV_pos (e q d : ℕ) (hq : q.Prime) (hd : d.Prime) : 0 < hostV e q d := by
  unfold hostV
  have h1 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have h2 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd.pos
  exact mul_pos (Real.rpow_pos_of_pos two_pos _) (Real.sqrt_pos.2 (mul_pos h1 h2))

section DataD
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

theorem inputs_discriminant_iff : InputsDIff (H := H) (W := W) (m := m) := by
  intro D ell G C cT N TT T2 a w Fm η θ eK K CL
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h4, h1, h2, h3, h5, h6, h7, h8⟩
  · rintro ⟨h4, h1, h2, h3, h5, h6, h7, h8⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

end DataD

theorem lattice_discriminant_reduction : Core2dToCore2c := by
  rintro Cord eD eL K cHH eK CL eW KW ε x ⟨e, q, d, i1, i2, Ω, i3, W, i4, i5, m, G, C, cT, N, TT, T2, a, w, Fm, Lp, P,
    π, s, sB, BAD, Sig, η, θ, g₁, g₂, logOm, hHyp, hx, hε, heD, heL, hcHH, hPe, hv, -, -, -, hPer, hL, hB⟩
  refine ⟨e, q, d, i1, i2, Ω, i3, W, i4, i5, m, G, C, cT, N, TT, T2, a, w, Fm, Lp, P, π, s, sB, BAD, Sig, η, θ,
    hHyp, hx, hε, heD, heL, hcHH, hPe, hL, fun o ho => ?_⟩
  refine (inputs_discriminant_iff _ _ G C cT N TT T2 (a o) (w o) (Fm o) η θ eK K CL).2 ⟨?_, ?_⟩
  · rw [hv]
    exact hostV_pos e q d hHyp.1 hHyp.2.1
  · have h := hB o ho
    unfold PerHost at hPer
    rw [hv, ← hPer]
    exact h

section ModelLemmas

open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat inclMat)

variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

theorem gram_std (n : Type) [Fintype n] [DecidableEq n] (v : InfinitePlace K) :
    gramPl (Pi.basisFun K n) (fun _ => 1) v
      (fun a : Fin (Fintype.card n) => Pi.basisFun K n ((Fintype.equivFin n).symm a)) = 1 := by
  ext a c
  simp [gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, Matrix.one_apply, Pi.single_apply, eq_comm]

theorem mu_std (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] :
    muDef (Pi.basisFun K n) (fun _ => 1) (stdLat K n) = 0 := by
  have hX : ∀ v : InfinitePlace K, IsUnit ((1 : Matrix n n ℂ)).det := by simp
  have hr : Set.range (fun a : Fin (Fintype.card n) => Pi.basisFun K n ((Fintype.equivFin n).symm a))
      = Set.range (Pi.basisFun K n) := EquivLike.range_comp _ (Fintype.equivFin n).symm
  have h := (height_gram_determinant K (n → K) n (Pi.basisFun K n) (fun _ => 1) hX (Fintype.card n)
    (fun a => Pi.basisFun K n ((Fintype.equivFin n).symm a))
    ((Pi.basisFun K n).linearIndependent.comp _ (Fintype.equivFin n).symm.injective)).1
  rw [hr] at h
  rw [slopeLatticeData.muDef_eq_log _ _ hX (ProjectiveLineModels.standard_lattice_fg K n) (ProjectiveLineModels.standard_lattice_ne_bot K n)]
  have h1 : ht (Pi.basisFun K n) (fun _ => 1) (stdLat K n) = 1 := by
    unfold stdLat
    rw [h]
    simp only [gram_std, Matrix.det_one, Complex.one_re, Finset.prod_const_one]
  rw [h1]
  simp

theorem twistP : Twist :=
  twist_of rescale_covolume_formula place_lattice_structure (shiftInvariance_of slope_characterization slope_characterization polygon_slopes_characterization)

theorem scaled_std (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] (c : ℝ) (hc : 0 < c) :
    muDef (Pi.basisFun K n) (fun _ => (c : ℂ) • (1 : Matrix n n ℂ)) (stdLat K n) = 2 * Real.log c ∧
    muMaxDef (Pi.basisFun K n) (fun _ => (c : ℂ) • (1 : Matrix n n ℂ)) (stdLat K n)
      = muMaxDef (Pi.basisFun K n) (fun _ => 1) (stdLat K n) + 2 * Real.log c := by
  have hX : ∀ v : InfinitePlace K, IsUnit ((1 : Matrix n n ℂ)).det := by simp
  have h := (twistP K (n → K) n (Pi.basisFun K n) (fun _ => 1) (fun _ => c) hX (fun _ => hc) (stdLat K n)
    (ProjectiveLineModels.standard_lattice_fg K n)).2.2.1 (ProjectiveLineModels.standard_lattice_ne_bot K n)
  have ht : (1 / (nPl K : ℝ)) * ∑ _v : InfinitePlace K, Real.log c = Real.log c := by
    have hn : (nPl K : ℝ) ≠ 0 := by
      have : 0 < nPl K := Fintype.card_pos
      exact_mod_cast this.ne'
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    unfold nPl at hn ⊢
    field_simp
  simp only [ht] at h
  exact ⟨by rw [h.1, mu_std]; ring, h.2.1⟩

def inclL (κ κ₁ : Type) : (κ → K) →ₗ[K] (κ ⊕ κ₁ → K) where
  toFun x := Sum.elim x 0
  map_add' x y := by ext (a | a) <;> simp
  map_smul' r x := by ext (a | a) <;> simp

theorem inclL_matrix (κ κ₁ : Type) [Fintype κ] [Fintype κ₁] [DecidableEq κ] [DecidableEq κ₁]
    (v : InfinitePlace K) :
    (LinearMap.toMatrix (Pi.basisFun K κ) (Pi.basisFun K (κ ⊕ κ₁)) (inclL K κ κ₁)).map v.embedding
      = inclMat κ κ₁ := by
  ext (a | a) k
  · simp [LinearMap.toMatrix_apply, inclL, inclMat, Pi.single_apply, apply_ite]
  · simp [LinearMap.toMatrix_apply, inclL, inclMat]

theorem inclMat_norm (κ κ₁ : Type) [Fintype κ] [Fintype κ₁] [DecidableEq κ] [DecidableEq κ₁] :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (inclMat κ κ₁))‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (le_of_eq ?_)
  rw [Fintype.sum_sum_type]
  simp [Matrix.toLpLin_apply, inclMat, Matrix.mulVec, dotProduct]

theorem inclL_ht (κ κ₁ : Type) [Fintype κ] [Fintype κ₁] [DecidableEq κ] [DecidableEq κ₁] :
    htMap (Pi.basisFun K κ) (fun _ => 1) (Pi.basisFun K (κ ⊕ κ₁)) (fun _ => 1) (inclL K κ κ₁) ≤ 0 := by
  unfold htMap
  refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos fun v _ => ?_)
  refine Real.log_nonpos (sq_nonneg _) ?_
  unfold opNormAt
  rw [inclL_matrix]
  simp only [inv_one, Matrix.one_mul, Matrix.mul_one]
  exact pow_le_one₀ (norm_nonneg _) (inclMat_norm κ κ₁)

theorem muMax_incl (κ κ₁ : Type) [Fintype κ] [Fintype κ₁] [DecidableEq κ] [DecidableEq κ₁] [Nonempty κ] :
    muMaxDef (Pi.basisFun K κ) (fun _ => 1) (stdLat K κ)
      ≤ muMaxDef (Pi.basisFun K (κ ⊕ κ₁)) (fun _ => 1) (stdLat K (κ ⊕ κ₁)) := by
  have hinj : Function.Injective (inclL K κ κ₁) := by
    intro x y hxy
    ext a
    exact congrFun hxy (Sum.inl a)
  have hmap : (stdLat K κ).map ((inclL K κ κ₁).restrictScalars (𝓞 K)) ≤ stdLat K (κ ⊕ κ₁) := by
    unfold stdLat
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨Sum.inl k, ?_⟩
    ext (a | a) <;> simp [inclL, Pi.single_apply]
  have hne : (stdLat K κ).map ((inclL K κ κ₁).restrictScalars (𝓞 K)) ≠ ⊥ := by
    intro h0
    obtain ⟨k⟩ := (inferInstance : Nonempty κ)
    have h1 : (inclL K κ κ₁) (Pi.basisFun K κ k) ∈
        (stdLat K κ).map ((inclL K κ κ₁).restrictScalars (𝓞 K)) :=
      ⟨_, Submodule.subset_span ⟨k, rfl⟩, rfl⟩
    rw [h0, Submodule.mem_bot] at h1
    exact (Pi.basisFun K κ).ne_zero k (hinj (h1.trans (map_zero _).symm))
  have h := ((slope_inequality_mean K (κ → K) κ (κ ⊕ κ₁ → K) (κ ⊕ κ₁) (Pi.basisFun K κ) (fun _ => 1)
    (Pi.basisFun K (κ ⊕ κ₁)) (fun _ => 1) (by simp) (by simp) (inclL K κ κ₁) (stdLat K κ)
    (ProjectiveLineModels.standard_lattice_fg K κ) hne).2 (stdLat K (κ ⊕ κ₁)) (ProjectiveLineModels.standard_lattice_fg K _) hmap).2 hinj.injOn
  have := inclL_ht K κ κ₁
  linarith

open Classical in

def plOver (p : ℕ) : Finset (slopeLatticeData.FinPl K) :=
  if h : {w : slopeLatticeData.FinPl K | prBelow w = p}.Finite then h.toFinset else ∅

variable {K} in
theorem mem_plOver {p : ℕ} (hp : p.Prime) (w : slopeLatticeData.FinPl K) : w ∈ plOver K p ↔ prBelow w = p := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hPprime : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hPne : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by simpa using hpZ.ne_zero
  have hPmax : (Ideal.span {(p : ℤ)}).IsMaximal := hPprime.isMaximal hPne
  have hfin : {w : slopeLatticeData.FinPl K | prBelow w = p}.Finite := by
    have : Finite {w : slopeLatticeData.FinPl K | prBelow w = p} :=
      Finite.of_injective
        (fun w : {w : slopeLatticeData.FinPl K | prBelow w = p} =>
          (⟨w.1.1, w.1.2.isPrime, (prBelow_iff w.1 p).1 w.2⟩ : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)))
        (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun q => q.1) hab)))
    exact Set.toFinite _
  unfold plOver
  rw [dif_pos hfin]
  simp

def tau0 (p₁ t₁ : ℕ) : slopeLatticeData.FinPl K →₀ ℤ :=
  Finsupp.onFinset (plOver K p₁)
    (fun w => if w ∈ plOver K p₁ then ((w.1.ramificationIdx ℤ : ℕ) : ℤ) * (t₁ : ℤ) else 0)
    (fun w hw => by
      by_contra h
      exact hw (if_neg h))

def dT (f T : ℕ) : ℝ := (f : ℝ) * Real.log ((T : ℝ) - 1) / ((T : ℝ) - 2)

def modelFam (v : InfinitePlace K) (m f T p₁ t₁ Mw : ℕ) (hb : ℝ) : Fam (Fin Mw) m where
  K := K
  Wd := Fin ((T - 2) ^ f) → K
  κ := Fin ((T - 2) ^ f)
  κ₁ := Fin ((T - 1) ^ f - (T - 2) ^ f)
  V := fun _ => Fin ((T - 2) ^ f) → K
  ι := fun _ => Fin ((T - 2) ^ f)
  Vf := fun _ => Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f) → K
  ιf := fun _ => Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f)
  b' := Pi.basisFun K _
  X' := fun _ => 1
  cc := stdLat K _
  b := fun _ => Pi.basisFun K _
  X := fun _ _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1
  M := fun _ => stdLat K _
  N0 := fun _ => Formalism.HermitianLatticesTheory.idealSmul
    ((slopeLatticeData.idealPow (tau0 K p₁ t₁) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (stdLat K _)
  bf := fun _ => Pi.basisFun K _
  Xf := fun _ _ => 1
  Mf := fun _ => stdLat K _
  σ := fun _ => tau0 K p₁ t₁
  τ := tau0 K p₁ t₁
  B := fun _ => LinearMap.id
  v := v
  Y := fun _ => 1
  Y' := 1
  Ball := fun _ => inclMat _ _
  γ := fun _ => 1
  Bf := fun _ => 1
  Vr := fun _ => inclMat _ _
  S := plOver K p₁ ∪ plOver K T
  gain := fun _ w => (tau0 K p₁ t₁ w : ℝ) / ramE w + 1
  Fj := fun _ _ => 1 / 2
  Ej := fun _ _ _ => 1 / 4
  iop := fun _ => 1
  T := fun _ => T
  h := fun _ => max (htMap (Pi.basisFun K (Fin ((T - 2) ^ f)))
    (fun _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1) (Pi.basisFun K (Fin ((T - 2) ^ f))) (fun _ => 1)
    LinearMap.id) hb
  lam := fun _ => 1
  Dstar := ((T - 1) ^ f : ℕ)
  η0 := 0
  η1 := 0
  e0 := 0

variable {K} in
theorem twist_vector_apply (p₁ t₁ : ℕ) (w : slopeLatticeData.FinPl K) :
    tau0 K p₁ t₁ w = if w ∈ plOver K p₁ then ((w.1.ramificationIdx ℤ : ℕ) : ℤ) * (t₁ : ℤ) else 0 := rfl

variable {K} in
theorem twist_vector_div_ramification (p₁ t₁ : ℕ) (w : slopeLatticeData.FinPl K) :
    (tau0 K p₁ t₁ w : ℝ) / ramE w = if w ∈ plOver K p₁ then (t₁ : ℝ) else 0 := by
  have he := ramE_pos w
  rw [twist_vector_apply]
  split_ifs with h
  · unfold ramE at he ⊢
    push_cast
    field_simp
  · simp

theorem modLat_cancel {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (τ : slopeLatticeData.FinPl K →₀ ℤ) (L : Submodule (𝓞 K) V) :
    slopeLatticeData.modLat τ (Formalism.HermitianLatticesTheory.idealSmul
      ((slopeLatticeData.idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) L) = L := by
  have h1 : slopeLatticeData.idealPow (-τ) * slopeLatticeData.idealPow τ = (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [← slopeLatticeData.idealPow_add, neg_add_cancel]
    unfold slopeLatticeData.idealPow
    rw [Finsupp.prod_zero_index]
  unfold slopeLatticeData.modLat
  rw [eq_inv_of_mul_eq_one_left h1]
  exact slopeLatticeData.idealSmul_inv_cancel (slopeLatticeData.idealPow_ne_zero τ) L

theorem oneInputS (I n : Type) [Fintype n] [DecidableEq n] :
    MatrixLatticeEstimates.InputSG (I := I) (ι := fun _ => n) (fun _ => (1 : Matrix n n ℂ)) (fun _ => 1)
      (Fintype.card n : ℝ) 0 0 0 := by
  have hK : ∀ i j : I, MatrixLatticeEstimates.KpG (I := I) (ι := fun _ => n) (fun _ => (1 : Matrix n n ℂ)) (fun _ => 1) i j = 1 := by
    intro i j
    simp [MatrixLatticeEstimates.KpG]
  refine ⟨fun i j _ => ?_, fun i => ?_, ?_⟩
  · rw [hK, ProjectiveLineModels.hs_sq_one]
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h | h
    · simp [h]
    · have : (0 : ℝ) < (Fintype.card n : ℝ) := by exact_mod_cast h
      field_simp
      simp
  · unfold MatrixLatticeEstimates.KdG
    rw [hK]
    simp [HilbertSchmidtNormSquare.hsSq]
  · simp

theorem ball_entry (n n₁ : Type) [Fintype n] [Fintype n₁] [DecidableEq n] [DecidableEq n₁]
    (v : InfinitePlace K) (k j : n) :
    inclMat n n₁ (Sum.inl k) j = ((1 : Matrix n n ℂ)⁻¹
      * (LinearMap.toMatrix (Pi.basisFun K n) (Pi.basisFun K n) LinearMap.id).map v.embedding
      * (1 : Matrix n n ℂ)) k j := by
  simp [inclMat, Matrix.map_one, Matrix.one_apply]

section Model
variable (v : InfinitePlace K) (m f T p₁ t₁ Mw : ℕ) (hb : ℝ)

theorem model_card (hT : 4 ≤ T) :
    0 < (T - 2) ^ f ∧ (T - 2) ^ f ≤ (T - 1) ^ f ∧
    Fintype.card (Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f)) = (T - 1) ^ f := by
  have h1 : 0 < (T - 2) ^ f := Nat.pow_pos (by omega)
  have h2 : (T - 2) ^ f ≤ (T - 1) ^ f := Nat.pow_le_pow_left (by omega) f
  refine ⟨h1, h2, ?_⟩
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  omega

theorem model_lat (sg : ℝ) (hT : 4 ≤ T) (hsg : 0 < sg) (hsg20 : sg ≤ 1 / 20) (hMw : 1 / sg ≤ (Mw : ℝ)) :
    (modelFam K v m f T p₁ t₁ Mw hb).LatHyp sg := by
  obtain ⟨ha, hab, hcard⟩ := model_card f T hT
  have hMpos : 0 < Mw := by
    have : (0 : ℝ) < (Mw : ℝ) := lt_of_lt_of_le (by positivity) hMw
    exact_mod_cast this
  have hbpos : (0 : ℝ) < (((T - 1) ^ f : ℕ) : ℝ) := by exact_mod_cast lt_of_lt_of_le ha hab
  have hN' : ∀ u, (modelFam K v m f T p₁ t₁ Mw hb).N' u = stdLat K (Fin ((T - 2) ^ f)) :=
    fun u => modLat_cancel K (tau0 K p₁ t₁) (stdLat K (Fin ((T - 2) ^ f)))
  have hRs : MatrixLatticeEstimates.RsG (modelFam K v m f T p₁ t₁ Mw hb).ιf = (Mw : ℝ) * (((T - 1) ^ f : ℕ) : ℝ) := by
    show ∑ _i : Fin Mw, ((Fintype.card (Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f)) : ℕ) : ℝ) = _
    rw [hcard]
    simp
  have hdel : (modelFam K v m f T p₁ t₁ Mw hb).del
      = 1 - (((T - 2) ^ f : ℕ) : ℝ) / (((T - 1) ^ f : ℕ) : ℝ) := by
    show 1 - ((Fintype.card (Fin ((T - 2) ^ f)) : ℕ) : ℝ)
      / ((Fintype.card (Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f)) : ℕ) : ℝ) = _
    rw [hcard, Fintype.card_fin]
  have hapos : (0 : ℝ) < (((T - 2) ^ f : ℕ) : ℝ) := by exact_mod_cast ha
  have hable : (((T - 2) ^ f : ℕ) : ℝ) ≤ (((T - 1) ^ f : ℕ) : ℝ) := by exact_mod_cast hab
  refine ⟨⟨?_, ?_, ?_, ?_, ProjectiveLineModels.standard_lattice_fg K _, ProjectiveLineModels.standard_lattice_span_eq_top K _, ?_, ?_, ?_, ?_,
    fun _ _ => le_max_left _ _, ?_, ?_, ?_, ?_⟩, fun _ => one_pos, ?_, fun _ => ProjectiveLineModels.inclusion_matrix_isometry _ _, hbpos, hsg,
    hsg20, ?_, by show (-1 : ℝ) ≤ 0; norm_num, by show (0 : ℝ) ≤ sg / 2; positivity, by show (0 : ℝ) ≤ sg / 2; positivity, le_rfl, ?_, ?_⟩
  · intro w
    show IsUnit (1 : Matrix (Fin ((T - 2) ^ f)) (Fin ((T - 2) ^ f)) ℂ).det
    simp
  · intro i w
    show IsUnit ((((Real.exp (-(dT f T) / 2) : ℝ) : ℂ)) • (1 : Matrix (Fin ((T - 2) ^ f)) (Fin ((T - 2) ^ f)) ℂ)).det
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact (IsUnit.mk0 _ (by exact_mod_cast (Real.exp_pos _).ne')).pow _
  · intro i
    show IsUnit (1 : Matrix (Fin ((T - 2) ^ f)) (Fin ((T - 2) ^ f)) ℂ).det
    simp
  · show IsUnit (1 : Matrix (Fin ((T - 2) ^ f)) (Fin ((T - 2) ^ f)) ℂ).det
    simp
  · intro i
    rw [hN']
    exact ProjectiveLineModels.standard_lattice_fg K _
  · intro i
    rw [hN']
    exact ProjectiveLineModels.standard_lattice_span_eq_top K _
  · show 0 < ∑ _i : Fin Mw, Fintype.card (Fin ((T - 2) ^ f))
    simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    exact Nat.mul_pos hMpos ha
  · intro i
    rw [hN']
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  · rw [hdel, sub_nonneg, div_le_one hbpos]
    exact hable
  · rw [hdel]
    have : 0 < (((T - 2) ^ f : ℕ) : ℝ) / (((T - 1) ^ f : ℕ) : ℝ) := div_pos hapos hbpos
    linarith
  · rw [hdel]
    show _ * ((Fintype.card (Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f)) : ℕ) : ℝ)
      ≤ ((Fintype.card (Fin ((T - 2) ^ f)) : ℕ) : ℝ)
    rw [hcard, Fintype.card_fin]
    have : (1 - (1 - (((T - 2) ^ f : ℕ) : ℝ) / (((T - 1) ^ f : ℕ) : ℝ))) * (((T - 1) ^ f : ℕ) : ℝ)
        = (((T - 2) ^ f : ℕ) : ℝ) := by
      field_simp
      ring
    rw [this]
  · intro i k j
    exact ball_entry K _ _ v k j
  · intro i
    exact (Matrix.one_mul (inclMat (Fin ((T - 2) ^ f)) (Fin ((T - 1) ^ f - (T - 2) ^ f)))).symm
  · rw [hRs]
    show (((T - 1) ^ f : ℕ) : ℝ) / sg ≤ _
    calc (((T - 1) ^ f : ℕ) : ℝ) / sg = 1 / sg * (((T - 1) ^ f : ℕ) : ℝ) := by ring
      _ ≤ (Mw : ℝ) * (((T - 1) ^ f : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hMw hbpos.le
  · show Real.sqrt 0 ≤ sg / 2
    rw [Real.sqrt_zero]
    positivity
  · have := oneInputS (Fin Mw) (Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f))
    rw [hcard] at this
    exact this

end Model

section Model2
variable (v : InfinitePlace K) (m f T p₁ t₁ Mw : ℕ) (hb : ℝ)

variable {K} in
theorem lenSelf0 {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : slopeLatticeData.FinPl K) (L : Submodule (𝓞 K) V) :
    (slopeLatticeData.lenAt w L L).toNat = 0 := by
  rw [ProjectiveLineModels.local_length_self_eq_zero]
  rfl

variable {K} in
theorem exists_place {p : ℕ} (hp : p.Prime) : ∃ w : slopeLatticeData.FinPl K, prBelow w = p := by
  by_contra h
  push Not at h
  have h1 := sum_log_norm_over_prime (∅ : Finset (slopeLatticeData.FinPl K)) p hp (fun w hw => absurd hw (h w))
  rw [Finset.filter_empty, Finset.sum_empty] at h1
  have : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  linarith

variable {K} in
theorem sum_tau (hp : p₁.Prime) (S : Finset (slopeLatticeData.FinPl K)) (hS : ∀ w : slopeLatticeData.FinPl K, prBelow w = p₁ → w ∈ S) :
    ∑ w ∈ S, lE w * ((tau0 K p₁ t₁ w : ℝ) / ramE w) = (t₁ : ℝ) * Real.log (p₁ : ℝ) := by
  rw [← sum_log_norm_over_prime S p₁ hp hS, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [twist_vector_div_ramification]
  by_cases h : prBelow w = p₁
  · rw [if_pos ((mem_plOver hp w).2 h), if_pos h]; ring
  · rw [if_neg (fun h' => h ((mem_plOver hp w).1 h')), if_neg h]; ring

theorem model_place (bb : ℝ) (hm : 1 ≤ m) (hf : 1 ≤ f) (hTp : T.Prime) (hp : p₁.Prime) (hne : p₁ ≠ T)
    (hT4 : 4 * f ≤ T) (hsmall : 4 * (f : ℝ) / (T : ℝ) * bb ^ 2 + dT f T ≤ 1)
    (hTa : 2 * ((t₁ : ℝ) * Real.log (p₁ : ℝ)) ≤ bb ^ 2) :
    (modelFam K v m f T p₁ t₁ Mw hb).PlaceHyp f bb := by
  have hT : 4 ≤ T := by omega
  obtain ⟨ha, hab, hcard⟩ := model_card f T hT
  have hTr : (4 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hmemS : ∀ w : slopeLatticeData.FinPl K, w ∈ plOver K p₁ ∪ plOver K T ↔ prBelow w = p₁ ∨ prBelow w = T := by
    intro w
    rw [Finset.mem_union, mem_plOver hp, mem_plOver hTp]
  have hτnn : ∀ w : slopeLatticeData.FinPl K, 0 ≤ tau0 K p₁ t₁ w := by
    intro w
    rw [twist_vector_apply]
    split_ifs
    · positivity
    · exact le_rfl
  have hτR : ∀ w : slopeLatticeData.FinPl K, 0 ≤ (tau0 K p₁ t₁ w : ℝ) / ramE w := fun w =>
    div_nonneg (by exact_mod_cast hτnn w) (ramE_pos w).le
  have hτT : ∀ w : slopeLatticeData.FinPl K, prBelow w = T → tau0 K p₁ t₁ w = 0 := by
    intro w hw
    rw [twist_vector_apply, if_neg]
    intro h
    exact hne (((mem_plOver hp w).1 h).symm.trans hw)
  have hdu : ∀ u, (modelFam K v m f T p₁ t₁ Mw hb).du u = (((T - 2) ^ f : ℕ) : ℝ) := by
    intro u
    show ((Fintype.card (Fin ((T - 2) ^ f)) : ℕ) : ℝ) = _
    rw [Fintype.card_fin]
  have hdM : ∀ u, (modelFam K v m f T p₁ t₁ Mw hb).dM u = (((T - 1) ^ f : ℕ) : ℝ) := by
    intro u
    show ((Fintype.card (Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f)) : ℕ) : ℝ) = _
    rw [hcard]
  have hable : (((T - 2) ^ f : ℕ) : ℝ) ≤ (((T - 1) ^ f : ℕ) : ℝ) := by exact_mod_cast hab
  have hbnn : (0 : ℝ) ≤ (((T - 1) ^ f : ℕ) : ℝ) := Nat.cast_nonneg _
  have hτoff : ∀ w : slopeLatticeData.FinPl K, w ∉ plOver K p₁ ∪ plOver K T → tau0 K p₁ t₁ w = 0 := by
    intro w hw
    rw [twist_vector_apply, if_neg]
    exact fun h => hw (Finset.mem_union_left _ h)
  have hlen : ∀ u (w : slopeLatticeData.FinPl K), (modelFam K v m f T p₁ t₁ Mw hb).lenN u w = 0 := fun u w =>
    lenSelf0 w (Formalism.HermitianLatticesTheory.idealSmul ((slopeLatticeData.idealPow (tau0 K p₁ t₁) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (stdLat K (Fin ((T - 2) ^ f))))
  have hlenR : ∀ u (w : slopeLatticeData.FinPl K), (modelFam K v m f T p₁ t₁ Mw hb).lenR u w
      = (((T - 2) ^ f : ℕ) : ℝ) * ((tau0 K p₁ t₁ w : ℝ) / ramE w) := by
    intro u w
    unfold Fam.lenR
    rw [hlen, hdu]
    show (((0 : ℕ) : ℝ) + (((T - 2) ^ f : ℕ) : ℝ) * (tau0 K p₁ t₁ w : ℝ)) / ramE w = _
    rw [Nat.cast_zero, zero_add, mul_div_assoc]
  have hrank : (((T - 2) ^ f : ℕ) : ℝ) = (((T - 1) ^ f : ℕ) : ℝ) * (1 - 1 / ((T : ℝ) - 1)) ^ f := by
    have h1 : ((T - 2 : ℕ) : ℝ) = (T : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have h2 : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [Nat.cast_pow, Nat.cast_pow, h1, h2, ← mul_pow]
    congr 1
    have : (T : ℝ) - 1 ≠ 0 := by linarith
    rw [mul_sub, mul_one, mul_one_div_cancel this]
    ring
  have hoffT : ∀ u (w : slopeLatticeData.FinPl K), (modelFam K v m f T p₁ t₁ Mw hb).lenR u w
      ≤ (modelFam K v m f T p₁ t₁ Mw hb).dM u * ((tau0 K p₁ t₁ w : ℝ) / ramE w + 1) := by
    intro u w
    rw [hlenR, hdM]
    have := hτR w
    nlinarith
  have hovT : ∀ u (w : slopeLatticeData.FinPl K), prBelow w = T → (modelFam K v m f T p₁ t₁ Mw hb).lenR u w
      ≤ (modelFam K v m f T p₁ t₁ Mw hb).dM u * 1 := by
    intro u w hw
    rw [hlenR, hdM, hτT w hw]
    simp
  have hround : ∀ w : slopeLatticeData.FinPl K, (tau0 K p₁ t₁ w : ℝ) / ramE w
      ≤ ∑ _j : Fin m, ((tau0 K p₁ t₁ w : ℝ) / ramE w + 1 + 1 / 2 - 1 / 4) := by
    intro w
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h2 := hτR w
    exact le_trans (by linarith) (le_mul_of_one_le_left (by linarith) h1)
  have hdT : 0 ≤ dT f T := by
    unfold dT
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))) (by linarith)
  have : Nonempty (Fin ((T - 2) ^ f)) := ⟨⟨0, ha⟩⟩
  have hsc := scaled_std K (Fin ((T - 2) ^ f)) (Real.exp (-(dT f T) / 2)) (Real.exp_pos _)
  rw [Real.log_exp] at hsc
  refine ⟨fun w _ => hτnn w, ?_, fun _ _ => zero_le_one, ?_, ?_, fun u => ⟨ProjectiveLineModels.standard_lattice_fg K _,
    ProjectiveLineModels.standard_lattice_span_eq_top K _, ProjectiveLineModels.standard_lattice_fg K _, ProjectiveLineModels.standard_lattice_span_eq_top K _, le_refl _,
    slopeLatticeData.rkK_idealSmul (slopeLatticeData.idealPow_ne_zero _) _, ?_, by exact_mod_cast hT4, ?_, ?_, ?_, ?_, ?_, zero_le_one, ?_, ?_,
    ?_, hsmall⟩⟩
  · exact fun w hw => hτoff w hw
  · intro w hw w' hw'
    rcases (hmemS w).1 hw with h | h
    · exact (hmemS w').2 (Or.inl (hw'.trans h))
    · exact (hmemS w').2 (Or.inr (hw'.trans h))
  · show 2 * ∑ w ∈ plOver K p₁ ∪ plOver K T, lE w * ((tau0 K p₁ t₁ w : ℝ) / ramE w) ≤ bb ^ 2
    rw [sum_tau p₁ t₁ hp _ (fun w hw => (hmemS w).2 (Or.inl hw))]
    exact hTa
  · intro w hw
    exact ⟨hτoff w hw, hlen u w⟩
  · obtain ⟨w, hw⟩ := exists_place (K := K) hTp
    exact Finset.mem_image.2 ⟨w, (hmemS w).2 (Or.inr hw), hw⟩
  · intro w hw
    exact hτT w (Finset.mem_filter.1 hw).2
  · show (modelFam K v m f T p₁ t₁ Mw hb).du u = (modelFam K v m f T p₁ t₁ Mw hb).dM u * (1 - 1 / ((T : ℝ) - 1)) ^ f
    rw [hdu, hdM]
    exact hrank
  · exact fun w _ => hoffT u w
  · exact fun w hw => hovT u w (Finset.mem_filter.1 hw).2
  · exact fun w _ => hround w
  · show muDef (Pi.basisFun K (Fin ((T - 2) ^ f))) (fun _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1)
        (stdLat K (Fin ((T - 2) ^ f)))
      = muDef (Pi.basisFun K (Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f))) (fun _ => 1) (stdLat K _)
        - dT f T
    rw [hsc.1, mu_std]
    ring
  · show muMaxDef (Pi.basisFun K (Fin ((T - 2) ^ f))) (fun _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1)
        (stdLat K (Fin ((T - 2) ^ f)))
      ≤ muMaxDef (Pi.basisFun K (Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f))) (fun _ => 1) (stdLat K _)
    rw [hsc.2]
    have := muMax_incl K (Fin ((T - 2) ^ f)) (Fin ((T - 1) ^ f - (T - 2) ^ f))
    linarith

end Model2

end ModelLemmas

theorem levelPrime (f : ℕ) (bb : ℝ) (hf : 1 ≤ f) (n0 : ℕ) :
    ∃ T : ℕ, T.Prime ∧ n0 ≤ T ∧ 4 * f ≤ T ∧
      4 * (f : ℝ) / (T : ℝ) * bb ^ 2 + (f : ℝ) * Real.log ((T : ℝ) - 1) / ((T : ℝ) - 2) ≤ 1 := by
  obtain ⟨T, hTge, hTp⟩ := Nat.exists_infinite_primes (n0 + 64 * f ^ 2 + ⌈8 * (f : ℝ) * bb ^ 2⌉₊ + 5)
  have hfr : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have h1 : (64 * (f : ℝ) ^ 2 + 5 : ℝ) ≤ (T : ℝ) := by
    have : 64 * f ^ 2 + 5 ≤ T := by omega
    exact_mod_cast this
  have h2 : 8 * (f : ℝ) * bb ^ 2 ≤ (T : ℝ) := by
    have h3 : (⌈8 * (f : ℝ) * bb ^ 2⌉₊ : ℝ) ≤ (T : ℝ) := by
      have : ⌈8 * (f : ℝ) * bb ^ 2⌉₊ ≤ T := by omega
      exact_mod_cast this
    exact le_trans (Nat.le_ceil _) h3
  have hTpos : (0 : ℝ) < (T : ℝ) := by nlinarith
  refine ⟨T, hTp, by omega, ?_, ?_⟩
  · have : 4 * f ≤ 64 * f ^ 2 := by nlinarith
    omega
  · have hA : 4 * (f : ℝ) / (T : ℝ) * bb ^ 2 ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hTpos]
      linarith
    set y : ℝ := (T : ℝ) - 1 with hy
    have hy1 : 64 * (f : ℝ) ^ 2 + 4 ≤ y := by rw [hy]; linarith
    have hypos : 0 < y := by nlinarith
    have hs : 8 * (f : ℝ) ≤ Real.sqrt y := by
      rw [show 8 * (f : ℝ) = Real.sqrt ((8 * (f : ℝ)) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hspos : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos
    have hlog : Real.log y ≤ 2 * Real.sqrt y := by
      have h4 := Real.log_le_sub_one_of_pos hspos
      have h5 : Real.log y = 2 * Real.log (Real.sqrt y) := by
        rw [Real.log_sqrt hypos.le]; ring
      rw [h5]; linarith
    have hsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hypos.le
    have hB : (f : ℝ) * Real.log y / ((T : ℝ) - 2) ≤ 1 / 2 := by
      have hden : 0 < (T : ℝ) - 2 := by nlinarith
      rw [div_le_iff₀ hden]
      have h6 : (T : ℝ) - 2 = y - 1 := by rw [hy]; ring
      rw [h6]
      have h7 : (f : ℝ) * Real.log y ≤ (f : ℝ) * (2 * Real.sqrt y) :=
        mul_le_mul_of_nonneg_left hlog (by linarith)
      have h8 : (f : ℝ) * (2 * Real.sqrt y) ≤ Real.sqrt y * Real.sqrt y / 4 := by nlinarith
      rw [hsq] at h8
      nlinarith
    linarith

theorem family_model : FamModel := by
  intro K _ _ _ _ v m f T p₁ t₁ Mw bb sg hb hm hf hTp hp hne hT4 hsmall hTa hsg hsg20 hMw
  have hT : 4 ≤ T := by omega
  obtain ⟨ha, hab, hcard⟩ := model_card f T hT
  have hlt : (T - 2) ^ f < (T - 1) ^ f := Nat.pow_lt_pow_left (by omega) (by omega)
  have hdu : ∀ u, (modelFam K v m f T p₁ t₁ Mw hb).du u = (((T - 2) ^ f : ℕ) : ℝ) := by
    intro u
    show ((Fintype.card (Fin ((T - 2) ^ f)) : ℕ) : ℝ) = _
    rw [Fintype.card_fin]
  have hdM : ∀ u, (modelFam K v m f T p₁ t₁ Mw hb).dM u = (((T - 1) ^ f : ℕ) : ℝ) := by
    intro u
    show ((Fintype.card (Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f)) : ℕ) : ℝ) = _
    rw [hcard]
  have hapos : (0 : ℝ) < (((T - 2) ^ f : ℕ) : ℝ) := by exact_mod_cast ha
  have hltR : (((T - 2) ^ f : ℕ) : ℝ) < (((T - 1) ^ f : ℕ) : ℝ) := by exact_mod_cast hlt
  have hmemS : ∀ w : slopeLatticeData.FinPl K, w ∈ plOver K p₁ ∪ plOver K T ↔ prBelow w = p₁ ∨ prBelow w = T := by
    intro w
    rw [Finset.mem_union, mem_plOver hp, mem_plOver hTp]
  have hτR : ∀ w : slopeLatticeData.FinPl K, 0 ≤ (tau0 K p₁ t₁ w : ℝ) / ramE w := by
    intro w
    rw [twist_vector_div_ramification]
    split_ifs
    · positivity
    · exact le_rfl
  have hRd : 0 < ∑ w ∈ plOver K p₁ ∪ plOver K T, 2 * lE w *
      ((∑ _j : Fin m, ((tau0 K p₁ t₁ w : ℝ) / ramE w + 1 + 1 / 2 - 1 / 4)) - (tau0 K p₁ t₁ w : ℝ) / ramE w) := by
    have h1 : ∀ w : slopeLatticeData.FinPl K, 2 * lE w ≤ 2 * lE w *
        ((∑ _j : Fin m, ((tau0 K p₁ t₁ w : ℝ) / ramE w + 1 + 1 / 2 - 1 / 4)) - (tau0 K p₁ t₁ w : ℝ) / ramE w) := by
      intro w
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h2 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have h3 := hτR w
      have h4 : (tau0 K p₁ t₁ w : ℝ) / ramE w + 1 + 1 / 2 - 1 / 4
          ≤ (m : ℝ) * ((tau0 K p₁ t₁ w : ℝ) / ramE w + 1 + 1 / 2 - 1 / 4) :=
        le_mul_of_one_le_left (by linarith) h2
      exact le_mul_of_one_le_right (mul_nonneg two_pos.le (lE_nonneg w)) (by linarith)
    have h5 : 2 * Real.log (p₁ : ℝ) ≤ ∑ w ∈ plOver K p₁ ∪ plOver K T, 2 * lE w := by
      rw [← sum_log_norm_over_prime (plOver K p₁ ∪ plOver K T) p₁ hp (fun w hw => (hmemS w).2 (Or.inl hw)), Finset.mul_sum]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun w _ _ => mul_nonneg two_pos.le (lE_nonneg w))
    have h6 : 0 < Real.log (p₁ : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
    have h7 := Finset.sum_le_sum (s := plOver K p₁ ∪ plOver K T) (fun w _ => h1 w)
    linarith
  refine ⟨modelFam K v m f T p₁ t₁ Mw hb, model_lat K v m f T p₁ t₁ Mw hb sg hT hsg hsg20 hMw,
    model_place K v m f T p₁ t₁ Mw hb bb hm hf hTp hp hne hT4 hsmall hTa, fun u => ⟨?_, ?_, rfl, le_max_right _ _, hRd⟩,
    ?_, ?_, ?_⟩
  · rw [hdu]; exact hapos
  · rw [hdu, hdM]; exact hltR
  · show 0 < 1 - ((Fintype.card (Fin ((T - 2) ^ f)) : ℕ) : ℝ)
      / ((Fintype.card (Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f)) : ℕ) : ℝ)
    rw [hcard, Fintype.card_fin, sub_pos, div_lt_one (lt_trans hapos hltR)]
    exact hltR
  · obtain ⟨w, hw⟩ := exists_place (K := K) hp
    exact ⟨w, (hmemS w).2 (Or.inl hw), hw⟩
  · have h1 : ∀ w : slopeLatticeData.FinPl K, prBelow w = p₁ → (tau0 K p₁ t₁ w : ℝ) / ramE w = (t₁ : ℝ) := by
      intro w hw
      rw [twist_vector_div_ramification, if_pos ((mem_plOver hp w).2 hw)]
    exact fun w _ hw => ⟨h1 w hw, fun _ => h1 w hw⟩

section DataL
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DataL

theorem absorb1 {ι : Type} [Fintype ι] (g : ι → ℝ) (i : ι) : |g i| ≤ ∑ i, |g i| :=
  Finset.single_le_sum (f := fun i => |g i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem absorb2 {ι : Type} {κ : ι → Type} [Fintype ι] [∀ i, Fintype (κ i)] (g : ∀ i, κ i → ℝ) (i : ι) (j : κ i) :
    |g i j| ≤ ∑ i, ∑ j, |g i j| :=
  le_trans (Finset.single_le_sum (f := fun j => |g i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))
    (Finset.single_le_sum (f := fun i => ∑ j, |g i j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))

theorem wmean_const {ι : Type} [Fintype ι] (d : ι → ℝ) (c : ℝ) (hd : ∑ i, d i ≠ 0) :
    wmean d (fun _ => c) = c := by
  unfold wmean
  rw [← Finset.sum_mul, mul_div_assoc, mul_comm, div_mul_cancel₀ _ hd]

theorem constsExist {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] {Top : Type} [Fintype Top]
    {m f : ℕ} (Dd : Data U0 W Top m f) (eDiv eLoss cHH c0 : ℝ)
    (hx : 0 < Dd.x) (hnT : 0 < Dd.nT) (ha : 0 < Dd.a) (hLa : 0 < Dd.La) (hm : 1 ≤ m) (hB0 : 0 < Dd.B0)
    (hNc : 0 ≤ Dd.Nc) (hb : 0 < Dd.b) (hL : 0 < Dd.L) (hk : 1 ≤ Dd.k) (hT : ∀ u0 u, 1 ≤ Dd.T u0 u)
    (hhw : ∀ u0 u u', Dd.h u0 u = Dd.h u0 u') (hTw : ∀ u0 u u', Dd.T u0 u = Dd.T u0 u') :
    ∃ cDiv cE cCount cSlope cLoss : ℝ, 0 ≤ cDiv ∧ 0 ≤ cE ∧ 0 ≤ cCount ∧ 0 ≤ cSlope ∧ 0 ≤ cLoss ∧
      Dd.DIV ⟨cDiv, eDiv, cE, 0, cCount, cSlope, c0, cLoss, eLoss, cHH⟩ ∧
      EComp5 Dd ⟨cDiv, eDiv, cE, 0, cCount, cSlope, c0, cLoss, eLoss, cHH⟩ ∧
      Dd.HComp ⟨cDiv, eDiv, cE, 0, cCount, cSlope, c0, cLoss, eLoss, cHH⟩ ∧
      Count5 Dd ⟨cDiv, eDiv, cE, 0, cCount, cSlope, c0, cLoss, eLoss, cHH⟩ ∧
      Dd.Slopes ⟨cDiv, eDiv, cE, 0, cCount, cSlope, c0, cLoss, eLoss, cHH⟩ ∧
      LossBounds Dd ⟨cDiv, eDiv, cE, 0, cCount, cSlope, c0, cLoss, eLoss, cHH⟩ := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hk0 : 0 < Dd.k := by linarith
  have hP1 : 0 < Dd.nT * Dd.a * Dd.La := mul_pos (mul_pos hnT ha) hLa
  have hP2 : 0 < (m : ℝ) * Dd.B0 := mul_pos (by linarith) hB0
  have hP5 : 0 < Dd.nT * (m : ℝ) * Dd.b * Dd.x ^ (eLoss * Dd.ε) :=
    mul_pos (mul_pos (mul_pos hnT (by linarith)) hb) (Real.rpow_pos_of_pos hx _)
  set S1 := ∑ u0, ∑ u : W u0, |Dd.muCC u0 + Dd.h u0 u - Dd.Fo u0
    - ∑ t, ((m : ℝ) * (ph (Dd.aT t) - Dd.aT t * Dd.logOm) - Dd.aT t * Real.log (Dd.T u0 u))| with hS1
  set S2 := ∑ u0, ∑ u : W u0, |Dd.Ee u0 u - (m : ℝ) * Dd.sumA * Dd.lg| with hS2
  set S3 := ∑ u0, |(∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (Dd.w u0 j ρ * Dd.v / Real.pi))
    + (m : ℝ) * Dd.lg| with hS3
  set S4 := ∑ u0, ∑ u : W u0, |Real.log (Dd.T u0 u)| with hS4
  set S5 := ∑ u0, ∑ u : W u0, |Dd.muM u0 u| with hS5
  set S6 := ∑ u0, ∑ u : W u0, |Dd.muMaxM u0 u| with hS6
  set S7 := ∑ u0, |Dd.ASK u0 - Dd.Ga u0| with hS7
  set S8 := ∑ u0, |Dd.IO u0| with hS8
  have n1 : 0 ≤ S1 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n2 : 0 ≤ S2 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n3 : 0 ≤ S3 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n4 : 0 ≤ S4 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n5 : 0 ≤ S5 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n6 : 0 ≤ S6 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n7 : 0 ≤ S7 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n8 : 0 ≤ S8 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨S1 / (Dd.nT * Dd.a * Dd.La), S2 / ((m : ℝ) * Dd.B0), S3 / Dd.La + S4 / Dd.L,
    (S5 + S6) / (Dd.nT * Dd.a * Dd.La), (S7 + S8) / (Dd.nT * (m : ℝ) * Dd.b * Dd.x ^ (eLoss * Dd.ε)),
    by positivity, by positivity, by positivity, by positivity, by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u0 u
    show Dd.muCC u0 + Dd.h u0 u - Dd.Fo u0 ≤
      (∑ t, ((m : ℝ) * (ph (Dd.aT t) - Dd.aT t * Dd.logOm) - Dd.aT t * Real.log (Dd.T u0 u)))
        + S1 / (Dd.nT * Dd.a * Dd.La) * Dd.nT * Dd.a * Dd.La
        + S1 / (Dd.nT * Dd.a * Dd.La) * (m : ℝ) * (Dd.B0 + Dd.Nc) * Dd.x ^ (eDiv * Dd.ε)
    have h1 := le_trans (le_abs_self _) (absorb2 (fun (u0 : U0) (u : W u0) => Dd.muCC u0 + Dd.h u0 u - Dd.Fo u0
      - ∑ t, ((m : ℝ) * (ph (Dd.aT t) - Dd.aT t * Dd.logOm) - Dd.aT t * Real.log (Dd.T u0 u))) u0 u)
    have h2 : S1 / (Dd.nT * Dd.a * Dd.La) * Dd.nT * Dd.a * Dd.La = S1 := by
      calc _ = S1 / (Dd.nT * Dd.a * Dd.La) * (Dd.nT * Dd.a * Dd.La) := by ring
        _ = S1 := div_mul_cancel₀ _ hP1.ne'
    have h3 : 0 ≤ S1 / (Dd.nT * Dd.a * Dd.La) * (m : ℝ) * (Dd.B0 + Dd.Nc) * Dd.x ^ (eDiv * Dd.ε) := by
      have : 0 < Dd.x ^ (eDiv * Dd.ε) := Real.rpow_pos_of_pos hx _
      positivity
    rw [h2]
    linarith
  · intro u0 u
    show |Dd.Ee u0 u - (m : ℝ) * Dd.sumA * Dd.lg| ≤ S2 / ((m : ℝ) * Dd.B0) * (m : ℝ) * Dd.B0
    have h2 : S2 / ((m : ℝ) * Dd.B0) * (m : ℝ) * Dd.B0 = S2 := by
      calc _ = S2 / ((m : ℝ) * Dd.B0) * ((m : ℝ) * Dd.B0) := by ring
        _ = S2 := div_mul_cancel₀ _ hP2.ne'
    rw [h2]
    exact absorb2 (fun (u0 : U0) (u : W u0) => Dd.Ee u0 u - (m : ℝ) * Dd.sumA * Dd.lg) u0 u
  · intro u0 u u'
    rw [hhw u0 u u', hTw u0 u u', sub_self, abs_zero]
    show (0 : ℝ) ≤ 0 * _
    rw [zero_mul]
  · intro u0 u
    have hc : 0 ≤ S3 / Dd.La + S4 / Dd.L := by positivity
    have hlog : 0 ≤ Real.log (Dd.T u0 u) := Real.log_nonneg (hT u0 u)
    refine ⟨?_, ?_, fun u' => ?_⟩
    · show (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (Dd.w u0 j ρ * Dd.v / Real.pi)) + (m : ℝ) * Dd.lg
        - (S3 / Dd.La + S4 / Dd.L) * (Dd.La + (m : ℝ) ^ 2 * Dd.La / Dd.k) ≤ Real.log (Dd.T u0 u)
      have h1 := le_trans (le_abs_self _) (absorb1 (fun u0 : U0 =>
        (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (Dd.w u0 j ρ * Dd.v / Real.pi)) + (m : ℝ) * Dd.lg) u0)
      have h2 : S3 ≤ (S3 / Dd.La + S4 / Dd.L) * (Dd.La + (m : ℝ) ^ 2 * Dd.La / Dd.k) := by
        have e1 : S3 = S3 / Dd.La * Dd.La := (div_mul_cancel₀ _ hLa.ne').symm
        have e2 : 0 ≤ S3 / Dd.La * ((m : ℝ) ^ 2 * Dd.La / Dd.k) := by positivity
        have e3 : 0 ≤ S4 / Dd.L * (Dd.La + (m : ℝ) ^ 2 * Dd.La / Dd.k) := by positivity
        nlinarith
      linarith
    · show Real.log (Dd.T u0 u) ≤ (S3 / Dd.La + S4 / Dd.L) * (m : ℝ) * Dd.L
      have h1 := le_trans (le_abs_self _) (absorb2 (fun (u0 : U0) (u : W u0) => Real.log (Dd.T u0 u)) u0 u)
      have e1 : S4 = S4 / Dd.L * Dd.L := (div_mul_cancel₀ _ hL.ne').symm
      have e2 : S4 / Dd.L * Dd.L ≤ (S3 / Dd.La + S4 / Dd.L) * (m : ℝ) * Dd.L := by
        have e3 : S4 / Dd.L ≤ (S3 / Dd.La + S4 / Dd.L) * (m : ℝ) := by
          have e4 : 0 ≤ S3 / Dd.La := by positivity
          have e5 : 0 ≤ S4 / Dd.L := by positivity
          nlinarith
        exact mul_le_mul_of_nonneg_right e3 hL.le
      linarith
    · rw [hTw u0 u u', sub_self, abs_zero]
      exact mul_nonneg hc (Real.log_nonneg hk)
  · intro u0 u
    have h5 := absorb2 (fun (u0 : U0) (u : W u0) => Dd.muM u0 u) u0 u
    have h6 := absorb2 (fun (u0 : U0) (u : W u0) => Dd.muMaxM u0 u) u0 u
    have h2 : (S5 + S6) / (Dd.nT * Dd.a * Dd.La) * Dd.nT * Dd.a * Dd.La = S5 + S6 := by
      calc _ = (S5 + S6) / (Dd.nT * Dd.a * Dd.La) * (Dd.nT * Dd.a * Dd.La) := by ring
        _ = S5 + S6 := div_mul_cancel₀ _ hP1.ne'
    constructor
    · show -((S5 + S6) / (Dd.nT * Dd.a * Dd.La) * Dd.nT * Dd.a * Dd.La * (1 + (m : ℝ) / Dd.k)) ≤ Dd.muM u0 u
      rw [h2]
      have e1 : 0 ≤ (S5 + S6) * ((m : ℝ) / Dd.k) := by positivity
      have e2 := neg_abs_le (Dd.muM u0 u)
      nlinarith
    · show Dd.muMaxM u0 u ≤ (S5 + S6) / (Dd.nT * Dd.a * Dd.La) * Dd.nT * Dd.a * Dd.La
      rw [h2]
      have e2 := le_abs_self (Dd.muMaxM u0 u)
      linarith
  · intro u0
    have h2 : Dd.LoP ⟨S1 / (Dd.nT * Dd.a * Dd.La), eDiv, S2 / ((m : ℝ) * Dd.B0), 0, S3 / Dd.La + S4 / Dd.L,
        (S5 + S6) / (Dd.nT * Dd.a * Dd.La), c0,
        (S7 + S8) / (Dd.nT * (m : ℝ) * Dd.b * Dd.x ^ (eLoss * Dd.ε)), eLoss, cHH⟩ = S7 + S8 := by
      show (S7 + S8) / (Dd.nT * (m : ℝ) * Dd.b * Dd.x ^ (eLoss * Dd.ε)) * Dd.nT * (m : ℝ) * Dd.b
        * Dd.x ^ (eLoss * Dd.ε) = S7 + S8
      calc _ = (S7 + S8) / (Dd.nT * (m : ℝ) * Dd.b * Dd.x ^ (eLoss * Dd.ε))
            * (Dd.nT * (m : ℝ) * Dd.b * Dd.x ^ (eLoss * Dd.ε)) := by ring
        _ = S7 + S8 := div_mul_cancel₀ _ hP5.ne'
    rw [h2]
    have h7 := le_trans (le_abs_self _) (absorb1 (fun u0 : U0 => Dd.ASK u0 - Dd.Ga u0) u0)
    have h8 := le_trans (le_abs_self _) (absorb1 (fun u0 : U0 => Dd.IO u0) u0)
    exact ⟨by linarith, by linarith⟩

set_option maxHeartbeats 1000000 in
theorem sizeData_model : ArithDataModel := by
  intro K _ _ _ _ v0 H _ _ _ D ell N TT T2 m a w x ε k La v lg cHH eDiv eLoss hx hε hk hLa hv hm hTT hsg20
  have hx0 : 0 < x := by linarith
  have hk0 : 0 < k := by linarith
  have hsg : 0 < x ^ (-cHH) := Real.rpow_pos_of_pos hx0 _
  have hf : 1 ≤ (PhiSet (H := H)).card := phi_card_pos
  have hfr : (1 : ℝ) ≤ ((PhiSet (H := H)).card : ℝ) := by exact_mod_cast hf
  have hb : 0 < bTx x ε := Real.exp_pos _
  have hb2 : 2 ≤ bTx x ε := by
    have h1 : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
    have := Real.add_one_le_exp (x ^ ε)
    unfold bTx
    linarith
  obtain ⟨T, hTp, hTn0, hT4, hsmall⟩ := levelPrime (PhiSet (H := H)).card (bTx x ε) hf
    (⌈18 * ((PhiSet (H := H)).card : ℝ) / (x ^ (-cHH)) ^ 2⌉₊ + 3)
  have hT : 4 ≤ T := by omega
  have hTr : (4 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hMw : 1 / x ^ (-cHH) ≤ ((⌈1 / x ^ (-cHH)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hMw2 : ((⌈1 / x ^ (-cHH)⌉₊ : ℕ) : ℝ) < x ^ cHH + 1 := by
    have h1 : 1 / x ^ (-cHH) = x ^ cHH := by
      rw [Real.rpow_neg hx0.le, one_div, inv_inv]
    rw [h1]
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le _)
  have hMpos : 0 < ⌈1 / x ^ (-cHH)⌉₊ := Nat.ceil_pos.2 (by positivity)
  have hTa : 2 * (((1 : ℕ) : ℝ) * Real.log ((2 : ℕ) : ℝ)) ≤ bTx x ε ^ 2 := by
    have h1 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos two_pos
    push_cast
    nlinarith
  obtain ⟨ha, hab, hcard⟩ := model_card (PhiSet (H := H)).card T hT
  set Mw : ℕ := ⌈1 / x ^ (-cHH)⌉₊ with hMwdef
  set F : Fam (Fin Mw) m := modelFam K v0 m (PhiSet (H := H)).card T 2 1 Mw
    (muDef (Pi.basisFun K (Fin ((T - 2) ^ (PhiSet (H := H)).card)))
        (fun _ => ((Real.exp (-(dT (PhiSet (H := H)).card T) / 2) : ℝ) : ℂ) • 1) (ProjectiveLineModels.stdLat K _)
      - muMinDef (Pi.basisFun K (Fin ((T - 2) ^ (PhiSet (H := H)).card))) (fun _ => 1) (ProjectiveLineModels.stdLat K _)) with hF
  have hLat : F.LatHyp (x ^ (-cHH)) := model_lat K v0 m _ T 2 1 Mw _ _ hT hsg hsg20 hMw
  have hPl : F.PlaceHyp (PhiSet (H := H)).card (bTx x ε) :=
    model_place K v0 m _ T 2 1 Mw _ _ hm hf hTp Nat.prime_two (by omega) hT4 hsmall hTa
  have hdu : ∀ u, F.du u = (((T - 2) ^ (PhiSet (H := H)).card : ℕ) : ℝ) := by
    intro u
    show ((Fintype.card (Fin ((T - 2) ^ (PhiSet (H := H)).card)) : ℕ) : ℝ) = _
    rw [Fintype.card_fin]
  have hdupos : ∀ u, 0 < F.du u := fun u => by rw [hdu]; exact_mod_cast ha
  have hrk := ranks_of_places (Fin Mw) F _ _ hf (by nlinarith) hdupos hPl
  set G : Glob := ⟨x, ε, k, La, v, lg, 1 / 4, 6 * x ^ (-cHH), 0⟩ with hG
  set Dd := mkData (W := fun _ : H => Fin Mw) G cHH D ell N TT T2 a w (fun _ => F) with hDd
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hnT : (0 : ℝ) < Dd.nT := by
    show (0 : ℝ) < ((Fintype.card TT : ℕ) : ℝ)
    rw [Fintype.card_coe]
    exact_mod_cast hTT.card_pos
  have hnH : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have haa : (0 : ℝ) < Dd.a := mul_pos hx0 hb
  have hP1 : 0 < Dd.nT * Dd.a * Dd.La := mul_pos (mul_pos hnT haa) hLa
  have hxe : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 _
  have hB0 : 0 < Dd.B0 := by
    show 0 < (2 * (Fintype.card H : ℝ)) * m * bTx x ε * x ^ ε
    positivity
  have hNc : 0 ≤ Dd.Nc := by
    show 0 ≤ (T2.card : ℝ) * k * bTx x ε * x ^ ε / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε)))
    have := Real.rpow_pos_of_pos hx0 (-ε)
    positivity
  have hL : 0 < Dd.L := by
    show 0 < Real.log (bTx x ε)
    exact Real.log_pos (by linarith)
  have hlogT : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by linarith)
  have hN' : ∀ u, F.N' u = ProjectiveLineModels.stdLat K (Fin ((T - 2) ^ (PhiSet (H := H)).card)) :=
    fun u => modLat_cancel K (tau0 K 2 1) (ProjectiveLineModels.stdLat K (Fin ((T - 2) ^ (PhiSet (H := H)).card)))

  have hbp : 0 < bpTx x ε := div_pos (mul_pos hx0 hb) (Real.exp_pos _)
  have hP3 : 0 < (TT.card : ℝ) * (m : ℝ) * (aTx x ε / k + bpTx x ε) := by
    have h1 : (0 : ℝ) < (TT.card : ℝ) := by exact_mod_cast hTT.card_pos
    have h2 : 0 < aTx x ε := mul_pos hx0 hb
    positivity
  have hXpp : 0 < XppH H G := by
    show 0 < aTx x ε / (bpTx x ε / (x * (Fintype.card H : ℝ)))
    have h2 : 0 < aTx x ε := mul_pos hx0 hb
    positivity
  have hSz : ∀ (u : Fin Mw), F.lam u ≤ 1 / ((TT.card : ℝ) * (m : ℝ) * (aTx x ε / k + bpTx x ε)) * (TT.card : ℝ)
        * (m : ℝ) * (aTx x ε / k + bpTx x ε) ∧
      F.Rd u ≤ (4 + 4 * (1 / ((TT.card : ℝ) * (m : ℝ) * (aTx x ε / k + bpTx x ε)))
        + (∑ u, |F.Rd u|) / XppH H G) * XppH H G := by
    intro u
    constructor
    · have e1 : 1 / ((TT.card : ℝ) * (m : ℝ) * (aTx x ε / k + bpTx x ε)) * (TT.card : ℝ)
          * (m : ℝ) * (aTx x ε / k + bpTx x ε) = 1 := by
        calc _ = 1 / ((TT.card : ℝ) * (m : ℝ) * (aTx x ε / k + bpTx x ε))
              * ((TT.card : ℝ) * (m : ℝ) * (aTx x ε / k + bpTx x ε)) := by ring
          _ = 1 := div_mul_cancel₀ _ hP3.ne'
      rw [e1]
      exact le_refl (1 : ℝ)
    · have e1 := le_trans (le_abs_self _) (absorb1 (fun u => F.Rd u) u)
      have e2 : (∑ u, |F.Rd u|) / XppH H G * XppH H G = ∑ u, |F.Rd u| := div_mul_cancel₀ _ hXpp.ne'
      have e3 : 0 ≤ (4 + 4 * (1 / ((TT.card : ℝ) * (m : ℝ) * (aTx x ε / k + bpTx x ε)))) * XppH H G := by
        positivity
      nlinarith
  have hSabs : 0 ≤ (∑ u, |F.Rd u|) / XppH H G :=
    div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) hXpp.le
  have hcT : 0 ≤ 1 / ((TT.card : ℝ) * (m : ℝ) * (aTx x ε / k + bpTx x ε)) := by positivity

  have hsum : ∑ u : Fin Mw, F.du u ≠ 0 := by
    have : 0 < ∑ u : Fin Mw, F.du u :=
      Finset.sum_pos (fun u _ => hdupos u) ⟨⟨0, hMpos⟩, Finset.mem_univ _⟩
    exact this.ne'
  have hHH : ∀ u0 : H, Dd.s u0 - muMinDef F.b' F.X' F.cc ≤ x ^ cHH * bTx x ε := by
    intro u0
    have hfun : (fun u : Fin Mw => Dd.muN u0 u - Dd.h u0 u) = fun _ =>
        muDef (Pi.basisFun K (Fin ((T - 2) ^ (PhiSet (H := H)).card)))
          (fun _ => ((Real.exp (-(dT (PhiSet (H := H)).card T) / 2) : ℝ) : ℂ) • 1) (ProjectiveLineModels.stdLat K _)
        - F.h ⟨0, hMpos⟩ := by
      funext u
      exact congrArg (fun L => muDef (Pi.basisFun K (Fin ((T - 2) ^ (PhiSet (H := H)).card)))
          (fun _ => ((Real.exp (-(dT (PhiSet (H := H)).card T) / 2) : ℝ) : ℂ) • 1) L - F.h ⟨0, hMpos⟩) (hN' u)
    have hs : Dd.s u0 = muDef (Pi.basisFun K (Fin ((T - 2) ^ (PhiSet (H := H)).card)))
          (fun _ => ((Real.exp (-(dT (PhiSet (H := H)).card T) / 2) : ℝ) : ℂ) • 1) (ProjectiveLineModels.stdLat K _)
        - F.h ⟨0, hMpos⟩ := by
      unfold Data.s
      rw [hfun]
      exact wmean_const _ _ hsum
    have hh : muDef (Pi.basisFun K (Fin ((T - 2) ^ (PhiSet (H := H)).card)))
          (fun _ => ((Real.exp (-(dT (PhiSet (H := H)).card T) / 2) : ℝ) : ℂ) • 1) (ProjectiveLineModels.stdLat K _)
        - muMinDef (Pi.basisFun K (Fin ((T - 2) ^ (PhiSet (H := H)).card))) (fun _ => 1) (ProjectiveLineModels.stdLat K _)
        ≤ F.h ⟨0, hMpos⟩ := le_max_right _ _
    have hmin : muMinDef F.b' F.X' F.cc
        = muMinDef (Pi.basisFun K (Fin ((T - 2) ^ (PhiSet (H := H)).card))) (fun _ => 1) (ProjectiveLineModels.stdLat K _) := rfl
    have hpos : 0 ≤ x ^ cHH * bTx x ε := mul_nonneg (Real.rpow_nonneg hx0.le _) hb.le
    rw [hs, hmin]
    linarith

  have hdM0 : 0 < F.dM ⟨0, hMpos⟩ := lt_of_lt_of_le (hdupos _) (hrk ⟨0, hMpos⟩).2
  have hde : 1 - F.du ⟨0, hMpos⟩ / F.dM ⟨0, hMpos⟩ ≤ 2 * ((PhiSet (H := H)).card : ℝ) / (T : ℝ) :=
    (UnitWeightPartition.deficit_bounds _ (T : ℝ) _ _ hdM0 (by linarith)
      ((hPl.2.2.2.2.2 ⟨0, hMpos⟩).2.2.2.2.2.2.2.2.2.2.1)).2.2.2
  have hdel : F.del = 1 - F.du ⟨0, hMpos⟩ / F.dM ⟨0, hMpos⟩ := rfl
  have hdeF : F.deF = 1 - F.du ⟨0, hMpos⟩ / F.dM ⟨0, hMpos⟩ := by
    have h1 : MatrixLatticeEstimates.RsG F.ι = (Mw : ℝ) * F.du ⟨0, hMpos⟩ := by
      show ∑ _u : Fin Mw, F.du ⟨0, hMpos⟩ = _
      simp
    have h2 : MatrixLatticeEstimates.RsG F.ιf = (Mw : ℝ) * F.dM ⟨0, hMpos⟩ := by
      show ∑ _u : Fin Mw, F.dM ⟨0, hMpos⟩ = _
      simp
    have h3 : (Mw : ℝ) ≠ 0 := by exact_mod_cast hMpos.ne'
    unfold Fam.deF
    rw [h1, h2, mul_div_mul_left _ _ h3]
  have hsmallde : 2 * ((PhiSet (H := H)).card : ℝ) / (T : ℝ) ≤ (x ^ (-cHH) / 3) ^ 2 := by
    have h1 : 18 * ((PhiSet (H := H)).card : ℝ) / (x ^ (-cHH)) ^ 2 ≤ (T : ℝ) := by
      have h2 : (⌈18 * ((PhiSet (H := H)).card : ℝ) / (x ^ (-cHH)) ^ 2⌉₊ : ℝ) ≤ (T : ℝ) := by
        have : ⌈18 * ((PhiSet (H := H)).card : ℝ) / (x ^ (-cHH)) ^ 2⌉₊ ≤ T := by omega
        exact_mod_cast this
      exact le_trans (Nat.le_ceil _) h2
    have hsq : 0 < (x ^ (-cHH)) ^ 2 := by positivity
    rw [div_le_iff₀ hsq] at h1
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hFP : F.del ≤ 1 / 4 ∧ 5 * x ^ (-cHH) + 3 * Real.sqrt F.deF ≤ 6 * x ^ (-cHH) ∧ 2 * F.e0 ≤ 0 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hdel]
      have h1 : 3 / 4 ≤ F.du ⟨0, hMpos⟩ / F.dM ⟨0, hMpos⟩ := by
        rw [le_div_iff₀ hdM0]; exact (hrk ⟨0, hMpos⟩).1
      linarith
    · have h1 : Real.sqrt F.deF ≤ x ^ (-cHH) / 3 := by
        rw [hdeF]
        calc Real.sqrt (1 - F.du ⟨0, hMpos⟩ / F.dM ⟨0, hMpos⟩) ≤ Real.sqrt ((x ^ (-cHH) / 3) ^ 2) :=
              Real.sqrt_le_sqrt (le_trans hde hsmallde)
          _ = x ^ (-cHH) / 3 := Real.sqrt_sq (by positivity)
      linarith
    · show 2 * (0 : ℝ) ≤ 0
      norm_num
  obtain ⟨cDiv, cE, cCount, cSlope, cLoss, p1, p2, p3, p4, p5, hDIV, hE, hHC, hCnt, hSl, hLoss⟩ :=
    constsExist Dd eDiv eLoss cHH (4 + 4 * (1 / ((TT.card : ℝ) * (m : ℝ) * (aTx x ε / k + bpTx x ε)))
        + (∑ u, |F.Rd u|) / XppH H G) hx0 hnT haa hLa hm hB0 hNc hb hL hk
      (fun _ _ => by show (1 : ℝ) ≤ (T : ℝ); linarith) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  exact ⟨Mw, G, ⟨cDiv, eDiv, cE, 0, cCount, cSlope, _, cLoss, eLoss, cHH⟩,
    1 / ((TT.card : ℝ) * (m : ℝ) * (aTx x ε / k + bpTx x ε)), fun _ => F, hMpos, hMw2, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, ⟨p1, p2, le_rfl, p3, p4, by positivity, p5⟩,
    ⟨fun _ => hLat, fun _ => hPl, ⟨by linarith, by linarith, fun _ u => hSz u⟩, hv, fun _ u => hdupos u,
      by show (0 : ℝ) ≤ 1 / 4; norm_num, hDIV, hE, hHC, hCnt, hSl, hHH, fun _ => hFP⟩, hLoss⟩

section DataT
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DataT

section StdSlopes

open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat)

section RankOne

variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

theorem std_deg_eq (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (N : Submodule (𝓞 K) V)
    (h : rk (Formalism.HermitianLatticesTheory.realize b X) N ≠ 0) :
    deg (Formalism.HermitianLatticesTheory.realize b X) N = slope (Formalism.HermitianLatticesTheory.realize b X) N * (rk (Formalism.HermitianLatticesTheory.realize b X) N : ℝ) := by
  have h' : ((rk (Formalism.HermitianLatticesTheory.realize b X) N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h
  show deg (Formalism.HermitianLatticesTheory.realize b X) N
    = deg (Formalism.HermitianLatticesTheory.realize b X) N / (rk (Formalism.HermitianLatticesTheory.realize b X) N : ℝ) * (rk (Formalism.HermitianLatticesTheory.realize b X) N : ℝ)
  field_simp

theorem std_deg_bot_le (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    {L : Submodule (𝓞 K) V} (hL : L.FG) (hL0 : L ≠ ⊥) :
    deg (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) ≤ 0 := by
  have hlat := (place_lattice_structure K V ι b X hX L hL).1
  have h := ((slope_characterization (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) L hlat hL0).1
    (muMax (Formalism.HermitianLatticesTheory.realize b X) L)).1 le_rfl ⊥ bot_le
  rw [hnSum_rk_bot] at h
  simpa using h

theorem std_rank_one (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    {L : Submodule (𝓞 K) V} (hL : L.FG) (hrk : rkK L = 1) :
    muMax (Formalism.HermitianLatticesTheory.realize b X) L = slope (Formalism.HermitianLatticesTheory.realize b X) L ∧
    muMin (Formalism.HermitianLatticesTheory.realize b X) L = slope (Formalism.HermitianLatticesTheory.realize b X) L := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hL0 : L ≠ ⊥ := by
    rintro rfl
    have h0 : rkK (⊥ : Submodule (𝓞 K) V) = 0 := by
      unfold rkK
      rw [Submodule.bot_coe, Submodule.span_zero_singleton, finrank_bot]
    omega
  have hlat := (place_lattice_structure K V ι b X hX L hL).1
  have hrkL := (place_lattice_structure K V ι b X hX L hL).2.1
  obtain ⟨c1, c2, -, c4, c5⟩ := slope_characterization (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) L hlat hL0
  have hbot := std_deg_bot_le b X hX hL hL0
  have hfr : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hr0 : rk (Formalism.HermitianLatticesTheory.realize b X) L ≠ 0 := by
    rw [hrkL, hrk]; omega
  have hdegL := std_deg_eq b X L hr0
  have key : ∀ N : Submodule (𝓞 K) V, N ≤ L → N ≠ ⊥ →
      rk (Formalism.HermitianLatticesTheory.realize b X) N = rk (Formalism.HermitianLatticesTheory.realize b X) L ∧
      deg (Formalism.HermitianLatticesTheory.realize b X) N ≤ deg (Formalism.HermitianLatticesTheory.realize b X) L := by
    intro N hN hN0
    have hNfg : N.FG := Submodule.FG.of_le hL hN
    have hrkN : rkK N = 1 := by
      have h1 : rkK N ≤ rkK L := Submodule.finrank_mono (Submodule.span_mono hN)
      have h2 := slopeLatticeData.rkK_pos (K := K) hN0
      omega
    have hr := (place_lattice_structure K V ι b X hX N hNfg).2.1
    have hrr : rk (Formalism.HermitianLatticesTheory.realize b X) N = rk (Formalism.HermitianLatticesTheory.realize b X) L := by rw [hr, hrkL, hrkN, hrk]
    have hmu := slopeLatticeData.muDef_index b X hX hL hN hN0 (hrkN.trans hrk.symm)
    have hlog : 0 ≤ Real.log (N.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) := Real.log_natCast_nonneg _
    have hq : 0 ≤ 2 * Real.log (N.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) /
        ((Module.finrank ℚ K : ℝ) * (rkK L : ℝ)) := by positivity
    have hsl : slope (Formalism.HermitianLatticesTheory.realize b X) N ≤ slope (Formalism.HermitianLatticesTheory.realize b X) L := by
      unfold muDef at hmu
      linarith
    refine ⟨hrr, ?_⟩
    rw [std_deg_eq b X N (by rw [hrr]; exact hr0), hdegL, hrr]
    exact mul_le_mul_of_nonneg_right hsl (Nat.cast_nonneg _)
  constructor
  · refine le_antisymm ((c1 _).2 fun N hN => ?_) c5
    by_cases hN0 : N = ⊥
    · subst hN0
      rw [hnSum_rk_bot]
      simpa using hbot
    · obtain ⟨k1, k2⟩ := key N hN hN0
      rw [k1, ← hdegL]
      exact k2
  · refine le_antisymm c4 ((c2 _).2 fun N hN => ?_)
    by_cases hN0 : N = ⊥
    · subst hN0
      rw [hnSum_rk_bot, ← sub_nonneg]
      have : deg (Formalism.HermitianLatticesTheory.realize b X) L - deg (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V)
          - slope (Formalism.HermitianLatticesTheory.realize b X) L * ((rk (Formalism.HermitianLatticesTheory.realize b X) L : ℝ) - ((0 : ℕ) : ℝ))
          = - deg (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) := by
        rw [hdegL]; push_cast; ring
      rw [this]
      linarith
    · obtain ⟨k1, k2⟩ := key N hN hN0
      rw [k1, sub_self, mul_zero]
      linarith

end RankOne

variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  (n : Type) [Fintype n] [DecidableEq n]

def standardSpanAlt (s : Finset n) : Submodule (𝓞 K) (n → K) :=
  Submodule.span (𝓞 K) ((Pi.basisFun K n) '' (s : Set n))

variable {K n}

theorem std_T_supp {s : Finset n} {x : n → K} (hx : x ∈ standardSpanAlt K n s) {k : n} (hk : k ∉ s) : x k = 0 := by
  unfold standardSpanAlt at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    have : k ≠ i := by
      rintro rfl
      exact hk hi
    simp [this]
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => simp [hx]

theorem std_real_zero {x : n → K} {k : n} (hk : x k = 0) (v : InfinitePlace K) (e : Fin 2) :
    (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K n) (fun _ => (1 : Matrix n n ℂ)) x) (v, k, e) = 0 := by
  have h : Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K n) (fun _ => (1 : Matrix n n ℂ)) v x k = 0 := by
    simp [Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, hk]
  fin_cases e
  · exact (PlaceOperatorNorms.realize_apply0 _ _ x v k).trans (by rw [h]; rfl)
  · exact (PlaceOperatorNorms.realize_apply1 _ _ x v k).trans (by rw [h]; rfl)

theorem std_orth {s : Finset n} {a : n} (ha : a ∉ s) {x y : n → K} (hx : x ∈ standardSpanAlt K n {a})
    (hy : y ∈ standardSpanAlt K n s) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K n) (fun _ => (1 : Matrix n n ℂ)) x)
      (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K n) (fun _ => (1 : Matrix n n ℂ)) y) = 0 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  obtain ⟨v, k, e⟩ := p
  by_cases hk : k = a
  · subst hk
    rw [std_real_zero (std_T_supp hy ha) v e]
    simp
  · rw [std_real_zero (std_T_supp hx (by simpa using hk)) v e]
    simp

theorem std_T_fg (s : Finset n) : (standardSpanAlt K n s).FG :=
  Submodule.fg_span ((Finset.finite_toSet s).image _)

theorem std_T_cons (a : n) (s : Finset n) (ha : a ∉ s) :
    standardSpanAlt K n (Finset.cons a s ha) = standardSpanAlt K n {a} ⊔ standardSpanAlt K n s := by
  unfold standardSpanAlt
  rw [Finset.coe_cons, Set.image_insert_eq, Submodule.span_insert, Finset.coe_singleton, Set.image_singleton]

theorem std_T_ne {s : Finset n} (hs : s.Nonempty) : standardSpanAlt K n s ≠ ⊥ := by
  obtain ⟨i, hi⟩ := hs
  intro h0
  have h1 : Pi.basisFun K n i ∈ standardSpanAlt K n s := Submodule.subset_span ⟨i, hi, rfl⟩
  rw [h0, Submodule.mem_bot] at h1
  exact (Pi.basisFun K n).ne_zero i h1

theorem std_T_single (a : n) :
    rkK (standardSpanAlt K n {a}) = 1 ∧ muDef (Pi.basisFun K n) (fun _ => 1) (standardSpanAlt K n {a}) = 0 := by
  have hX : ∀ v : InfinitePlace K, IsUnit ((1 : Matrix n n ℂ)).det := by simp
  have hr : Set.range (fun _ : Fin 1 => Pi.basisFun K n a) = (Pi.basisFun K n) '' ((({a} : Finset n)) : Set n) := by
    simp
  have hli : LinearIndependent K (fun _ : Fin 1 => Pi.basisFun K n a) :=
    LinearIndependent.of_subsingleton 0 ((Pi.basisFun K n).ne_zero a)
  have h := (height_gram_determinant K (n → K) n (Pi.basisFun K n) (fun _ => 1) hX 1
    (fun _ => Pi.basisFun K n a) hli).1
  rw [hr] at h
  have hg : ∀ v : InfinitePlace K, gramPl (Pi.basisFun K n) (fun _ => 1) v (fun _ : Fin 1 => Pi.basisFun K n a) = 1 := by
    intro v
    ext i j
    simp [gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, Matrix.one_apply, Pi.single_apply,
      Subsingleton.elim i j]
  have hrk : rkK (standardSpanAlt K n {a}) = 1 := by
    unfold rkK standardSpanAlt
    rw [Submodule.span_span_of_tower, Finset.coe_singleton, Set.image_singleton]
    exact finrank_span_singleton ((Pi.basisFun K n).ne_zero a)
  refine ⟨hrk, ?_⟩
  rw [slopeLatticeData.muDef_eq_log _ _ hX (std_T_fg {a}) (std_T_ne (Finset.singleton_nonempty a))]
  have h1 : ht (Pi.basisFun K n) (fun _ => 1) (standardSpanAlt K n {a}) = 1 := by
    unfold standardSpanAlt
    rw [h]
    simp only [hg, Matrix.det_one, Complex.one_re, Finset.prod_const_one]
  rw [h1]
  simp

theorem std_T_slopes (s : Finset n) (hs : s.Nonempty) :
    muMaxDef (Pi.basisFun K n) (fun _ => 1) (standardSpanAlt K n s) = 0 ∧
    muMinDef (Pi.basisFun K n) (fun _ => 1) (standardSpanAlt K n s) = 0 := by
  have hX : ∀ v : InfinitePlace K, IsUnit ((1 : Matrix n n ℂ)).det := by simp
  have hone : ∀ a : n, muMaxDef (Pi.basisFun K n) (fun _ => 1) (standardSpanAlt K n {a}) = 0 ∧
      muMinDef (Pi.basisFun K n) (fun _ => 1) (standardSpanAlt K n {a}) = 0 := by
    intro a
    obtain ⟨h1, h2⟩ := std_T_single (K := K) a
    obtain ⟨h3, h4⟩ := std_rank_one (Pi.basisFun K n) (fun _ => 1) hX (std_T_fg {a}) h1
    unfold muDef at h2
    unfold muMaxDef muMinDef
    rw [h3, h4]
    exact ⟨h2, h2⟩
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact hone a
  | cons a s ha hs ih =>
    have hA := (place_lattice_structure K (n → K) n (Pi.basisFun K n) (fun _ => 1) hX _ (std_T_fg (K := K) {a})).1
    have hB := (place_lattice_structure K (n → K) n (Pi.basisFun K n) (fun _ => 1) hX _ (std_T_fg (K := K) s)).1
    obtain ⟨m1, m2⟩ := ((polygon_slope_sum.{0, 0, 0, 0} (𝓞 K) (n → K) _
      (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K n) (fun _ => (1 : Matrix n n ℂ)))).2 _ _ hA hB
      (fun x hx y hy => std_orth ha hx hy)).2.2 (std_T_ne (Finset.singleton_nonempty a)) (std_T_ne hs)
    obtain ⟨o1, o2⟩ := hone a
    obtain ⟨i1, i2⟩ := ih
    rw [std_T_cons]
    unfold muMaxDef at o1 i1 ⊢
    unfold muMinDef at o2 i2 ⊢
    rw [m1, m2]
    constructor
    · rcases max_choice (muMax (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K n) (fun _ => (1 : Matrix n n ℂ))) (standardSpanAlt K n {a}))
        (muMax (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K n) (fun _ => (1 : Matrix n n ℂ))) (standardSpanAlt K n s)) with h | h
      · rw [h]; exact o1
      · rw [h]; exact i1
    · rcases min_choice (muMin (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K n) (fun _ => (1 : Matrix n n ℂ))) (standardSpanAlt K n {a}))
        (muMin (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K n) (fun _ => (1 : Matrix n n ℂ))) (standardSpanAlt K n s)) with h | h
      · rw [h]; exact o2
      · rw [h]; exact i2

variable (K n)

theorem standard_lattice_semistable [Nonempty n] :
    muDef (Pi.basisFun K n) (fun _ => 1) (stdLat K n) = 0 ∧
    muMaxDef (Pi.basisFun K n) (fun _ => 1) (stdLat K n) = 0 ∧
    muMinDef (Pi.basisFun K n) (fun _ => 1) (stdLat K n) = 0 := by
  have h : stdLat K n = standardSpanAlt K n Finset.univ := by
    unfold stdLat standardSpanAlt
    rw [Finset.coe_univ, Set.image_univ]
  refine ⟨mu_std K n, ?_⟩
  rw [h]
  exact std_T_slopes Finset.univ Finset.univ_nonempty

end StdSlopes

open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat inclMat)

section Coll
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

def bump (m : ℕ) (c : ℝ) (w : slopeLatticeData.FinPl K) : ℝ :=
  if prBelow w = 2 then c / (2 * (m : ℝ) * Real.log 2) else 0

def collFam (v : InfinitePlace K) (m f T Mw : ℕ) (hb gG gE : ℝ) : Fam (Fin Mw) m where
  K := K
  Wd := Fin ((T - 2) ^ f) → K
  κ := Fin ((T - 2) ^ f)
  κ₁ := Fin ((T - 1) ^ f - (T - 2) ^ f)
  V := fun _ => Fin ((T - 2) ^ f) → K
  ι := fun _ => Fin ((T - 2) ^ f)
  Vf := fun _ => Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f) → K
  ιf := fun _ => Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f)
  b' := Pi.basisFun K _
  X' := fun _ => 1
  cc := stdLat K _
  b := fun _ => Pi.basisFun K _
  X := fun _ _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1
  M := fun _ => stdLat K _
  N0 := fun _ => Formalism.HermitianLatticesTheory.idealSmul
    ((slopeLatticeData.idealPow (tau0 K 2 0) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (stdLat K _)
  bf := fun _ => Pi.basisFun K _
  Xf := fun _ _ => 1
  Mf := fun _ => stdLat K _
  σ := fun _ => tau0 K 2 0
  τ := tau0 K 2 0
  B := fun _ => LinearMap.id
  v := v
  Y := fun _ => 1
  Y' := 1
  Ball := fun _ => inclMat _ _
  γ := fun _ => 1
  Bf := fun _ => 1
  Vr := fun _ => inclMat _ _
  S := plOver K 2 ∪ plOver K T
  gain := fun _ w => bump K m gG w
  Fj := fun _ w => bump K m (gE - gG) w
  Ej := fun _ _ w => bump K m gE w
  iop := fun _ => 0
  T := fun _ => T
  h := fun _ => max (htMap (Pi.basisFun K (Fin ((T - 2) ^ f)))
    (fun _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1) (Pi.basisFun K (Fin ((T - 2) ^ f))) (fun _ => 1)
    LinearMap.id) hb
  lam := fun _ => 0
  Dstar := ((T - 1) ^ f : ℕ)
  η0 := 0
  η1 := 0
  e0 := 0

variable (v : InfinitePlace K) (m f T Mw : ℕ) (hb gG gE : ℝ)

theorem coll_lat (sg : ℝ) (hT : 4 ≤ T) (hsg : 0 < sg) (hsg20 : sg ≤ 1 / 20) (hMw : 1 / sg ≤ (Mw : ℝ)) :
    (collFam K v m f T Mw hb gG gE).LatHyp sg :=
  model_lat K v m f T 2 0 Mw hb sg hT hsg hsg20 hMw

theorem twist_vector_at_zero (w : slopeLatticeData.FinPl K) : tau0 K 2 0 w = 0 := by
  rw [twist_vector_apply]; split_ifs <;> simp

theorem bump_cancel (w : slopeLatticeData.FinPl K) : bump K m gG w + bump K m (gE - gG) w - bump K m gE w = 0 := by
  unfold bump
  split_ifs
  · ring
  · ring

theorem sum_bump (hm : 1 ≤ m) (c : ℝ) (S : Finset (slopeLatticeData.FinPl K)) (hS : ∀ w : slopeLatticeData.FinPl K, prBelow w = 2 → w ∈ S) :
    2 * ∑ w ∈ S, lE w * bump K m c w = c / (m : ℝ) := by
  have hu := sum_log_norm_over_prime S 2 Nat.prime_two hS
  have h1 : ∑ w ∈ S, lE w * bump K m c w = c / (2 * (m : ℝ) * Real.log 2) * ∑ w ∈ S.filter (fun w => prBelow w = 2), lE w := by
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold bump
    split_ifs <;> ring
  rw [h1, hu]
  have hl : Real.log ((2 : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < Real.log ((2 : ℕ) : ℝ) := Real.log_pos (by norm_num)
    exact this.ne'
  have hm' : (m : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  push_cast at hl ⊢
  field_simp

theorem coll_place (bb : ℝ) (hm : 1 ≤ m) (hf : 1 ≤ f) (hTp : T.Prime) (hne : 2 ≠ T)
    (hT4 : 4 * f ≤ T) (hsmall : 4 * (f : ℝ) / (T : ℝ) * bb ^ 2 + dT f T ≤ 1) :
    (collFam K v m f T Mw hb gG gE).PlaceHyp f bb := by
  have hP := model_place K v m f T 2 0 Mw hb bb hm hf hTp Nat.prime_two hne hT4 hsmall
    (by push_cast; nlinarith [sq_nonneg bb])
  obtain ⟨a1, a2, -, a4, a5, a6⟩ := hP
  have hlen : ∀ u (w : slopeLatticeData.FinPl K), (collFam K v m f T Mw hb gG gE).lenN u w = 0 := fun u w =>
    lenSelf0 w (Formalism.HermitianLatticesTheory.idealSmul ((slopeLatticeData.idealPow (tau0 K 2 0) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (stdLat K (Fin ((T - 2) ^ f))))
  have hlenR : ∀ u (w : slopeLatticeData.FinPl K), (collFam K v m f T Mw hb gG gE).lenR u w = 0 := by
    intro u w
    unfold Fam.lenR
    rw [hlen]
    show (((0 : ℕ) : ℝ) + _ * ((tau0 K 2 0 w : ℤ) : ℝ)) / ramE w = 0
    rw [twist_vector_at_zero]
    simp
  have htR : ∀ w : slopeLatticeData.FinPl K, (collFam K v m f T Mw hb gG gE).tauR w = 0 := by
    intro w
    show ((tau0 K 2 0 w : ℤ) : ℝ) / ramE w = 0
    rw [twist_vector_at_zero]; simp
  refine ⟨a1, a2, fun _ _ => le_rfl, a4, a5, fun u => ?_⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, -, -, -, -, b16, b17, b18⟩ := a6 u
  refine ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, ?_, ?_, le_rfl, ?_, b16, b17, b18⟩
  · intro w _
    have h1 : (collFam K v m f T Mw hb gG gE).lenR u w = 0 := hlenR u w
    have h2 : (collFam K v m f T Mw hb gG gE).tauR w = 0 := htR w
    have h3 : (collFam K v m f T Mw hb gG gE).iop (prBelow w) = 0 := rfl
    rw [h1, h2, h3]; simp
  · intro w _
    have h1 : (collFam K v m f T Mw hb gG gE).lenR u w = 0 := hlenR u w
    have h3 : (collFam K v m f T Mw hb gG gE).lam u = 0 := rfl
    rw [h1, h3]; simp
  · intro (w : slopeLatticeData.FinPl K) _
    show ((tau0 K 2 0 w : ℤ) : ℝ) / ramE w ≤ ∑ j : Fin m, (bump K m gG w + bump K m (gE - gG) w - bump K m gE w)
    rw [twist_vector_at_zero]
    simp [bump_cancel]

theorem mem_second_closed (w : slopeLatticeData.FinPl K) (hw : prBelow w = 2) : w ∈ plOver K 2 ∪ plOver K T :=
  Finset.mem_union_left _ ((mem_plOver Nat.prime_two w).2 hw)

theorem coll_Ga (hm : 1 ≤ m) : (collFam K v m f T Mw hb gG gE).Ga = gG := by
  have hm' : (m : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  show 2 * ∑ w ∈ plOver K 2 ∪ plOver K T, lE w * ((∑ _j : Fin m, bump K m gG w) - ((tau0 K 2 0 w : ℤ) : ℝ) / ramE w) = gG
  have h1 : ∀ w ∈ plOver K 2 ∪ plOver K T, lE w * ((∑ _j : Fin m, bump K m gG w) - ((tau0 K 2 0 w : ℤ) : ℝ) / ramE w)
      = (m : ℝ) * (lE w * bump K m gG w) := by
    intro w _
    rw [twist_vector_at_zero]
    simp
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have := sum_bump K m hm gG _ (mem_second_closed K T)
  calc 2 * ((m : ℝ) * ∑ w ∈ plOver K 2 ∪ plOver K T, lE w * bump K m gG w)
      = (m : ℝ) * (2 * ∑ w ∈ plOver K 2 ∪ plOver K T, lE w * bump K m gG w) := by ring
    _ = gG := by rw [this]; field_simp

theorem coll_Fo (hm : 1 ≤ m) : (collFam K v m f T Mw hb gG gE).Fo = gE - gG := by
  have hm' : (m : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  show 2 * ∑ _j : Fin m, ∑ w ∈ plOver K 2 ∪ plOver K T, lE w * bump K m (gE - gG) w = gE - gG
  have := sum_bump K m hm (gE - gG) _ (mem_second_closed K T)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc 2 * ((m : ℝ) * ∑ w ∈ plOver K 2 ∪ plOver K T, lE w * bump K m (gE - gG) w)
      = (m : ℝ) * (2 * ∑ w ∈ plOver K 2 ∪ plOver K T, lE w * bump K m (gE - gG) w) := by ring
    _ = gE - gG := by rw [this]; field_simp

theorem coll_EeJ (hm : 1 ≤ m) (u : Fin Mw) (j : Fin m) : (collFam K v m f T Mw hb gG gE).EeJ u j = gE / (m : ℝ) :=
  sum_bump K m hm gE _ (mem_second_closed K T)

theorem coll_IO : (collFam K v m f T Mw hb gG gE).IO = 0 := by
  show ∑ p ∈ (collFam K v m f T Mw hb gG gE).Pr, Real.log (p : ℝ) * (0 : ℝ) = 0
  simp

theorem coll_Rd (u : Fin Mw) : (collFam K v m f T Mw hb gG gE).Rd u = 0 := by
  show ∑ w ∈ plOver K 2 ∪ plOver K T, 2 * lE w * ((∑ j : Fin m, (bump K m gG w + bump K m (gE - gG) w - bump K m gE w))
    - ((tau0 K 2 0 w : ℤ) : ℝ) / ramE w) = 0
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [twist_vector_at_zero]
  simp [bump_cancel]

theorem ht_scaled_id (n : Type) [Fintype n] [DecidableEq n] (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 1) :
    htMap (Pi.basisFun K n) (fun _ => ((c : ℝ) : ℂ) • (1 : Matrix n n ℂ)) (Pi.basisFun K n) (fun _ => 1)
      LinearMap.id ≤ 0 := by
  unfold htMap
  refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos fun v _ => ?_)
  refine Real.log_nonpos (sq_nonneg _) ?_
  unfold opNormAt
  rw [LinearMap.toMatrix_id, Matrix.map_one _ (map_zero _) (map_one _)]
  simp only [inv_one, Matrix.one_mul]
  refine pow_le_one₀ (norm_nonneg _) ?_
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  have : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (((c : ℝ) : ℂ) • (1 : Matrix n n ℂ)))) x
      = ((c : ℝ) : ℂ) • x := by
    ext i
    simp [Matrix.toLpLin_apply, Matrix.smul_mulVec]
  rw [this, norm_smul, one_mul]
  have h1 : ‖((c : ℝ) : ℂ)‖ = c := by simp [abs_of_nonneg hc0]
  rw [h1]
  exact mul_le_of_le_one_left (norm_nonneg _) hc

def hbT (f T : ℕ) : ℝ :=
  muDef (Pi.basisFun K (Fin ((T - 2) ^ f))) (fun _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1) (stdLat K _)
    - muMinDef (Pi.basisFun K (Fin ((T - 2) ^ f))) (fun _ => 1) (stdLat K _)

theorem dT_nonneg (hT : 4 ≤ T) : 0 ≤ dT f T := by
  have hTr : (4 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  unfold dT
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))) (by linarith)

theorem coll_h_le (hT : 4 ≤ T) (hs : ℝ) (hs0 : 0 ≤ hs)
    (hmin : -hs ≤ muMinDef (Pi.basisFun K (Fin ((T - 2) ^ f))) (fun _ => 1) (stdLat K _)) (u : Fin Mw) :
    (collFam K v m f T Mw (hbT K f T) gG gE).h u ≤ hs := by
  have hdT := dT_nonneg f T hT
  obtain ⟨ha, -, -⟩ := model_card f T hT
  have : Nonempty (Fin ((T - 2) ^ f)) := ⟨⟨0, ha⟩⟩
  have hsc := (scaled_std K (Fin ((T - 2) ^ f)) (Real.exp (-(dT f T) / 2)) (Real.exp_pos _)).1
  rw [Real.log_exp] at hsc
  refine max_le (le_trans (ht_scaled_id K _ _ (Real.exp_pos _).le (Real.exp_le_one_iff.2 (by linarith))) hs0) ?_
  unfold hbT
  rw [hsc]
  linarith

theorem coll_du (hT : 4 ≤ T) (u : Fin Mw) : 0 < (collFam K v m f T Mw hb gG gE).du u := by
  obtain ⟨ha, -, -⟩ := model_card f T hT
  show (0 : ℝ) < ((Fintype.card (Fin ((T - 2) ^ f)) : ℕ) : ℝ)
  rw [Fintype.card_fin]
  exact_mod_cast ha

theorem collection_family_slope_gap (hT : 4 ≤ T) (hMpos : 0 < Mw) :
    wmean (collFam K v m f T Mw (hbT K f T) gG gE).du
      (fun u => muDef ((collFam K v m f T Mw (hbT K f T) gG gE).b u) ((collFam K v m f T Mw (hbT K f T) gG gE).X u)
        ((collFam K v m f T Mw (hbT K f T) gG gE).N' u) - (collFam K v m f T Mw (hbT K f T) gG gE).h u)
      - muMinDef (collFam K v m f T Mw (hbT K f T) gG gE).b' (collFam K v m f T Mw (hbT K f T) gG gE).X'
          (collFam K v m f T Mw (hbT K f T) gG gE).cc ≤ 0 := by
  set F := collFam K v m f T Mw (hbT K f T) gG gE with hF
  have hN' : ∀ u, F.N' u = stdLat K (Fin ((T - 2) ^ f)) :=
    fun u => modLat_cancel K (tau0 K 2 0) (stdLat K (Fin ((T - 2) ^ f)))
  have hsum : ∑ u : Fin Mw, F.du u ≠ 0 := by
    have : 0 < ∑ u : Fin Mw, F.du u :=
      Finset.sum_pos (fun u _ => coll_du K v m f T Mw _ gG gE hT u) ⟨⟨0, hMpos⟩, Finset.mem_univ _⟩
    exact this.ne'
  have hfun : (fun u : Fin Mw => muDef (F.b u) (F.X u) (F.N' u) - F.h u) = fun _ =>
      muDef (Pi.basisFun K (Fin ((T - 2) ^ f)))
        (fun _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1) (stdLat K _) - F.h ⟨0, hMpos⟩ := by
    funext u
    exact congrArg (fun L => muDef (Pi.basisFun K (Fin ((T - 2) ^ f)))
        (fun _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1) L - F.h ⟨0, hMpos⟩) (hN' u)
  rw [hfun, wmean_const _ _ hsum]
  have hh : hbT K f T ≤ F.h ⟨0, hMpos⟩ := le_max_right _ _
  have hmin : muMinDef F.b' F.X' F.cc
      = muMinDef (Pi.basisFun K (Fin ((T - 2) ^ f))) (fun _ => 1) (stdLat K _) := rfl
  rw [hmin]
  unfold hbT at hh
  linarith

theorem coll_tr (bb sg : ℝ) (hm : 1 ≤ m) (hf : 1 ≤ f) (hTp : T.Prime) (hT4 : 4 * f ≤ T) (hbb : 2 ≤ bb ^ 2)
    (hsmall : 4 * (f : ℝ) / (T : ℝ) * bb ^ 2 + dT f T ≤ 1) (hMpos : 0 < Mw) (hsg : 0 < sg)
    (h18 : 18 * (f : ℝ) / sg ^ 2 ≤ (T : ℝ)) :
    (collFam K v m f T Mw hb gG gE).del ≤ 1 / 4 ∧
      5 * sg + 3 * Real.sqrt (collFam K v m f T Mw hb gG gE).deF ≤ 6 * sg ∧
      2 * (collFam K v m f T Mw hb gG gE).e0 ≤ 0 := by
  have hT : 4 ≤ T := by omega
  have hTr : (4 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  set F := collFam K v m f T Mw hb gG gE with hF
  have hPl : F.PlaceHyp f bb := coll_place K v m f T Mw hb gG gE bb hm hf hTp (by omega) hT4 hsmall
  have hdupos : ∀ u, 0 < F.du u := coll_du K v m f T Mw hb gG gE hT
  have hrk := ranks_of_places (Fin Mw) F _ _ hf hbb hdupos hPl
  have hdM0 : 0 < F.dM ⟨0, hMpos⟩ := lt_of_lt_of_le (hdupos _) (hrk ⟨0, hMpos⟩).2
  have hde : 1 - F.du ⟨0, hMpos⟩ / F.dM ⟨0, hMpos⟩ ≤ 2 * (f : ℝ) / (T : ℝ) :=
    (UnitWeightPartition.deficit_bounds _ (T : ℝ) _ _ hdM0 (by linarith)
      ((hPl.2.2.2.2.2 ⟨0, hMpos⟩).2.2.2.2.2.2.2.2.2.2.1)).2.2.2
  have hdel : F.del = 1 - F.du ⟨0, hMpos⟩ / F.dM ⟨0, hMpos⟩ := rfl
  have hdeF : F.deF = 1 - F.du ⟨0, hMpos⟩ / F.dM ⟨0, hMpos⟩ := by
    have h1 : MatrixLatticeEstimates.RsG F.ι = (Mw : ℝ) * F.du ⟨0, hMpos⟩ := by
      show ∑ _u : Fin Mw, F.du ⟨0, hMpos⟩ = _
      simp
    have h2 : MatrixLatticeEstimates.RsG F.ιf = (Mw : ℝ) * F.dM ⟨0, hMpos⟩ := by
      show ∑ _u : Fin Mw, F.dM ⟨0, hMpos⟩ = _
      simp
    have h3 : (Mw : ℝ) ≠ 0 := by exact_mod_cast hMpos.ne'
    unfold Fam.deF
    rw [h1, h2, mul_div_mul_left _ _ h3]
  have hsmallde : 2 * (f : ℝ) / (T : ℝ) ≤ (sg / 3) ^ 2 := by
    have hsq : 0 < sg ^ 2 := by positivity
    rw [div_le_iff₀ hsq] at h18
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hdel]
    have h1 : 3 / 4 ≤ F.du ⟨0, hMpos⟩ / F.dM ⟨0, hMpos⟩ := by
      rw [le_div_iff₀ hdM0]; exact (hrk ⟨0, hMpos⟩).1
    linarith
  · have h1 : Real.sqrt F.deF ≤ sg / 3 := by
      rw [hdeF]
      calc Real.sqrt (1 - F.du ⟨0, hMpos⟩ / F.dM ⟨0, hMpos⟩) ≤ Real.sqrt ((sg / 3) ^ 2) :=
            Real.sqrt_le_sqrt (le_trans hde hsmallde)
        _ = sg / 3 := Real.sqrt_sq (by positivity)
    linarith
  · show 2 * (0 : ℝ) ≤ 0
    norm_num

end Coll

theorem latticeCollapse (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v0 : InfinitePlace K)
    (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ)
    (TT T2 : Finset H) (m : ℕ) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (G : Glob) (C : Consts) (cT hs : ℝ)
    (T : H → ℕ)
    (hx : 1 ≤ G.x) (hε : 0 < G.ε) (hk : 1 ≤ G.k) (hLa : 0 ≤ G.La) (hv : 0 < G.v) (hm : 1 ≤ m)
    (hsg20 : G.x ^ (-C.cHH) ≤ 1 / 20)
    (hC : 4 ≤ C.cSl1 ∧ 4 * cT ≤ C.cSl1 ∧ 0 ≤ cT ∧ 0 ≤ C.cE ∧ 0 ≤ C.cH ∧ 0 ≤ C.cCount ∧ 0 ≤ C.cSlope ∧ 0 ≤ C.cLoss)
    (hbar : 1 / 4 ≤ G.delBar ∧ 6 * G.x ^ (-C.cHH) ≤ G.etaBar ∧ 0 ≤ G.eBar ∧ G.eBar ≤ 1 / 4)
    (hTp : ∀ u0, (T u0).Prime) (hT4 : ∀ u0, 4 * (PhiSet (H := H)).card ≤ T u0)
    (hT18 : ∀ u0, 18 * ((PhiSet (H := H)).card : ℝ) / (G.x ^ (-C.cHH)) ^ 2 ≤ (T u0 : ℝ))
    (hsmall : ∀ u0, 4 * ((PhiSet (H := H)).card : ℝ) / (T u0 : ℝ) * bTx G.x G.ε ^ 2
      + dT (PhiSet (H := H)).card (T u0) ≤ 1)
    (hCl : ∀ u0, (∑ j : Fin m, (1 / ((PhiSet (H := H)).card : ℝ)) * ∑ ρ : Fin (PhiSet (H := H)).card,
        Real.log (w u0 j (ePhi ρ) * G.v / Real.pi)) + (m : ℝ) * G.lg
        - C.cCount * (G.La + (m : ℝ) ^ 2 * G.La / G.k) ≤ Real.log (T u0 : ℝ))
    (hCu : ∀ u0, Real.log (T u0 : ℝ) ≤ C.cCount * (m : ℝ) * Real.log (bTx G.x G.ε))
    (hs0 : 0 ≤ hs)
    (hmin : ∀ u0, -hs ≤ muMinDef (Pi.basisFun K (Fin ((T u0 - 2) ^ (PhiSet (H := H)).card))) (fun _ => 1)
      (ProjectiveLineModels.stdLat K _))
    (hmax : ∀ u0, muMaxDef (Pi.basisFun K (Fin ((T u0 - 2) ^ (PhiSet (H := H)).card)
        ⊕ Fin ((T u0 - 1) ^ (PhiSet (H := H)).card - (T u0 - 2) ^ (PhiSet (H := H)).card))) (fun _ => 1)
      (ProjectiveLineModels.stdLat K _) ≤ C.cSlope * (Fintype.card TT : ℝ) * aTx G.x G.ε * G.La)
    (hTop : ∀ u0, hs + ∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j) ≤
      (∑ t : TT, ((m : ℝ) * (ph (a t) - a t * (Real.eulerMascheroniConstant + Real.log (Real.pi / G.v) - (ell chC).re))
          - a t * Real.log (T u0 : ℝ)))
        + (m : ℝ) * (∑ t : TT, a t) * G.lg
        + C.cDiv * (Fintype.card TT : ℝ) * aTx G.x G.ε * G.La
        + C.cDiv * (m : ℝ) * ((2 * (Fintype.card H : ℝ)) * m * bTx G.x G.ε * G.x ^ G.ε
            + (T2.card : ℝ) * G.k * bTx G.x G.ε * G.x ^ G.ε
              / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * G.x ^ (-G.ε))))
          * G.x ^ (C.eDiv * G.ε)) :
    ∃ (Mw : ℕ) (Fm : H → Fam (Fin Mw) m), 0 < Mw ∧ (Mw : ℝ) < G.x ^ C.cHH + 1 ∧ (∀ u0 u, (Fm u0).T u = T u0) ∧
      InputsL D ell G C cT N TT T2 a w Fm ∧ LossBounds (mkData G C.cHH D ell N TT T2 a w Fm) C := by
  obtain ⟨hc1, hc2, hcT, hcE, hcH, hcC, hcS, hcL⟩ := hC
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hbar
  have hx0 : 0 < G.x := by linarith
  have hk0 : 0 < G.k := by linarith
  have hsg : 0 < G.x ^ (-C.cHH) := Real.rpow_pos_of_pos hx0 _
  have hf : 1 ≤ (PhiSet (H := H)).card := phi_card_pos
  have hb : 0 < bTx G.x G.ε := Real.exp_pos _
  have hb2' : 2 ≤ bTx G.x G.ε := by
    have h1 : 1 ≤ G.x ^ G.ε := Real.one_le_rpow hx hε.le
    have := Real.add_one_le_exp (G.x ^ G.ε)
    unfold bTx
    linarith
  have hT : ∀ u0, 4 ≤ T u0 := fun u0 => by have := hT4 u0; omega
  have hMw : 1 / G.x ^ (-C.cHH) ≤ ((⌈1 / G.x ^ (-C.cHH)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hMw2 : ((⌈1 / G.x ^ (-C.cHH)⌉₊ : ℕ) : ℝ) < G.x ^ C.cHH + 1 := by
    have h1 : 1 / G.x ^ (-C.cHH) = G.x ^ C.cHH := by
      rw [Real.rpow_neg hx0.le, one_div, inv_inv]
    rw [h1]
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le _)
  have hMpos : 0 < ⌈1 / G.x ^ (-C.cHH)⌉₊ := Nat.ceil_pos.2 (by positivity)
  obtain ⟨Mw, hMwdef⟩ : ∃ n : ℕ, n = ⌈1 / G.x ^ (-C.cHH)⌉₊ := ⟨_, rfl⟩
  rw [← hMwdef] at hMw hMw2 hMpos
  obtain ⟨gE, hgE⟩ : ∃ g : ℝ, g = (m : ℝ) * (∑ t : TT, a t) * G.lg := ⟨_, rfl⟩
  obtain ⟨gG, hgG⟩ : ∃ g : H → ℝ, ∀ u0, g u0 = ∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j) :=
    ⟨_, fun _ => rfl⟩
  set Fm : H → Fam (Fin Mw) m := fun u0 =>
    collFam K v0 m (PhiSet (H := H)).card (T u0) Mw (hbT K (PhiSet (H := H)).card (T u0)) (gG u0) gE with hFm
  set Dd := mkData (W := fun _ : H => Fin Mw) G C.cHH D ell N TT T2 a w Fm with hDd
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hnT : (0 : ℝ) ≤ Dd.nT := Nat.cast_nonneg _
  have hnH : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have haa : (0 : ℝ) < Dd.a := mul_pos hx0 hb
  have hxe : 0 < G.x ^ G.ε := Real.rpow_pos_of_pos hx0 _
  have hB0 : 0 < Dd.B0 := by
    show 0 < (2 * (Fintype.card H : ℝ)) * m * bTx G.x G.ε * G.x ^ G.ε
    positivity
  have hbp : 0 < bpTx G.x G.ε := div_pos (mul_pos hx0 hb) (Real.exp_pos _)
  have hXpp : 0 < XppH H G := by
    show 0 < aTx G.x G.ε / (bpTx G.x G.ε / (G.x * (Fintype.card H : ℝ)))
    have h2 : 0 < aTx G.x G.ε := mul_pos hx0 hb
    positivity
  have hne : ∀ u0, Nonempty (Fin ((T u0 - 2) ^ (PhiSet (H := H)).card)) := fun u0 =>
    ⟨⟨0, (model_card _ (T u0) (hT u0)).1⟩⟩
  have hLoP : 0 ≤ Dd.LoP C := by
    show 0 ≤ C.cLoss * Dd.nT * (m : ℝ) * bTx G.x G.ε * G.x ^ (C.eLoss * G.ε)
    have := Real.rpow_pos_of_pos hx0 (C.eLoss * G.ε)
    positivity
  refine ⟨Mw, Fm, hMpos, hMw2, fun _ _ => rfl, ⟨fun u0 => coll_lat K v0 m _ (T u0) Mw _ _ _ _ (hT u0) hsg hsg20 hMw,
    fun u0 => coll_place K v0 m _ (T u0) Mw _ _ _ _ hm hf (hTp u0) (by have := hT u0; omega) (hT4 u0) (hsmall u0),
    ⟨hc1, hc2, fun u0 u => ⟨?_, ?_⟩⟩, hv, fun u0 u => coll_du K v0 m _ (T u0) Mw _ _ _ (hT u0) u, hb4,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show (0 : ℝ) ≤ cT * (TT.card : ℝ) * (m : ℝ) * (aTx G.x G.ε / G.k + bpTx G.x G.ε)
    have h2 : 0 < aTx G.x G.ε := mul_pos hx0 hb
    positivity
  · have : (Fm u0).Rd u = 0 := coll_Rd K v0 m _ (T u0) Mw _ _ _ u
    rw [this]
    exact mul_nonneg (by linarith) hXpp.le
  ·
    intro u0 u
    have := hne u0
    have e1 : Dd.muCC u0 = 0 := mu_std K (Fin ((T u0 - 2) ^ (PhiSet (H := H)).card))
    have e2 : Dd.h u0 u ≤ hs := coll_h_le K v0 m _ (T u0) Mw (gG u0) gE (hT u0) hs hs0 (hmin u0) u
    have e3 : Dd.Fo u0 = gE - gG u0 := coll_Fo K v0 m _ (T u0) Mw _ _ _ hm
    have ht := hTop u0
    rw [← hgG u0, ← hgE] at ht
    rw [e1, e3]
    show 0 + Dd.h u0 u - (gE - gG u0) ≤
      (∑ t : TT, ((m : ℝ) * (ph (a t) - a t * (Real.eulerMascheroniConstant + Real.log (Real.pi / G.v) - (ell chC).re))
          - a t * Real.log (T u0 : ℝ)))
        + C.cDiv * (Fintype.card TT : ℝ) * aTx G.x G.ε * G.La
        + C.cDiv * (m : ℝ) * ((2 * (Fintype.card H : ℝ)) * m * bTx G.x G.ε * G.x ^ G.ε
            + (T2.card : ℝ) * G.k * bTx G.x G.ε * G.x ^ G.ε
              / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * G.x ^ (-G.ε))))
          * G.x ^ (C.eDiv * G.ε)
    linarith
  ·
    intro u0 u
    have e1 : Dd.Ee u0 u = gE := by
      show ∑ j : Fin m, (Fm u0).EeJ u j = gE
      rw [Finset.sum_congr rfl (fun j _ => coll_EeJ K v0 m _ (T u0) Mw _ _ _ hm u j)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have e2 : (m : ℝ) * Dd.sumA * Dd.lg = gE := hgE.symm
    rw [e1, e2, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg hcE (by linarith)) hB0.le
  ·
    intro u0 u u'
    have hh : Dd.h u0 u = Dd.h u0 u' := rfl
    have hTw : Dd.T u0 u = Dd.T u0 u' := rfl
    rw [hh, hTw, sub_self, abs_zero]
    exact mul_nonneg hcH (add_nonneg (mul_nonneg (mul_nonneg hnT haa.le) hLa) (mul_nonneg (by linarith) hB0.le))
  ·
    intro u0 u
    refine ⟨hCl u0, hCu u0, fun u' => ?_⟩
    have hTw : Dd.T u0 u = Dd.T u0 u' := rfl
    rw [hTw, sub_self, abs_zero]
    exact mul_nonneg hcC (Real.log_nonneg hk)
  ·
    intro u0 u
    have := hne u0
    have e1 : Dd.muM u0 u = 0 := mu_std K (Fin ((T u0 - 2) ^ (PhiSet (H := H)).card)
        ⊕ Fin ((T u0 - 1) ^ (PhiSet (H := H)).card - (T u0 - 2) ^ (PhiSet (H := H)).card))
    refine ⟨?_, hmax u0⟩
    rw [e1, neg_nonpos]
    have h1 : 0 ≤ 1 + (m : ℝ) / Dd.k := add_nonneg zero_le_one (div_nonneg (by linarith) hk0.le)
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hcS hnT) haa.le) hLa) h1
  ·
    intro u0
    exact le_trans (collection_family_slope_gap K v0 m _ (T u0) Mw (gG u0) gE (hT u0) hMpos)
      (mul_nonneg (Real.rpow_nonneg hx0.le _) hb.le)
  ·
    intro u0
    obtain ⟨t1, t2, t3⟩ := coll_tr K v0 m _ (T u0) Mw (hbT K (PhiSet (H := H)).card (T u0)) (gG u0) gE
      (bTx G.x G.ε) (G.x ^ (-C.cHH)) hm hf (hTp u0) (hT4 u0) (by nlinarith) (hsmall u0) hMpos hsg (hT18 u0)
    exact ⟨le_trans t1 hb1, le_trans t2 hb2, le_trans t3 hb3⟩
  ·
    intro u0
    have e1 : Dd.Ga u0 = gG u0 := coll_Ga K v0 m _ (T u0) Mw _ _ _ hm
    have e2 : Dd.ASK u0 = gG u0 := (hgG u0).symm
    have e3 : Dd.IO u0 = 0 := coll_IO K v0 m _ (T u0) Mw _ _ _
    rw [e1, e2, e3, sub_self]
    exact ⟨hLoP, hLoP⟩

theorem lattice_completion : LatticeCompletion := by
  intro K _ _ _ _ v0 H _ _ _ D ell N TT T2 m a w G C cT T hS hW hTop
  obtain ⟨hx, hε, hk, hLa, hv, hm, hsg20, hC, hbar⟩ := hS
  have hT : ∀ u0, 4 ≤ T u0 := fun u0 => by
    have h1 := (hW u0).2.1
    have h2 : 1 ≤ (PhiSet (H := H)).card := phi_card_pos
    omega
  have hne : ∀ u0, Nonempty (Fin ((T u0 - 2) ^ (PhiSet (H := H)).card)) := fun u0 =>
    ⟨⟨0, (model_card _ (T u0) (hT u0)).1⟩⟩
  refine latticeCollapse K v0 H D ell N TT T2 m a w G C cT 0 T hx hε hk hLa hv hm hsg20 hC hbar
    (fun u0 => (hW u0).1) (fun u0 => (hW u0).2.1) (fun u0 => (hW u0).2.2.1) (fun u0 => (hW u0).2.2.2.1)
    (fun u0 => (hW u0).2.2.2.2.1) (fun u0 => (hW u0).2.2.2.2.2) le_rfl (fun u0 => ?_) (fun u0 => ?_) (fun u0 => ?_)
  · have := hne u0
    rw [(standard_lattice_semistable K _).2.2, neg_zero]
  · have := hne u0
    rw [(standard_lattice_semistable K _).2.1]
    have hb : 0 < bTx G.x G.ε := Real.exp_pos _
    have ha : 0 ≤ aTx G.x G.ε := mul_nonneg (by linarith) hb.le
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.2.2.2.2.2.2.1 (Nat.cast_nonneg _)) ha) hLa
  · rw [zero_add]
    exact hTop u0

section Lm
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

def lm_S (Q : Finset ℕ) : Finset (slopeLatticeData.FinPl K) := Q.biUnion (plOver K)

def lmFam (v : InfinitePlace K) (m f T Mw : ℕ) (hb gE : ℝ) (Q : Finset ℕ) (gn : Fin m → ℕ → ℝ) : Fam (Fin Mw) m where
  K := K
  Wd := Fin ((T - 2) ^ f) → K
  κ := Fin ((T - 2) ^ f)
  κ₁ := Fin ((T - 1) ^ f - (T - 2) ^ f)
  V := fun _ => Fin ((T - 2) ^ f) → K
  ι := fun _ => Fin ((T - 2) ^ f)
  Vf := fun _ => Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f) → K
  ιf := fun _ => Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f)
  b' := Pi.basisFun K _
  X' := fun _ => 1
  cc := stdLat K _
  b := fun _ => Pi.basisFun K _
  X := fun _ _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1
  M := fun _ => stdLat K _
  N0 := fun _ => Formalism.HermitianLatticesTheory.idealSmul
    ((slopeLatticeData.idealPow (tau0 K 2 0) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (stdLat K _)
  bf := fun _ => Pi.basisFun K _
  Xf := fun _ _ => 1
  Mf := fun _ => stdLat K _
  σ := fun _ => tau0 K 2 0
  τ := tau0 K 2 0
  B := fun _ => LinearMap.id
  v := v
  Y := fun _ => 1
  Y' := 1
  Ball := fun _ => inclMat _ _
  γ := fun _ => 1
  Bf := fun _ => 1
  Vr := fun _ => inclMat _ _
  S := lm_S K Q
  gain := fun j w => gn j (prBelow w)
  Fj := fun j w => bump K m gE w - gn j (prBelow w)
  Ej := fun _ _ w => bump K m gE w
  iop := fun _ => 0
  T := fun _ => T
  h := fun _ => max (htMap (Pi.basisFun K (Fin ((T - 2) ^ f)))
    (fun _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1) (Pi.basisFun K (Fin ((T - 2) ^ f))) (fun _ => 1)
    LinearMap.id) hb
  lam := fun _ => 0
  Dstar := ((T - 1) ^ f : ℕ)
  η0 := 0
  η1 := 0
  e0 := 0

variable (v : InfinitePlace K) (m f T Mw : ℕ) (hb gE : ℝ) (Q : Finset ℕ) (gn : Fin m → ℕ → ℝ)

end Lm

section LmLoss
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {m : ℕ}

def lm_gn (D : ArithData H) (N : ℕ) (TT : Finset H) (a : H → ℝ) (w : Fin m → E0 × H → ℝ) (Xpp : ℝ) (j : Fin m)
    (p : ℕ) : ℝ :=
  if p ∈ inertPs D N ∧ (p : ℝ) ≤ Xpp then
    ∑ t ∈ TT, DeficitSplitLemmas.askAt ((Finset.Icc 1 N).filter (fun i => ¬ InPhi (i • D.frob p))) (a t) p
      (fun i => w j (partner t (i • D.frob p)))
  else 0

def lm_Lp (D : ArithData H) (N : ℕ) (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (P : PrimeWindowSizeBounds.Par)
    (u0 : H) : LossP H m where
  cl := fun p => if (p : ℝ) ≤ P.Xpp then DeficitSplitLemmas.PClass.served else DeficitSplitLemmas.PClass.high
  TTp := fun _ => TT
  gainP := lm_gn D N TT a (w u0) P.Xpp
  tauP := fun _ => 0
  lo := fun _ => 0
  fl := fun _ => 0
  L₁ := fun p => Real.logb p P.K₀ + 1

end LmLoss

section LmMain
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v0 : InfinitePlace K)
  {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {m : ℕ}
  (D : ArithData H) (N : ℕ) (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (P : PrimeWindowSizeBounds.Par) (T : H → ℕ)
  (Mw : ℕ) (gE : ℝ)

def lm_Q (u0 : H) : Finset ℕ := insert 2 (insert (T u0) (inertPs D N))

def lm_Fm : H → Fam (Fin Mw) m := fun u0 =>
  lmFam K v0 m (PhiSet (H := H)).card (T u0) Mw (hbT K (PhiSet (H := H)).card (T u0)) gE (lm_Q D N T u0)
    (lm_gn D N TT a (w u0) P.Xpp)

def lm_ld (u0 : H) : PrimeWindowSizeBounds.LD (PlAll (Ω := Unit) (W := fun _ _ => Fin Mw) (fun _ => lm_Fm K v0 D N TT a w P T Mw gE))
    (Fin m) H :=
  ldOf (Ω := Unit) (W := fun _ _ => Fin Mw) D N (fun _ => a) (fun _ => w) (fun _ => lm_Fm K v0 D N TT a w P T Mw gE)
    (fun u0 _ => lm_Lp D N TT a w P u0) u0 ()

variable {D N T}

variable (D N T)

end LmMain

section LmMain2
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v0 : InfinitePlace K)
  {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {m : ℕ}
  (D : ArithData H) (N : ℕ) (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (P : PrimeWindowSizeBounds.Par) (T : H → ℕ)
  (Mw : ℕ) (gE : ℝ)

end LmMain2

theorem ev_level (f T : ℕ) (bb : ℝ) (hf : 1 ≤ f) (h1 : (64 * (f : ℝ) ^ 2 + 5 : ℝ) ≤ (T : ℝ))
    (h2 : 8 * (f : ℝ) * bb ^ 2 ≤ (T : ℝ)) :
    4 * (f : ℝ) / (T : ℝ) * bb ^ 2 + (f : ℝ) * Real.log ((T : ℝ) - 1) / ((T : ℝ) - 2) ≤ 1 := by
  have hfr : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hTpos : (0 : ℝ) < (T : ℝ) := by nlinarith
  have hA : 4 * (f : ℝ) / (T : ℝ) * bb ^ 2 ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hTpos]
    linarith
  set y : ℝ := (T : ℝ) - 1 with hy
  have hy1 : 64 * (f : ℝ) ^ 2 + 4 ≤ y := by rw [hy]; linarith
  have hypos : 0 < y := by nlinarith
  have hs : 8 * (f : ℝ) ≤ Real.sqrt y := by
    rw [show 8 * (f : ℝ) = Real.sqrt ((8 * (f : ℝ)) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hspos : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos
  have hlog : Real.log y ≤ 2 * Real.sqrt y := by
    have h4 := Real.log_le_sub_one_of_pos hspos
    have h5 : Real.log y = 2 * Real.log (Real.sqrt y) := by
      rw [Real.log_sqrt hypos.le]; ring
    rw [h5]; linarith
  have hsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hypos.le
  have hB : (f : ℝ) * Real.log y / ((T : ℝ) - 2) ≤ 1 / 2 := by
    have hden : 0 < (T : ℝ) - 2 := by nlinarith
    rw [div_le_iff₀ hden]
    have h6 : (T : ℝ) - 2 = y - 1 := by rw [hy]; ring
    rw [h6]
    have h7 : (f : ℝ) * Real.log y ≤ (f : ℝ) * (2 * Real.sqrt y) :=
      mul_le_mul_of_nonneg_left hlog (by linarith)
    have h8 : (f : ℝ) * (2 * Real.sqrt y) ≤ Real.sqrt y * Real.sqrt y / 4 := by nlinarith
    rw [hsq] at h8
    nlinarith
  linarith

theorem ev_prime (f : ℕ) (x b : ℝ) (hf : 1 ≤ f) (hx : 1 ≤ x) (hE : 100 * (f : ℝ) ^ 2 * x ^ 2 ≤ b) :
    ∃ T : ℕ, T.Prime ∧ 4 * f ≤ T ∧ 18 * (f : ℝ) * x ^ 2 ≤ (T : ℝ) ∧
      4 * (f : ℝ) / (T : ℝ) * b ^ 2 + (f : ℝ) * Real.log ((T : ℝ) - 1) / ((T : ℝ) - 2) ≤ 1 ∧ (T : ℝ) ≤ b ^ 4 := by
  have hfr : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx
  have hf2 : (f : ℝ) ≤ (f : ℝ) ^ 2 := by nlinarith
  have hfx : (f : ℝ) ^ 2 ≤ (f : ℝ) ^ 2 * x ^ 2 := le_mul_of_one_le_right (by positivity) hx2
  have hfx' : (f : ℝ) * x ^ 2 ≤ (f : ℝ) ^ 2 * x ^ 2 := mul_le_mul_of_nonneg_right hf2 (by positivity)
  have hb100 : 100 ≤ b := by nlinarith
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 64 * f ^ 2 + ⌈8 * (f : ℝ) * b ^ 2⌉₊ + ⌈18 * (f : ℝ) * x ^ 2⌉₊ + 5 := ⟨_, rfl⟩
  obtain ⟨T, hTp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul M (by omega)
  have c1 : (⌈8 * (f : ℝ) * b ^ 2⌉₊ : ℝ) < 8 * (f : ℝ) * b ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have c2 : (⌈18 * (f : ℝ) * x ^ 2⌉₊ : ℝ) < 18 * (f : ℝ) * x ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have d1 : 8 * (f : ℝ) * b ^ 2 ≤ (⌈8 * (f : ℝ) * b ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have d2 : 18 * (f : ℝ) * x ^ 2 ≤ (⌈18 * (f : ℝ) * x ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have hMr : (M : ℝ) = 64 * (f : ℝ) ^ 2 + (⌈8 * (f : ℝ) * b ^ 2⌉₊ : ℝ) + (⌈18 * (f : ℝ) * x ^ 2⌉₊ : ℝ) + 5 := by
    rw [hM]; push_cast; ring
  have hTM : (M : ℝ) ≤ (T : ℝ) := by exact_mod_cast hlt.le
  have hT2M : (T : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hle
  have p1 : (0 : ℝ) ≤ 8 * (f : ℝ) * b ^ 2 := by positivity
  have p2 : (0 : ℝ) ≤ 18 * (f : ℝ) * x ^ 2 := by positivity
  have p3 : (0 : ℝ) ≤ 64 * (f : ℝ) ^ 2 := by positivity
  refine ⟨T, hTp, ?_, by linarith, ev_level f T b hf (by linarith) (by linarith), ?_⟩
  · have : 4 * f ≤ 64 * f ^ 2 := by nlinarith
    omega
  · have hb0 : 0 < b := by linarith
    have e1 : 8 * (f : ℝ) * b ^ 2 ≤ b ^ 3 := by
      have : 8 * (f : ℝ) ≤ b := by nlinarith
      calc 8 * (f : ℝ) * b ^ 2 ≤ b * b ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
        _ = b ^ 3 := by ring
    have e2 : b ≤ b ^ 3 := by
      have : 1 ≤ b ^ 2 := one_le_pow₀ (by linarith)
      calc b = b * 1 := by ring
        _ ≤ b * b ^ 2 := mul_le_mul_of_nonneg_left this hb0.le
        _ = b ^ 3 := by ring
    have e3 : 100 * b ^ 3 ≤ b ^ 4 := by
      calc 100 * b ^ 3 ≤ b * b ^ 3 := mul_le_mul_of_nonneg_right hb100 (by positivity)
        _ = b ^ 4 := by ring
    have e4 : 0 < b ^ 3 := by positivity
    nlinarith

theorem ev_wF_pos {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (x ε : ℝ) (m : ℕ) (TT T2 : Finset H)
    (hx : 0 < x) (u0 : H) (j : Fin m) (ρ : E0 × H) : 0 < ModelText.wF x ε m TT T2 u0 j ρ := by
  have hb : 0 < bTx x ε := Real.exp_pos _
  have he : 0 < ModelText.etaTx x ε := Real.exp_pos _
  have hbp : 0 < bpTx x ε := div_pos (mul_pos hx hb) (Real.exp_pos _)
  have hn : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hw : 0 < wppTx x ε (Fintype.card H) := div_pos hbp (mul_pos hx hn)
  unfold ModelText.wF
  split_ifs
  · linarith
  · linarith
  · exact hw

theorem ev_top_arith (c m A lA lT lg γ lx xe l2 E1 E2 : ℝ) (hc : 0 ≤ c) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hlg : m * lg = lT - m * (l2 + xe)) (hlA : lA = lx + xe) (h : 2 + γ + l2 ≤ lx) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) :
    c * (m * A) ≤ c * (m * ((A * lA - A) - A * γ) - A * lT) + m * (c * A) * lg + E1 + E2 := by
  have key : c * (m * ((A * lA - A) - A * γ) - A * lT) + m * (c * A) * lg = c * (m * A) * (lx - 1 - γ - l2) := by
    have h1 : m * (c * A) * lg = c * A * (m * lg) := by ring
    rw [h1, hlg, hlA]; ring
  rw [key]
  have h2 : c * (m * A) * 1 ≤ c * (m * A) * (lx - 1 - γ - l2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

def evG (x ε lg : ℝ) : Glob :=
  ⟨x, ε, ModelText.kTx x ε, Real.log (aTx x ε) + x ^ (ε / 3), Real.pi, lg, 1 / 4, 6 * x ^ (-(1 : ℝ)), 0⟩

def evC : Consts := ⟨1, 1, 1, 1, 4, 1, 4, 1, 1, 1⟩

theorem ev_top_arith' (c m A lA lT lg γ lx xe l2 : ℝ) (hc : 0 ≤ c) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hlg : m * lg = lT - m * (l2 + xe)) (hlA : lA = lx + xe) (h : 2 + γ + l2 ≤ lx) :
    c * (m * A) ≤ c * (m * ((A * lA - A) - A * γ) - A * lT) + m * (c * A) * lg := by
  have := ev_top_arith c m A lA lT lg γ lx xe l2 0 0 hc hm hA hlg hlA h le_rfl le_rfl
  linarith

theorem ev_logW (x k : ℝ) (Mw : ℕ) (h48 : 48 ≤ x) (hk2 : x ^ 2 ≤ k) (hM0 : 0 < Mw) (hMx : (Mw : ℝ) < x + 1) :
    Real.log (Mw : ℝ) ≤ (k - 3) * Real.log 2 := by
  have hMp : (0 : ℝ) < (Mw : ℝ) := by exact_mod_cast hM0
  have h1 := Real.log_le_sub_one_of_pos hMp
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h3 : (3 : ℝ) ≤ x ^ 2 := by nlinarith
  have h2 : (x ^ 2 - 3) * (1 / 2) ≤ (k - 3) * Real.log 2 :=
    mul_le_mul (by linarith) hl2 (by norm_num) (by linarith)
  nlinarith

theorem ev_trace (x xe b c : ℝ) (h48 : 48 ≤ x) (hxe : 1 ≤ xe) (hb : 0 < b) (hc : 1 ≤ c) :
    (6 * x ^ (-(1 : ℝ)) + 4 * Real.sqrt 0) * (x ^ (1 : ℝ) * b) ≤ 4 * xe * (c * (x * b)) := by
  have hx0 : 0 < x := by linarith
  rw [Real.sqrt_zero, mul_zero, add_zero, Real.rpow_neg_one, Real.rpow_one]
  have e : 6 * x⁻¹ * (x * b) = 6 * b := by field_simp
  rw [e]
  have ha0 : 0 < x * b := mul_pos hx0 hb
  have h2 : x * b ≤ c * (x * b) := le_mul_of_one_le_left ha0.le hc
  have h3 : c * (x * b) ≤ xe * (c * (x * b)) := le_mul_of_one_le_left (by positivity) hxe
  have h4 : 6 * b ≤ 4 * (x * b) := by nlinarith
  linarith

section EvModel
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem ev_errW (x ε lg : ℝ) (m N Mw : ℕ) (TT T2 : Finset H) (Fm : H → Fam (Fin Mw) m) (h48 : 48 ≤ x)
    (g3 : ErrWindows (ModelText.textData x ε m TT T2) ModelText.CF (XppTx x ε (Fintype.card H)) 15 2)
    (hM0 : 0 < Mw) (hM1 : (Mw : ℝ) < x + 1) :
    ErrWindows (mkData (evG x ε lg) evC.cHH Model.DA (fun _ => 0) N TT T2 (fun _ => aTx x ε)
      (ModelText.wF x ε m TT T2) Fm) evC (XppH H (evG x ε lg)) 15 4 := by
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩ := g3
  have hε0 : 0 < ε := w2
  have hx1 : 1 ≤ x := by linarith only [h48]
  have hlogb : Real.log (bTx x ε) = x ^ ε := Real.log_exp _
  refine ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, ?_, ?_, w15, w16, w17, w18, w19, w20, w21, w22, w23,
    ?_, ?_, ?_, le_rfl, ?_⟩, ?_⟩
  · show 0 ≤ Real.log (bTx x ε)
    rw [hlogb]; exact w13
  · show Real.log (bTx x ε) ≤ 2 * x ^ ε
    rw [hlogb]; exact w14
  · intro u0
    show Real.log ((Fintype.card (Fin Mw) : ℕ) : ℝ) ≤ (ModelText.kTx x ε - 3) * Real.log 2
    rw [Fintype.card_fin]
    refine ev_logW x _ Mw h48 ?_ hM0 hM1
    have := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [hε0] : (2 : ℝ) ≤ (9 : ℝ) / 2 + 10 * ε)
    rwa [Real.rpow_two] at this
  · show (1 : ℝ) / 4 ≤ 1 / 2
    norm_num
  · show 0 ≤ 6 * x ^ (-(1 : ℝ))
    have := Real.rpow_nonneg (by linarith only [h48] : (0 : ℝ) ≤ x) (-(1 : ℝ))
    linarith only [this]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [evC]
  · exact ev_trace x (x ^ ε) (bTx x ε) (Fintype.card TT : ℝ) h48 (Real.one_le_rpow hx1 hε0.le) (Real.exp_pos _) w6

theorem ev_levelW (x ε lg : ℝ) (m T : ℕ) (TT T2 : Finset H) (h48 : 48 ≤ x) (hm1 : 1 ≤ m)
    (hLa : 0 ≤ Real.log (aTx x ε) + x ^ (ε / 3)) (hk0 : 0 < ModelText.kTx x ε)
    (hN : NodeSizes T2 (bTx x ε) (bpTx x ε) (ModelText.etaTx x ε) (ModelText.wF x ε m TT T2))
    (heta : ModelText.etaTx x ε + 1 ≤ bTx x ε) (hbpb : bpTx x ε ≤ bTx x ε)
    (hTp : T.Prime) (hT4 : 4 * (PhiSet (H := H)).card ≤ T)
    (hT18 : 18 * ((PhiSet (H := H)).card : ℝ) * x ^ 2 ≤ (T : ℝ))
    (hTlev : 4 * ((PhiSet (H := H)).card : ℝ) / (T : ℝ) * bTx x ε ^ 2
      + ((PhiSet (H := H)).card : ℝ) * Real.log ((T : ℝ) - 1) / ((T : ℝ) - 2) ≤ 1)
    (hlogT : Real.log (T : ℝ) ≤ 4 * x ^ ε)
    (hmlg : (m : ℝ) * lg = Real.log (T : ℝ) - (m : ℝ) * (Real.log 2 + x ^ ε)) :
    LevelWindow (evG x ε lg) evC (ModelText.wF x ε m TT T2) (fun _ => T) := by
  obtain ⟨nz1, nz2, nz3⟩ := hN
  have hx0 : 0 < x := by linarith
  have hb0 : 0 < bTx x ε := Real.exp_pos _
  have hlogb : Real.log (bTx x ε) = x ^ ε := Real.log_exp _
  have hm1r : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hfpos : (0 : ℝ) < ((PhiSet (H := H)).card : ℝ) := by exact_mod_cast (phi_card_pos (H := H))
  have hw2b : ∀ u0 j ρ, InPhi ρ → ModelText.wF x ε m TT T2 u0 j ρ ≤ 2 * bTx x ε := by
    intro u0 j ρ hρ
    by_cases ht : IsThickAt T2 u0 ρ
    · have := (nz2 u0 j ρ ht).2
      linarith
    · have := nz3 u0 j ρ hρ ht
      linarith
  have hlogw : ∀ u0 j (ρ : Fin (PhiSet (H := H)).card),
      Real.log (ModelText.wF x ε m TT T2 u0 j (ePhi ρ) * Real.pi / Real.pi) ≤ Real.log 2 + x ^ ε := by
    intro u0 j ρ
    have hρ : InPhi ((ePhi ρ : PhiSet (H := H)) : E0 × H) := (Finset.mem_filter.1 (ePhi ρ).2).2
    rw [mul_div_assoc, div_self Real.pi_ne_zero, mul_one]
    have := Real.log_le_log (nz1 u0 j _ hρ) (hw2b u0 j _ hρ)
    rwa [Real.log_mul two_ne_zero hb0.ne', hlogb] at this
  intro u0
  refine ⟨hTp, hT4, ?_, hTlev, ?_, ?_⟩
  · show 18 * ((PhiSet (H := H)).card : ℝ) / (x ^ (-(1 : ℝ))) ^ 2 ≤ (T : ℝ)
    rw [Real.rpow_neg_one]
    have : 18 * ((PhiSet (H := H)).card : ℝ) / (x⁻¹) ^ 2 = 18 * ((PhiSet (H := H)).card : ℝ) * x ^ 2 := by
      field_simp
    rw [this]
    exact hT18
  · show (∑ j : Fin m, (1 / ((PhiSet (H := H)).card : ℝ)) * ∑ ρ : Fin (PhiSet (H := H)).card,
        Real.log (ModelText.wF x ε m TT T2 u0 j (ePhi ρ) * Real.pi / Real.pi)) + (m : ℝ) * lg
        - 4 * ((Real.log (aTx x ε) + x ^ (ε / 3)) + (m : ℝ) ^ 2 * (Real.log (aTx x ε) + x ^ (ε / 3))
          / ModelText.kTx x ε) ≤ Real.log (T : ℝ)
    have h1 : ∀ j : Fin m, (1 / ((PhiSet (H := H)).card : ℝ)) * ∑ ρ : Fin (PhiSet (H := H)).card,
        Real.log (ModelText.wF x ε m TT T2 u0 j (ePhi ρ) * Real.pi / Real.pi) ≤ Real.log 2 + x ^ ε := by
      intro j
      have h2' := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (PhiSet (H := H)).card)))
        fun ρ _ => hlogw u0 j ρ
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2'
      calc _ ≤ (1 / ((PhiSet (H := H)).card : ℝ)) * (((PhiSet (H := H)).card : ℝ) * (Real.log 2 + x ^ ε)) :=
            mul_le_mul_of_nonneg_left h2' (by positivity)
        _ = Real.log 2 + x ^ ε := by field_simp
    have h3 := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) fun j _ => h1 j
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
    have hsl : 0 ≤ 4 * ((Real.log (aTx x ε) + x ^ (ε / 3)) + (m : ℝ) ^ 2 * (Real.log (aTx x ε) + x ^ (ε / 3))
          / ModelText.kTx x ε) := by positivity
    rw [hmlg]
    linarith
  · show Real.log (T : ℝ) ≤ 4 * (m : ℝ) * Real.log (bTx x ε)
    rw [hlogb]
    have h0 : 0 ≤ x ^ ε := Real.rpow_nonneg hx0.le _
    have : 4 * x ^ ε * 1 ≤ 4 * x ^ ε * (m : ℝ) := mul_le_mul_of_nonneg_left hm1r (by positivity)
    linarith

theorem ev_topW (x ε lg : ℝ) (m T N : ℕ) (TT T2 : Finset H) (h48 : 48 ≤ x) (hlx : 4 ≤ Real.log x)
    (hLa : 0 ≤ Real.log (aTx x ε) + x ^ (ε / 3)) (hk0 : 0 < ModelText.kTx x ε)
    (hmlg : (m : ℝ) * lg = Real.log (T : ℝ) - (m : ℝ) * (Real.log 2 + x ^ ε)) :
    TopAtLevel Model.DA (fun _ => 0) (evG x ε lg) evC N TT T2
      (fun _ => aTx x ε) (ModelText.wF x ε m TT T2) (fun _ => T) := by
  have hx0 : 0 < x := by linarith
  have hb0 : 0 < bTx x ε := Real.exp_pos _
  have hlogb : Real.log (bTx x ε) = x ^ ε := Real.log_exp _
  have ha0 : 0 < aTx x ε := mul_pos hx0 hb0
  have hloga : Real.log (aTx x ε) = Real.log x + x ^ ε := by
    unfold aTx; rw [Real.log_mul hx0.ne' hb0.ne', hlogb]
  intro u0
  have hL : (∑ t ∈ TT, ∑ j : Fin m, ASK Model.DA N (aTx x ε) t
      (ModelText.wF x ε m TT T2 u0 j)) ≤ (TT.card : ℝ) * ((m : ℝ) * aTx x ε) := by
    calc _ ≤ ∑ _t ∈ TT, ∑ _j : Fin m, aTx x ε := Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun j _ =>
          ModelEv.askDA_le _ _ _ _ ha0.le (fun ρ => (ev_wF_pos x ε m TT T2 hx0 u0 j ρ).le)
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  refine le_trans hL (le_add_of_le_of_nonneg (le_add_of_le_of_nonneg ?_ ?_) ?_)
  · show (TT.card : ℝ) * ((m : ℝ) * aTx x ε) ≤
      (∑ _t : TT, ((m : ℝ) * (ph (aTx x ε) - aTx x ε * (Real.eulerMascheroniConstant + Real.log (Real.pi / Real.pi)
          - (0 : ℂ).re)) - aTx x ε * Real.log (T : ℝ))) + (m : ℝ) * (∑ _t : TT, aTx x ε) * lg
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, nsmul_eq_mul,
      div_self Real.pi_ne_zero, Real.log_one, Complex.zero_re, add_zero, sub_zero]
    unfold ph
    refine ev_top_arith' _ _ _ _ _ _ _ (Real.log x) (x ^ ε) (Real.log 2) (Nat.cast_nonneg _) (Nat.cast_nonneg _) ha0.le
      hmlg hloga ?_
    have h1 := Real.eulerMascheroniConstant_lt_two_thirds
    have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  · exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_one (Nat.cast_nonneg _)) ha0.le) hLa
  · show 0 ≤ (1 : ℝ) * (m : ℝ) * ((2 * (Fintype.card H : ℝ)) * m * bTx x ε * x ^ ε
          + (T2.card : ℝ) * ModelText.kTx x ε * bTx x ε * x ^ ε
            / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε)))) * x ^ ((1 : ℝ) * ε)
    positivity

end EvModel

theorem ev_at (ε x : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (h48 : 48 ≤ x) (hlx : 4 ≤ Real.log x)
    (h24 : x ^ (24 : ℝ) ≤ Real.exp (x ^ ε)) (hF : ModelText.FamAt ε x) :
    Chain2aCoreNoAnalytic 1 1 4 1 15 ε x := by
  obtain ⟨n, i, m, TT, T2, s1, s2, s3, s4, s5, s6, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hF
  have hx0 : 0 < x := by linarith only [h48]
  have hx1 : 1 ≤ x := by linarith only [h48]
  have hb0 : 0 < bTx x ε := Real.exp_pos _
  have hlogb : Real.log (bTx x ε) = x ^ ε := Real.log_exp _
  have hm1r : (1 : ℝ) ≤ (m : ℝ) := le_trans (Real.one_le_rpow hx1 (by linarith only [hε1])) s3
  have hm1 : 1 ≤ m := by exact_mod_cast hm1r
  have hm0 : (m : ℝ) ≠ 0 := by
    intro h; rw [h] at hm1r; norm_num at hm1r
  have hf1 : 1 ≤ (PhiSet (H := ZMod n)).card := phi_card_pos
  have hf2n : ((PhiSet (H := ZMod n)).card : ℝ) = 2 * (n : ℝ) := by
    have := Model.fPl_eq (H := ZMod n)
    rw [ZMod.card] at this
    exact this
  have hn10 : (n : ℝ) ≤ 2 * x ^ (10 : ℕ) := by
    have h1 : x ^ (2 + 8 * ε) ≤ x ^ ((10 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith only [hε1])
    rw [Real.rpow_natCast] at h1
    linarith only [h1, s2]
  have hE : 100 * ((PhiSet (H := ZMod n)).card : ℝ) ^ 2 * x ^ 2 ≤ bTx x ε := by
    rw [hf2n]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have h1 : (2 * (n : ℝ)) ^ 2 ≤ (4 * x ^ 10) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith only [hn10]) 2
    have h2 : x ^ (24 : ℝ) = x ^ (24 : ℕ) := by rw [← Real.rpow_natCast]; norm_num
    have h3 : (1600 : ℝ) ≤ x ^ 2 := by nlinarith only [h48]
    calc 100 * (2 * (n : ℝ)) ^ 2 * x ^ 2 ≤ 100 * (4 * x ^ 10) ^ 2 * x ^ 2 := by gcongr
      _ = 1600 * x ^ 22 := by ring
      _ ≤ x ^ 2 * x ^ 22 := by gcongr
      _ = x ^ (24 : ℕ) := by ring
      _ ≤ bTx x ε := by rw [← h2]; exact h24
  obtain ⟨T, hTp, hT4, hT18, hTlev, hTb⟩ := ev_prime _ x (bTx x ε) hf1 hx1 hE
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hTp.pos
  have hlogT : Real.log (T : ℝ) ≤ 4 * x ^ ε := by
    have := Real.log_le_log hT0 hTb
    rw [Real.log_pow, hlogb] at this
    exact_mod_cast this
  obtain ⟨lg, hlg⟩ : ∃ lg : ℝ, lg = Real.log (T : ℝ) / (m : ℝ) - (Real.log 2 + x ^ ε) := ⟨_, rfl⟩
  have hmlg : (m : ℝ) * lg = Real.log (T : ℝ) - (m : ℝ) * (Real.log 2 + x ^ ε) := by
    rw [hlg]; field_simp
  have w8 : x * (m : ℝ) ≤ ModelText.kTx x ε := g3.1.2.2.2.2.2.2.2.1
  have w10 : 1 ≤ ModelText.kTx x ε := g3.1.2.2.2.2.2.2.2.2.2.1
  have w15 : 0 ≤ Real.log (aTx x ε) + x ^ (ε / 3) := g3.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have w18 : ModelText.kTx x ε * bpTx x ε ≤ aTx x ε := g3.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk0 : 0 < ModelText.kTx x ε := lt_of_lt_of_le one_pos w10
  have z1 : 0 ≤ ModelText.etaTx x ε := g5.1
  have z3 : 0 < bpTx x ε := g5.2.2.1
  have hk_x : x ≤ ModelText.kTx x ε := by
    have h7 : x * 1 ≤ x * (m : ℝ) := mul_le_mul_of_nonneg_left hm1r hx0.le
    linarith only [h7, w8]
  have hbpb : bpTx x ε ≤ bTx x ε := by
    have h1 : x * bpTx x ε ≤ x * bTx x ε := le_trans (mul_le_mul_of_nonneg_right hk_x z3.le) w18
    exact le_of_mul_le_mul_left h1 hx0
  have heta : ModelText.etaTx x ε + 1 ≤ bTx x ε := by
    have h6 : 6 * fPl (ZMod n) * (x + 1) * (ModelText.etaTx x ε + 1) ≤ bTx x ε / x := g6.2
    have hfp : 1 ≤ fPl (ZMod n) := by
      show (1 : ℝ) ≤ ((PhiSet (H := ZMod n)).card : ℝ)
      exact_mod_cast hf1
    have hc : 1 ≤ 6 * fPl (ZMod n) * (x + 1) := by nlinarith only [hfp, hx1]
    have h1 : ModelText.etaTx x ε + 1 ≤ 6 * fPl (ZMod n) * (x + 1) * (ModelText.etaTx x ε + 1) :=
      le_mul_of_one_le_left (by linarith only [z1]) hc
    have h2 : bTx x ε / x ≤ bTx x ε := div_le_self hb0.le hx1
    linarith only [h6, h1, h2]
  have hSigns : CompletionSigns (evG x ε lg) evC 1 m := by
    refine ⟨hx1, hε0, w10, w15, Real.pi_pos, hm1, ?_, ?_, ⟨le_rfl, le_rfl, le_rfl, ?_⟩⟩
    · show x ^ (-(1 : ℝ)) ≤ 1 / 20
      rw [Real.rpow_neg_one, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith only [h48])
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [evC]
    · show (0 : ℝ) ≤ 1 / 4
      norm_num
  have hLevel := ev_levelW x ε lg m T TT T2 h48 hm1 w15 hk0 g5.2.2.2.2.2.2.1 heta hbpb hTp hT4 hT18 hTlev hlogT hmlg
  have hTop := ev_topW x ε lg m T (ModelText.NF (ZMod n) x ε) TT T2 h48 hlx w15 hk0 hmlg
  let _ : StarRing (CyclotomicField 3 ℚ) := starRingOfComm
  have : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) := CyclotomicField.isCyclotomicExtension 3 ℚ
  have : IsTotallyComplex (CyclotomicField 3 ℚ) :=
    IsCyclotomicExtension.Rat.isTotallyComplex (n := 3) (CyclotomicField 3 ℚ) (by norm_num)
  obtain ⟨v0⟩ : Nonempty (InfinitePlace (CyclotomicField 3 ℚ)) := inferInstance
  obtain ⟨Mw, Fm, hM0, hM1, -, hL, hLoss⟩ := lattice_completion (CyclotomicField 3 ℚ) v0 (ZMod n) Model.DA
    (fun _ => 0) (ModelText.NF (ZMod n) x ε) TT T2 m (fun _ => aTx x ε) (ModelText.wF x ε m TT T2) (evG x ε lg) evC 1
    (fun _ => T) hSigns hLevel hTop
  have hMx : (Mw : ℝ) < x + 1 := by
    have h : (Mw : ℝ) < x ^ (1 : ℝ) + 1 := hM1
    rwa [Real.rpow_one] at h
  exact ⟨ZMod n, inferInstance, inferInstance, inferInstance, fun _ => Fin Mw, inferInstance, fun _ => ⟨⟨0, hM0⟩⟩, m,
    Model.DA, fun _ => 0, evG x ε lg, evC, 1, ModelText.NF (ZMod n) x ε, TT, T2, fun _ => aTx x ε,
    ModelText.wF x ε m TT T2, Fm, ModelText.etaTx x ε, ModelText.thTx x ε, rfl, rfl, le_rfl, le_rfl, le_rfl, g1, hL,
    ev_errW x ε lg m _ Mw TT T2 Fm h48 g3 hM0 hMx, g5, Real.exp_pos _, g6, g7, hLoss⟩

theorem chain_lattice_sizes_model_eventually : Chain2aSizesModelEv := by
  intro ε h0 h1
  obtain ⟨x1, hx1⟩ := ModelText.family ε h0 h1
  have e1 := ModelText.ev_rpow_le_exp 24 ε h0
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, (4 : ℝ) ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop 4
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1
    ((e1.and e2).and ((Filter.eventually_ge_atTop (48 : ℝ)).and (Filter.eventually_ge_atTop x1)))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨⟨f1, f2⟩, f3, f4⟩ := hx0 x hx
  exact ev_at ε x h0 h1 f3 f2 f1 (hx1 x f4)

end Formalism.LFunctionChainParameters.LChain2

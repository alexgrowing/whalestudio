import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSupLatticeDegreeTwistLowerBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwSecOfConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPointsDeepLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKeySecOfFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLogRootDiscSubLogHostPrimeLe

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.TwistDeg

open GlobalTheory.FlatTw GlobalTheory.FlatLine GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem logSum_bad_le {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) :
    logSum (GlobalTheory.FlatTw.badPrimes H l) ≤ Real.log 2 + Real.log H.d + Real.log |(discr E : ℝ)| + Real.log l.M' := by
  have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hD : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have hd := H.d_prime.ne_zero
  have hne : 2 * H.d * (discr E).natAbs * l.M' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hd) hD) hM
  have h0 : ∀ p ∈ (2 * H.d * (discr E).natAbs * l.M').primeFactors, (p : ℝ) ≠ 0 := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have e : Real.log 2 + Real.log H.d + Real.log |(discr E : ℝ)| + Real.log l.M' =
      Real.log ((2 * H.d * (discr E).natAbs * l.M' : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Nat.cast_natAbs, Int.cast_abs, Nat.cast_ofNat]
  rw [e, logSum, GlobalTheory.FlatTw.badPrimes, ← Real.log_prod h0, ← Nat.cast_prod]
  refine Real.log_le_log ?_ (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (Nat.prod_primeFactors_dvd _))
  exact_mod_cast Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

theorem lrd_eq (E : Type) [Field E] [NumberField E] :
    lrd E = Real.log |(discr E : ℝ)| / (Module.finrank ℚ E : ℝ) := by
  have h : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero E)
  rw [lrd, rootDiscr_def, Int.cast_abs, Real.log_rpow h, div_eq_inv_mul]

theorem numeric {f r L q a b s c : ℝ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hL : 1 ≤ L) (hq : q ≤ r)
    (hb0 : 0 ≤ b) (hb : b ≤ 3 * L) (hs0 : 0 ≤ s) (hs : s ≤ 6 * f * r) (hc : |a| ≤ 9 * r * L * s)
    (hB : c ≤ 1 + 2 * b + 2 * f * b + 30 * L) : -(120 * (f * r * L) ^ 2) ≤ a - q * b * s - c := by
  have h1 : q * b * s ≤ r * (3 * L) * (6 * f * r) := by gcongr
  have h2 : 9 * r * L * s ≤ 9 * r * L * (6 * f * r) := by gcongr
  have h3 : f * b ≤ f * (3 * L) := by gcongr
  have h4 : f * r ^ 2 * L ≤ (f * r * L) ^ 2 := by
    rw [show (f * r * L) ^ 2 = f * r ^ 2 * L * (f * L) by ring]
    exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hf hL)
  have h5 : f * L ≤ f * r ^ 2 * L := by
    rw [show f * r ^ 2 * L = f * L * r ^ 2 by ring]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hr)
  have h6 : L ≤ f * L := le_mul_of_one_le_left (by positivity) hf
  have h7 := (abs_le.1 hc).1
  nlinarith

theorem deg_twist_ge : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → ∀ (la : AllWt.Weight (T.Q.Dw j)) (w : Psi T.Q.H → ℤ) Z, (∀ τ, |w τ| ≤ 3 * (D.R.r : ℤ)) → GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0) → Y.degC la Z - Y.rkC la Z * (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2) ≤ Y.degC (la + GlobalTheory.FlatLine.parWt (T.Q.Dw j) w) Z := by
  intro hP
  refine ⟨120, by norm_num, fun D T hT j hp hq _ hj Y e o hY Lb hL hM hE _ _ c₁ hc hc₁ la w Z hw hG => ?_⟩
  have hn : 1 ≤ D.R.n := D.R.toFrame.ord_pos
  have h1 := D.R.two_le_m
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hrk : (0 : ℝ) ≤ Y.rkC la Z := Nat.cast_nonneg _
  rcases isEmpty_or_nonempty (Psi T.Q.H) with h0 | ⟨⟨τ₀⟩⟩
  · rw [show la + parWt (T.Q.Dw j) w = la from funext fun τ => h0.elim τ]
    exact sub_le_self _ (by positivity)
  obtain ⟨hpq, -, -, -, -, g, ee, F, -⟩ := hY.unf Y.d.c₂.F.val.toRingHom rfl
  have hK := GlobalTheory.KeyCover.nonempty_keySec_of_family _ _ _ _ _ _ Y.d.c₂.F.val.toRingHom rfl ee F (by omega) hY.geo
  obtain ⟨t, ht, -, hd⟩ := (GlobalTheory.FlatTwisting.twSec_of_flat _ _ _ _ _ _ _ Y.U (xiR D) _ hK hY.unf (by omega)
    (GlobalTheory.T.unramified_points_deep_level hP D T j Y e o hT hj hY)).2 ⟨c₁, hc⟩ Z w (hc Z τ₀).1.some.hasPts
  have key := GlobalTheory.FlatTw.degOn_add_rank_mul_degLo_le _ _ _ _ _ _ _ Y.U (xiR D) D (fun _ => D.sp.W j) Y.dict Z _ t _ _ hY.unf
    (AllWt.even_wtOf la 0) badPrimes_prime ht hG
  rw [← wtOf_add'] at key
  refine le_trans ?_ key
  rw [sub_eq_add_neg, ← mul_neg]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_trans ?_ (sub_le_sub_right hd _)) hrk)
  have hdeg : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have hd2 := abs_le.1 (GlobalTheory.abs_lrd_sub_log_d_le_lrd _ T.Q.H)
  have hcard : (Fintype.card (Psi T.Q.H) : ℝ) ≤ 2 * D.R.f := by
    have := Fintype.card_subtype_le fun τ : D.host.E →+* ℂ => τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0
    rw [Embeddings.card, hdeg] at this
    exact_mod_cast (Fintype.card_congr (Equiv.refl _)).le.trans this
  refine numeric hf hr hL (by exact_mod_cast (by omega : (T.Q.Dw j).q ≤ D.R.r)) (by linarith [hd2.1, hd2.2])
    (by rw [lrd_eq]; exact (log_rd_le_fieldSz _).trans hE) (Finset.sum_nonneg fun _ _ => abs_nonneg _) ?_ ?_ ?_
  · refine (Finset.sum_le_card_nsmul _ _ (3 * (D.R.r : ℝ)) fun τ _ => by exact_mod_cast hw τ).trans ?_
    rw [nsmul_eq_mul, Finset.card_univ]
    nlinarith
  · simp only [hc.c1_eq ⟨Z⟩]
    rw [← Finset.sum_mul, abs_mul, mul_comm]
    exact mul_le_mul hc₁ (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _) (by positivity)
  · refine (logSum_bad_le _ _).trans ?_
    have l2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    have hM' : Y.d.l₂.M' = Y.d.l₂.M := by rw [Level.M', hY.lev.2, Nat.lcm_one_right]
    have hD : Real.log |(discr D.host.E : ℝ)| = 2 * D.R.f * lrd D.host.E := by
      rw [lrd_eq, hdeg]; push_cast; field_simp
    rw [hM', hD]
    linarith [hd2.1]

end GlobalTheory.TwistDeg

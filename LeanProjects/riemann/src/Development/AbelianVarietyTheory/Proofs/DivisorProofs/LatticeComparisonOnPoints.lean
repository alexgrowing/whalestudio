import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLogDivPredLeReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightComparisonLocalGreen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetResidueLogBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumValuationLogLeLogDiscriminant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGreenDifferenceDeterminantLe

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Toroidal AlgebraicGeometry CategoryTheory

noncomputable section

namespace GlobalTheory.LatHt

def jump (E : Type) [Field E] [NumberField E] (p : ℕ) : ℝ := Real.log p / ((p : ℝ) - 1) + vDiff E p * Real.log p

theorem jump_nonneg (E : Type) [Field E] [NumberField E] (p : ℕ) : 0 ≤ jump E p := by
  refine add_nonneg ?_ (mul_nonneg (by unfold vDiff; positivity) (Real.log_natCast_nonneg p))
  rcases Nat.eq_zero_or_pos p with rfl | h
  · simp
  · have : (1 : ℝ) ≤ p := by exact_mod_cast h
    exact div_nonneg (Real.log_natCast_nonneg p) (by linarith)

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem abs_lgOf_rootSym_sub_le (τ : E →+* ℂ) (i : ℕ) (T : Finset ℕ) (v : HeightOneSpectrum (𝓞 F))
    (ε : Ext v) (y : AlgPt Y.Y) :
    |lgOf Y (rootSym Dw (ArIn.ind T) none τ i) v ε y - lgOf Y (rootSym Dw (ArIn.ind ∅) none τ i) v ε y| ≤
      if resP v ∈ T then |-Real.log (ε.w (resP v)) / Real.log (resP v)| * jump E (resP v) else 0 := by
  by_cases hp : (resP v).Prime
  swap
  · simp only [lgOf, dif_neg hp, sub_self, abs_zero]
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (jump_nonneg _ _)
    · exact le_rfl
  haveI := Fact.mk hp
  have hs (a : ℕ → Bool) (Φ : Sym E → ℝ) : ((rootSym Dw a none τ i).sum fun b n => (n : ℝ) * Φ b) =
      if i < Dw.p then Φ (a, none, .inl (τ, i)) else -Φ (a, none, .inl (conjEmb τ, Dw.p + Dw.q - 1 - i)) := by
    unfold rootSym
    split_ifs <;> rw [Finsupp.sum_single_index (by simp)] <;> push_cast <;> ring
  have h0 : ArIn.ind ∅ (resP v) = false := by simp [ArIn.ind]
  simp only [lgOf, dif_pos hp]
  rewrite [expo_rootSym Dw (ArIn.ind T), expo_rootSym Dw (ArIn.ind ∅), add_sub_add_left_eq_sub, ← mul_sub, abs_mul, hs, hs]
  dsimp only
  rewrite [h0]
  by_cases hT : resP v ∈ T
  · have hb : ArIn.ind T (resP v) = true := by simp [ArIn.ind, hT]
    rewrite [if_pos hT, hb]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    split_ifs
    · exact LgDiff.abs_lnStep_sub_le HTBound.htBound _ _ _ _ _ _
    · rw [neg_sub_neg, abs_sub_comm]
      exact LgDiff.abs_lnStep_sub_le HTBound.htBound _ _ _ _ _ _
  · have hb : ArIn.ind T (resP v) = false := by simp [ArIn.ind, hT]
    rewrite [hb, sub_self, abs_zero, mul_zero, if_neg hT]
    exact le_rfl

theorem abs_ht_rootSym_sub_le {C : CxSt F} (h₀ : ∀ (σ : F →+* ℂ) (n : Letter Dw → ℤ), C.Met Y.Y σ (divOf Y n))
    (τ : E →+* ℂ) (i : ℕ) (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (x : Y.Y.X) :
    |(adlOf Y (fun _ => h₀) (rootSym Dw (ArIn.ind T) none τ i)).ht x -
      (adlOf Y (fun _ => h₀) (rootSym Dw (ArIn.ind ∅) none τ i)).ht x| ≤ ∑ p ∈ T, jump E p := by
  have e2 : adlOf Y (fun _ => h₀) (rootSym Dw (ArIn.ind ∅) none τ i) =
      { adlOf Y (fun _ => h₀) (rootSym Dw (ArIn.ind T) none τ i) with
        lg := lgOf Y (rootSym Dw (ArIn.ind ∅) none τ i) } := by
    unfold adlOf
    rw [expo_rootSym Dw (ArIn.ind T), expo_rootSym Dw (ArIn.ind ∅)]
  obtain ⟨hle, S, hS, hsum⟩ := PlaceSum.sum_localDeg_le (F := F) T hT (jump E) (jump_nonneg E)
  have hc (v : HeightOneSpectrum (𝓞 F)) :
      0 ≤ -Real.log (NumberField.HeightOneSpectrum.adicAbv F v (resP v : F)) / Real.log (resP v) :=
    div_nonneg (neg_nonneg.2 (Real.log_nonpos (AbsoluteValue.nonneg _ _) (hle v))) (Real.log_natCast_nonneg _)
  rw [e2]
  refine Adl.abs_ht_sub_ht_with_lg_le _ _ _ S
    (fun v => (-Real.log (NumberField.HeightOneSpectrum.adicAbv F v (resP v : F)) / Real.log (resP v)) *
      jump E (resP v)) _ (Finset.sum_nonneg fun p _ => jump_nonneg E p) ?_ ?_ ?_
  · intro v hv ε y
    have h := abs_lgOf_rootSym_sub_le Y τ i T v ε y
    rw [if_neg (fun h' => hv ((hS v).2 h'))] at h
    exact sub_eq_zero.1 (abs_nonpos_iff.1 h)
  · intro v ε y
    refine (abs_lgOf_rootSym_sub_le Y τ i T v ε y).trans ?_
    split_ifs
    · rw [← map_natCast (algebraMap F (AlgebraicClosure F)), ε.w_alg, abs_of_nonneg (hc v)]
    · exact mul_nonneg (hc v) (jump_nonneg _ _)
  · simpa [adlOf] using hsum

end Gen

theorem sum_jump_le {D : D7} {A : Amb D} (κ : Lv A) : ∃ K : ℝ, 0 ≤ K ∧ ∀ B : ℝ, 2 ≤ B →
    (∀ p ∈ Pad.setB κ B, p.Prime) ∧ ∑ p ∈ Pad.setB κ B, jump D.host.E p ≤ K * Real.log B := by
  set b : ℝ := ∑ p ∈ (2 * (NumberField.discr D.host.E).natAbs * κ.l.M').primeFactors, jump D.host.E p with hb
  have hb0 : 0 ≤ b := Finset.sum_nonneg fun p _ => jump_nonneg _ p
  have hv0 : 0 ≤ Real.log D.host.rdE := by simpa using PlaceBd.sum_vDiff_mul_log_le_log_rdE D ∅ (by simp)
  refine ⟨1 + 2 * (3 + Real.log D.host.rdE + b), by positivity, fun B hB => ⟨fun p hp => ?_, ?_⟩⟩
  · rcases Finset.mem_union.1 hp with h | h
    · exact (Finset.mem_filter.1 h).2
    · exact Nat.prime_of_mem_primeFactors h
  have hlB : 1 / 2 ≤ Real.log B := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log two_pos hB
    linarith
  have h1 := PrimeLogSum.sum_log_div_pred_le_real B (by linarith)
  have h2 := PlaceBd.sum_vDiff_mul_log_le_log_rdE D ((Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime)
    fun p hp => (Finset.mem_filter.1 hp).2
  have h3 : ∑ p ∈ Pad.setB κ B, jump D.host.E p ≤
      ∑ p ∈ (Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime, jump D.host.E p + b := by
    rw [Pad.setB, hb, ← Finset.sum_union_inter]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun p _ => jump_nonneg _ p)
  simp only [jump, Finset.sum_add_distrib] at h3 ⊢
  nlinarith

theorem latCmp : Hypotheses2 → HypothesesH → OnObj fun _ _ _ _ H h => LatCmp H h.pts := by
  intro _ _ D O _ _ A T H h
  obtain ⟨K, hK0, hK⟩ := sum_jump_le O.κ
  refine ⟨Fintype.card (DV.Rt D.what₂.Tau O.N) * K, fun B hB u y => ?_⟩
  obtain ⟨hp, hs⟩ := hK B hB
  have e1 := h.pts_is.L B hB y u
  have e2 := h.ht.h0 u y
  refine (congrArg abs (congrArg₂ (· - ·) e1 e2)).trans_le ?_
  rw [O.setB_eq]
  unfold Setup.htWt
  rw [neg_sub_neg, abs_sub_comm, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (g := fun _ => ‖u‖ * (K * Real.log B))
    fun x _ => ?_).trans_eq ?_)
  · rw [← mul_sub, abs_mul]
    refine mul_le_mul ((norm_le_pi_norm (u x.1) x.2).trans (norm_le_pi_norm u x.1)) ?_ (abs_nonneg _) (norm_nonneg _)
    exact (abs_ht_rootSym_sub_le (O.Φ.C _) (O.met.h0 _) _ _ _ hp _).trans hs
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring

end GlobalTheory.LatHt

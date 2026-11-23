import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsLogGrNormSubLe
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier AlgebraicGeometry CategoryTheory

set_option autoImplicit false

noncomputable section

open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.HTFrame
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal Limits

namespace GlobalTheory.LgDiff

attribute [local instance] Over.cartesianMonoidalCategory

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

open Classical in

theorem expo_single' (a : Sym E) (n : ℤ) (x : Letter Dw) :
    expo Dw (Finsupp.single a n) x = if letterOf Dw a.2.2 = some x then n else 0 :=
  Finsupp.sum_single_index (by simp)

theorem expo_detSym (a a' : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) :
    expo Dw (detSym Dw a R τ) = expo Dw (detSym Dw a' R τ) := by
  classical
  have h (b : ℕ → Bool) (x : Letter Dw) : expo Dw (detSym Dw b R τ) x =
      ∑ i ∈ Finset.range (Dw.p + Dw.q), expo Dw (rootSym Dw b R τ i) x := by
    unfold detSym expo
    rw [Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp)]
  funext x
  rw [h, h]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold rootSym
  split_ifs <;> simp only [expo_single']

theorem sum_detSym (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (Φ : Sym E → ℝ) :
    ((detSym Dw a R τ).sum fun b n => (n : ℝ) * Φ b) =
      ∑ i ∈ Finset.range (Dw.p + Dw.q), (if i < Dw.p then Φ (a, R, .inl (τ, i))
        else -Φ (a, R, .inl (conjEmb τ, Dw.p + Dw.q - 1 - i))) := by
  unfold detSym
  rw [← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold rootSym
  split_ifs <;> rw [Finsupp.sum_single_index (by simp)] <;> push_cast <;> ring

end Free

section Step

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem abs_log_grNorm_DR_HT_le (hB : HTBoundSt) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (p : ℕ) [hp : Fact p.Prime]
    (x : Sp ℂ_[p] ⟶ Z.X) {m : ℕ} (u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left)) (i : Fin m) :
    |Real.log (grNorm Z.t x (latDR Z.t x) u i) - Real.log (grNorm Z.t x (latHT Z.t p x) u i)| ≤
      Real.log p * (1 / ((p : ℝ) - 1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp2 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (p : ℂ_[p]) (n := p - 1) (Nat.sub_pos_of_lt hp.out.one_lt)
  have hc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub hp.out.one_lt.le, Nat.cast_one]
  have hna : ‖a‖ = (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
    have e : ‖a‖ ^ ((p : ℝ) - 1) = (p : ℝ)⁻¹ := by rw [← hc, Real.rpow_natCast, ← norm_pow, ha, hn]
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), ← e, one_div,
      Real.rpow_rpow_inv (norm_nonneg _) hp2.ne']
  have ha0 : a ≠ 0 := by
    rw [← norm_pos_iff, hna]
    positivity
  have ha1 : ‖a‖ ≤ 1 := by
    rw [hna]
    exact Real.rpow_le_one_of_one_le_of_nonpos hp1.le (by simp [hp1.le])
  obtain ⟨xO, hx, hu⟩ := existsUnique_ext Z x
  refine (abs_log_grNorm_sub_le Z.t _ ha0 ha1 (latDR_subset_latHT E H _ Z.t _ p _) (fun v hv => ?_) _ _).trans_eq ?_
  · rw [← hx] at hv ⊢
    exact hB E H _ Z.t p ℂ_[p] hn xO (fun xO' h' => hu xO' (h'.trans hx)) v hv a hna.le
  · rw [hna, Real.log_inv, Real.log_rpow (by positivity)]
    ring

theorem abs_lnStep_sub_le (hB : HTBoundSt) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (p : ℕ) [hp : Fact p.Prime]
    (x : Sp ℂ_[p] ⟶ Z.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left))
    (τ : E →+* ℂ) (k : ℕ) :
    |lnStep Z.t x u p true (.inl (τ, k)) - lnStep Z.t x u p false (.inl (τ, k))| ≤
      Real.log p / ((p : ℝ) - 1) + vDiff E p * Real.log p := by
  have hv : 0 ≤ vDiff E p * Real.log p := mul_nonneg (by unfold vDiff; positivity) (Real.log_natCast_nonneg p)
  have hL : 0 ≤ Real.log p / ((p : ℝ) - 1) := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    exact div_nonneg (Real.log_natCast_nonneg p) (by linarith)
  by_cases h : k < Dw.mult τ
  · have hs := abs_log_grNorm_DR_HT_le hB Z p x (u τ) ⟨k, h⟩
    rw [mul_one_div, abs_sub_comm] at hs
    have e : lnStep Z.t x u p true (.inl (τ, k)) - lnStep Z.t x u p false (.inl (τ, k)) =
        (Real.log (grNorm Z.t x (latHT Z.t p x) (u τ) ⟨k, h⟩) - Real.log (grNorm Z.t x (latDR Z.t x) (u τ) ⟨k, h⟩)) -
          (if τ (H.rt : E) = H.rt0 then vDiff E p * Real.log p else 0) := by
      simp only [lnStep, dif_pos h, lat, true_and, Bool.false_eq_true, false_and, if_false]
      ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have : |(if τ (H.rt : E) = H.rt0 then vDiff E p * Real.log p else 0)| ≤ vDiff E p * Real.log p := by
      split_ifs
      · rw [abs_of_nonneg hv]
      · simpa using hv
    linarith
  · simp only [lnStep, dif_neg h, sub_self, abs_zero]
    linarith

end Step

end GlobalTheory.LgDiff

namespace GlobalTheory.LgDiff

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Z : Model Xo c (algebraMap (𝓞 c.F) c.F)}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem abs_lgOf_detSym_sub_le_gen (hB : HTBoundSt) (τ : E →+* ℂ) (T : Finset ℕ) (v : HeightOneSpectrum (𝓞 F))
    (ε : Ext v) (y : AlgPt Y.Y) (hp : (resP v).Prime) :
    |lgOf Y (detSym Dw (ArIn.ind T) none τ) v ε y - lgOf Y (detSym Dw (fun _ => false) none τ) v ε y| ≤
      if resP v ∈ T then |Real.log (ε.w (resP v)) / Real.log (resP v)| *
        (((Dw.p + Dw.q : ℕ) : ℝ) * (Real.log (resP v) / ((resP v : ℝ) - 1) + vDiff E (resP v) * Real.log (resP v)))
      else 0 := by
  haveI := Fact.mk hp
  simp only [lgOf, dif_pos hp]
  rewrite [expo_detSym Dw (ArIn.ind T) (fun _ => false), add_sub_add_left_eq_sub, ← mul_sub, abs_mul, sum_detSym,
    sum_detSym, ← Finset.sum_sub_distrib]
  dsimp only
  split_ifs with hT
  · have hb : ArIn.ind T (resP v) = true := by simp [ArIn.ind, hT]
    have hc : |-Real.log (ε.w (resP v)) / Real.log (resP v)| = |Real.log (ε.w (resP v)) / Real.log (resP v)| := by
      rw [neg_div, abs_neg]
    rewrite [hc, hb]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => Real.log (resP v) / ((resP v : ℝ) - 1) +
      vDiff E (resP v) * Real.log (resP v)) fun i _ => ?_).trans_eq ?_
    · split_ifs
      · exact abs_lnStep_sub_le hB _ _ _ _ _ _
      · rw [neg_sub_neg, abs_sub_comm]
        exact abs_lnStep_sub_le hB _ _ _ _ _ _
    · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · have hb : ArIn.ind T (resP v) = false := by simp [ArIn.ind, hT]
    rewrite [hb]
    simp

end Gen

end GlobalTheory.LgDiff

namespace GlobalTheory.LgDiff

theorem abs_lgOf_detSym_sub_le : HTBoundSt → ∀ {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}
    {s : FinalTheorems S κ} (fl : s.Flag) (k : s.Comp) (τ : D.host.E →+* ℂ) (T : Finset ℕ)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ε : Ext v) (y : AlgPt (fl.C k).Y),
    |lgOf (fl.C k) (detSym S.Dw (ArIn.ind T) none τ) v ε y -
        lgOf (fl.C k) (detSym S.Dw (fun _ => false) none τ) v ε y| ≤
      if resP v ∈ T then |Real.log (ε.w (resP v)) / Real.log (resP v)| *
        (N * (Real.log (resP v) / ((resP v : ℝ) - 1) + vDiff D.host.E (resP v) * Real.log (resP v))) else 0 := by
  intro hB D A N j S κ s fl k τ T v ε y
  have hN : ((S.Dw.p + S.Dw.q : ℕ) : ℝ) = N := by exact_mod_cast S.rank_eq
  by_cases hp : (resP v).Prime
  · have h := abs_lgOf_detSym_sub_le_gen (fl.C k) hB τ T v ε y hp
    rw [hN] at h
    exact h
  have hL0 : 0 ≤ Real.log (resP v) / ((resP v : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos (resP v) with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ resP v := by exact_mod_cast h
      exact div_nonneg (Real.log_natCast_nonneg _) (by linarith)
  have hL1 : 0 ≤ vDiff D.host.E (resP v) * Real.log (resP v) :=
    mul_nonneg (by unfold vDiff; positivity) (Real.log_natCast_nonneg _)
  simp only [lgOf, dif_neg hp, sub_self, abs_zero]
  split_ifs
  · exact mul_nonneg (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (add_nonneg hL0 hL1))
  · exact le_rfl

end GlobalTheory.LgDiff

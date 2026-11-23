import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRatSecOfPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopOfInduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BijectiveCompAlgebraMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistIsModelNefFib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsElementHeightDifference
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricShiftElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfInducedOfInduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MSmoothAndSemiPosIff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions GlobalTheory.CompHt GlobalTheory.TrueGeo.IndScale
open scoped ENNReal

namespace GlobalTheory.CovHt.HodgeCount

theorem ofReal_le_of_forall_lt {T : ℝ} {V : ℝ≥0∞} (h : ∀ r < T, ENNReal.ofReal r ≤ V) : ENNReal.ofReal T ≤ V :=
  le_of_tendsto ((ENNReal.continuous_ofReal.tendsto T).mono_left (nhdsWithin_le_nhds (s := Set.Iio T)))
    (eventually_nhdsWithin_of_forall h)

theorem le_countVol {D d a q : ℕ} (hd : 0 < d) (ha : 0 < a) (hq : 0 < q) (m : ℕ → ℕ∞) (s : ℝ)
    (h : (s : EReal) ≤ limsup (fun τ : ℕ => ENNReal.log (m (a * (q * τ)) : ENNReal) *
      ((((D + 1).factorial : ℝ) / (τ : ℝ) ^ (D + 1) : ℝ) : EReal)) atTop) :
    ENNReal.ofReal (s / ((a * q : ℕ) : ℝ) ^ (D + 1) / d / ((D : ℝ) + 1)) ≤ countVol D d a m := by
  have hc : (0 : ℝ) < ((a * q : ℕ) : ℝ) ^ (D + 1) * d * ((D : ℝ) + 1) := by positivity
  rw [div_div, div_div, ← mul_assoc]
  refine ofReal_le_of_forall_lt fun r hr => ?_
  rw [lt_div_iff₀ hc] at hr
  have h₁ := frequently_lt_of_lt_limsup (h := (EReal.coe_lt_coe_iff.2 hr).trans_le h)
  have ht : Tendsto (fun τ : ℕ => q * τ) atTop atTop := tendsto_id.const_mul_atTop' hq
  refine le_limsup_of_frequently_le (ht.frequently ((h₁.and_eventually (eventually_gt_atTop 0)).mono ?_))
  rintro τ ⟨h₂, hτ⟩
  have hf : (0 : ℝ) < ((D + 1).factorial : ℝ) / (τ : ℝ) ^ (D + 1) := by positivity
  have h₃ : ENNReal.ofReal (r * (((a * q : ℕ) : ℝ) ^ (D + 1) * d * ((D : ℝ) + 1)) /
      (((D + 1).factorial : ℝ) / (τ : ℝ) ^ (D + 1))) ≤ logCard (m (a * (q * τ))) := by
    unfold logCard
    generalize ENNReal.log (m (a * (q * τ)) : ENNReal) = y at h₂
    induction y with
    | bot => rw [EReal.bot_mul_coe_of_pos hf] at h₂; exact absurd h₂ not_lt_bot
    | top => simp
    | coe y =>
      rw [← EReal.coe_mul, EReal.coe_lt_coe_iff] at h₂
      rw [EReal.real_coe_toENNReal]
      exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hf).2 h₂.le)
  refine le_trans ?_ (ENNReal.div_le_div_right (mul_le_mul_right h₃ _) _)
  have hp : (0 : ℝ) < (d : ℝ) * ((a * (q * τ) : ℕ) : ℝ) ^ (D + 1) := by positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast d, ← ENNReal.ofReal_natCast (a * (q * τ)),
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_div_of_pos hp]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {A : Adl C Y}

theorem induced_scale {M : TrueGeo.Model Y} {L : HermLB M.p} {k : ℕ+} {cf : HeightOneSpectrum (𝓞 F) → ℝ} {b : F}
    (hb' : b ≠ 0) (t : (𝓞 F →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ)
    (htb : ∀ σ : F →+* ℂ, t (σ.comp (algebraMap (𝓞 F) F)) = Real.log ‖σ b‖) (hI : A.Induced M L k cf) :
    A.Induced M (L.shift t ht) k (fun v => cf v +
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v b) / (((k : ℕ) : ℝ) * (A.n : ℕ))) := by
  obtain ⟨hfin, r, hr, hinf, hv⟩ := hI
  have hu (x : Y.X) := unitAt_constFn Y.str x hb'
  let c : Y.Fnˣ := Units.mk0 (Cartier.constFn Y.str b) (hu (genericPoint Y.X)).ne_zero
  have hc : (c : Y.Fn) = Cartier.constFn Y.str b := rfl
  refine ⟨?_, fun i => r i * c, ⟨hr.isLB, (hr.add_principal c).isRatSec, fun i x hx => ?_⟩, ?_, ?_⟩
  · refine (hfin.union (sum_log_embedding_add_finsum_log_adicAbv_eq_zero F _ hb').1).subset fun v h => ?_
    by_contra h'
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h'
    exact h (by simp only [h'.1, h'.2, zero_div, add_zero])
  · refine (hr.isEqn i x hx).iff_unitAt.2 ?_
    rw [Units.val_mul, mul_div_cancel_left₀ _ (r i).ne_zero]
    exact hu x
  · intro σ y y' i f hy hi hf
    have h₁ : RegAt (under y) (f * (r i : Y.Fn)) := (hr.isEqn i _ hi).regularAt_iff.1 hf
    have h₂ : 0 < ‖σ b‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hb')
    refine (hinf σ y y' i f hy hi hf).trans ?_
    change _ = ‖ratVal (f * ((r i : Y.Fn) * (c : Y.Fn))) y‖ ^ 2 *
      Real.exp (-((L.φ _).φ (i PUnit.unit) y' + 2 * t (σ.comp (algebraMap (𝓞 F) F))))
    rw [htb, ← mul_assoc, hc, ratVal_mul h₁ (hu _).regAt, ratVal_constFn, norm_mul, neg_add, Real.exp_add,
      Real.exp_neg (2 * _), show (2 : ℝ) * Real.log ‖σ b‖ =
        Real.log (‖σ b‖ ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (pow_pos h₂ 2)]
    field_simp
  · intro v e y yt i h hi
    have h₁ : below y.1 ∈ (L.B.pull M.j).U i := OfModel.le_chart M L.B e y yt h hi trivial
    have h₂ : UnitAt (below y.1) (((eqn A.D (below y.1))⁻¹ ^ (k : ℕ) * r i : Y.Fnˣ) : Y.Fn) := by
      have := ((A.D.exists_isEqn (below y.1)).choose_spec.nsmul k).iff_unitAt.1 (hr.isEqn i _ h₁)
      rwa [div_eq_inv_mul, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← inv_pow] at this
    have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
    have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
    refine (hv v e y yt i h hi).trans ?_
    rw [← mul_assoc, Units.val_mul _ c, hc, OfModel.valAt_mul _ h₂.regAt (hu _).regAt,
      valAt_constFn Y.str _ y.1 y.2, map_mul, e.w_alg,
      Real.log_mul (e.w.ne_zero (valAt_ne_zero _ h₂)) (AbsoluteValue.ne_zero _ hb')]
    field_simp
    ring

theorem exists_induced_zero {M : TrueGeo.Model Y} {L : HermLB M.p} {k : ℕ+} {cf : HeightOneSpectrum (𝓞 F) → ℝ}
    (hI : A.Induced M L k cf) (hq : ∀ v, ∃ r : ℚ, cf v = r * Real.log (Ideal.absNorm v.asIdeal : ℝ)) (a : ℕ+) :
    ∃ (N : TrueGeo.Model Y) (L' : HermLB N.p) (q : ℕ+), Geo.Tor.IsNormalScheme N.X ∧ A.Induced N L' (a * q) 0 := by
  obtain ⟨N, π, -, hN, hπ, -, hj, -⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y M M
  obtain ⟨h, b, b', hb, hb', e⟩ := GlobalTheory.exists_mul_eq_log_adicAbv_sub F
    (fun v => ((k : ℕ) : ℝ) * a * (A.n : ℕ) * cf v) (hI.1.subset fun v hv h0 => hv (by simp [h0])) fun v => by
      obtain ⟨r, hr⟩ := hq v
      refine ⟨r.den, (k : ℕ) * (a : ℕ) * (A.n : ℕ) * r.num, r.den_pos, ?_⟩
      have : (r : ℝ) * r.den = r.num := by exact_mod_cast r.mul_den_eq_num
      rw [hr]
      push_cast
      rw [← this]
      ring
  have h₁ := InducedPow.induced_pow F C Y A N _ k (a * h) cf (InducedPull.induced_pull F C Y A M N π hπ hj L k cf hI)
  have hne : ∀ x : 𝓞 F, x ≠ 0 → algebraMap (𝓞 F) F x ≠ 0 := fun x hx =>
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 hx
  have h₂ := induced_scale (div_ne_zero (hne b' hb') (hne b hb)) (fun σ => Real.log ‖σ b'‖ - Real.log ‖σ b‖)
    (fun σ => by simp) (fun σ => by
      rw [map_div₀, norm_div, Real.log_div (norm_ne_zero_iff.2 ((map_ne_zero σ).2 (hne b' hb')))
        (norm_ne_zero_iff.2 ((map_ne_zero σ).2 (hne b hb)))]
      rfl) h₁
  rw [mul_left_comm] at h₂
  refine ⟨N, _, k * h, hN, (congrArg (A.Induced N _ _) (funext fun v => ?_)).mpr h₂⟩
  have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
  have ha : ((a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast a.ne_zero
  have hh : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
  rw [map_div₀, Real.log_div (AbsoluteValue.ne_zero _ (hne b' hb')) (AbsoluteValue.ne_zero _ (hne b hb)),
    ← neg_sub, ← e v]
  simp only [PNat.mul_coe, Nat.cast_mul, Pi.zero_apply]
  field_simp
  ring

theorem le_countVol_of_induced (hV : GlobalTheory.Published.VolGe) (hC : GlobalTheory.Published.ArCalc) (hD : GlobalTheory.Published.ArDegree)
    (hP : A.SemiPos) (hF : A.NefFib) {M : TrueGeo.Model Y} {L : HermLB M.p} {a q : ℕ+} (hN : Geo.Tor.IsNormalScheme M.X)
    (hI : A.Induced M L (a * q) 0) : ENNReal.ofReal (A.arTop / ((Y.dim : ℝ) + 1)) ≤
      countVol Y.dim (Module.finrank ℚ F) a fun τ => (A.small τ).encard := by
  haveI := M.ar.isIntegral
  obtain ⟨s, hs⟩ : ∃ s, L.IsSelfInter s := by
    obtain ⟨h, hh⟩ := (hC.arExists _ M.X M.p _ M.ar).1 L
    exact ⟨_, h, hh, rfl⟩
  have h₁ := hV _ M.X M.p Y.dim M.ar L s (NefFibUniq.nefFib_of_induced F C Y A M L _ _ hI hF)
    ((InducedSemiPos.mSmooth_and_semiPos_iff F C Y A M L _ _ hI).2.1 hP) hs
  have h₂ := (arTop_of_induced hC hD F C Y A M L _ _ hI).2 s hs
  have h₃ := le_countVol (D := Y.dim) (Module.finrank_pos (R := ℚ) (M := F)) a.pos (q * A.n).pos
    (fun τ => (A.small τ).encard) s (h₁.trans_eq (congrArg (limsup · atTop) (funext fun τ => ?_)))
  · rw [h₂]
    refine le_of_eq_of_le (congrArg _ ?_) h₃
    simp [mul_assoc]
  · obtain ⟨e⟩ := SmallSec.small_equiv_smallSec F C Y A M L _ hI hN τ
    rw [← Set.encard_congr e]
    congr 5
    simp only [PNat.mul_coe]
    ring

theorem small_twist_subset {δ : HeightOneSpectrum (𝓞 F) → ℝ} (hδ : ∀ v, 0 ≤ δ v) (τ : ℕ) :
    (A.twist 0 (-δ)).small τ ⊆ A.small τ := by
  rintro f ⟨h₁, h₂, h₃⟩
  refine ⟨h₁, fun σ y => ?_, fun v e y => le_trans ?_ (h₃ v e y)⟩
  · simpa only [Adl.nrmInf, Adl.twist, add_zero] using h₂ σ y
  · simp only [Adl.nrmFin, Adl.twist, Pi.neg_apply]
    have := hδ v
    gcongr
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (A.n : ℕ)) this]

theorem exists_rat_approx {c : HeightOneSpectrum (𝓞 F) → ℝ} (hc : (Function.support c).Finite) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : HeightOneSpectrum (𝓞 F) → ℝ, (Function.support δ).Finite ∧ (∀ v, 0 ≤ δ v) ∧ ∑ᶠ v, δ v ≤ ε ∧
      ∀ v, ∃ r : ℚ, (c + -δ) v = r * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  classical
  set η := ε / (hc.toFinset.card + 1) with hη
  have hη0 : 0 < η := by positivity
  have key : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : ℝ, 0 ≤ x ∧ x ≤ η ∧ (c v = 0 → x = 0) ∧
      ∃ r : ℚ, c v + -x = r * Real.log (Ideal.absNorm v.asIdeal : ℝ) := fun v => by
    by_cases h : c v = 0
    · exact ⟨0, le_rfl, hη0.le, fun _ => rfl, 0, by simp [h]⟩
    have hl : 0 < Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
      Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)
    obtain ⟨r, h₁, h₂⟩ := exists_rat_btwn (div_lt_div_of_pos_right (sub_lt_self (c v) hη0) hl)
    rw [div_lt_iff₀ hl] at h₁
    rw [lt_div_iff₀ hl] at h₂
    exact ⟨c v - r * Real.log (Ideal.absNorm v.asIdeal : ℝ), by linarith, by linarith, fun h' => absurd h' h, r, by ring⟩
  choose δ h₀ h₁ h₂ h₃ using key
  have hs : Function.support δ ⊆ hc.toFinset := fun v hv => by
    simpa using fun h => hv (h₂ v h)
  refine ⟨δ, (Finset.finite_toSet _).subset hs, h₀, ?_, h₃⟩
  rw [finsum_eq_sum_of_support_subset _ hs]
  refine (Finset.sum_le_card_nsmul _ _ _ fun v _ => h₁ v).trans ?_
  rw [nsmul_eq_mul, hη, mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

theorem arTop_twist (hC : GlobalTheory.Published.ArCalc) (hD : GlobalTheory.Published.ArDegree) (hF : A.NefFib) (ci : InfinitePlace F → ℝ)
    {cf : HeightOneSpectrum (𝓞 F) → ℝ} (hc : (Function.support cf).Finite) :
    (A.twist ci cf).arTop = A.arTop + ((Y.dim : ℝ) + 1) * A.deg *
      ((∑ v : InfinitePlace F, (v.mult : ℝ) * ci v) + ∑ᶠ v, cf v) / (Module.finrank ℚ F : ℝ) := by
  obtain ⟨M, L, k, c, hI, -⟩ := id hF
  obtain ⟨M', L', k', c', s, hI', hs, e⟩ :=
    GlobalTheory.TwistTop.isArTop_twist hC hD F C Y A _ ci cf hc (arTop_of_induced hC hD F C Y A M L k c hI).1
  exact ((arTop_of_induced hC hD F C Y _ M' L' k' c' hI').2 s hs).trans e.symm

theorem arTop_le_countVol (hV : GlobalTheory.Published.VolGe) (hC : GlobalTheory.Published.ArCalc) (hD : GlobalTheory.Published.ArDegree)
    (hP : A.SemiPos) (hF : A.NefFib) (a : ℕ+) : ENNReal.ofReal (A.arTop / ((Y.dim : ℝ) + 1)) ≤
      countVol Y.dim (Module.finrank ℚ F) a fun τ => (A.small τ).encard := by
  refine ofReal_le_of_forall_lt fun r hr => ?_
  obtain ⟨M, L, k, c, hI, -⟩ := id hF
  have hd : (1 : ℝ) ≤ (Module.finrank ℚ F : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  have hε : 0 < (A.arTop / ((Y.dim : ℝ) + 1) - r) / (|A.deg| + 1) := div_pos (sub_pos.2 hr) (by positivity)
  obtain ⟨δ, hδ, h₀, h₁, h₂⟩ := exists_rat_approx hI.1 hε
  have hδ' : (Function.support (-δ)).Finite := by rwa [Function.support_neg]
  obtain ⟨N, L', q, hN, hI'⟩ := exists_induced_zero (hI.twist_fin hδ') h₂ a
  have h₃ := le_countVol_of_induced hV hC hD (A := A.twist 0 (-δ)) hP
    ((GlobalTheory.TwistModel.twist_isModel_nefFib F C Y A 0 (-δ) hδ').2 hF) hN hI'
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (h₃.trans (countVol_mono _ _ _ fun τ => Set.encard_le_encard (small_twist_subset h₀ τ)))
  rw [arTop_twist hC hD hF 0 hδ']
  have h₄ : 0 ≤ ∑ᶠ v, δ v := finsum_nonneg h₀
  have e : ∑ᶠ v, (-δ) v = -∑ᶠ v, δ v := finsum_neg_distrib δ
  rw [le_div_iff₀ (by positivity)] at h₁
  have h₅ : A.deg * ((∑ᶠ v, δ v) / (Module.finrank ℚ F : ℝ)) ≤ (∑ᶠ v, δ v) * (|A.deg| + 1) := by
    calc _ ≤ (|A.deg| + 1) * ((∑ᶠ v, δ v) / (Module.finrank ℚ F : ℝ)) := by
          gcongr; linarith [le_abs_self A.deg]
      _ ≤ (|A.deg| + 1) * ∑ᶠ v, δ v := by gcongr; exact div_le_self h₄ hd
      _ = _ := mul_comm _ _
  have e₂ : (A.arTop + ((Y.dim : ℝ) + 1) * A.deg * ((∑ v : InfinitePlace F, (v.mult : ℝ) * (0 : InfinitePlace F → ℝ) v) +
      ∑ᶠ v, (-δ) v) / (Module.finrank ℚ F : ℝ)) / ((Y.dim : ℝ) + 1) =
      A.arTop / ((Y.dim : ℝ) + 1) - A.deg * ((∑ᶠ v, δ v) / (Module.finrank ℚ F : ℝ)) := by
    rw [e]
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
    field_simp
    ring
  rw [e₂]
  linarith

theorem twist_le_countVol : GlobalTheory.Published.VolGe → GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree →
    ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (M : Adl C Y), M.SemiPos → M.NefFib →
    ∀ (t : ℝ) (cf : HeightOneSpectrum (𝓞 F) → ℝ), (Function.support cf).Finite → ∀ a : ℕ, 0 < a →
      ENNReal.ofReal (M.arTop / ((Y.dim : ℝ) + 1) + M.deg * (t + (∑ᶠ v, cf v) / (Module.finrank ℚ F : ℝ))) ≤
        countVol Y.dim (Module.finrank ℚ F) a fun τ => ((M.twist (fun _ => t) cf).small τ).encard := by
  intro hV hC hD F _ _ C Y M hP hF t cf hc a ha
  refine le_of_eq_of_le (congrArg _ ?_) (arTop_le_countVol hV hC hD (A := M.twist (fun _ => t) cf) hP
    ((GlobalTheory.TwistModel.twist_isModel_nefFib F C Y M _ cf hc).2 hF) ⟨a, ha⟩)
  have hd : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hm : ∑ v : InfinitePlace F, (v.mult : ℝ) = Module.finrank ℚ F := by exact_mod_cast InfinitePlace.sum_mult_eq
  rw [arTop_twist hC hD hF _ hc, ← Finset.sum_mul, hm]
  field_simp

end GlobalTheory.CovHt.HodgeCount

end

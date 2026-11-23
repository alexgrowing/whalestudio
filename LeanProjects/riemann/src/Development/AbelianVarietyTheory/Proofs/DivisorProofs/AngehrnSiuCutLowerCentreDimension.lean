import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorNonKltPointsNumericallyMultipleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalLogCanonicalThresholdAtPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonKltLocusDimLtAfterPerturbation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleAddNefIsAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulIntersectionLeOfNefClassOnClosed
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefLineBundleNumericalTheoremsProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtAddSmulOfLcAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberCurveOfClassEqSmulAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultNsmulOfQadd
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem exists_nat_div_of_nonneg (q : ℚ) (hq : 0 ≤ q) : ∃ a b : ℕ, 0 < b ∧ q = a / b := by
  refine ⟨q.num.toNat, q.den, q.den_pos, ?_⟩
  have h1 : ((q.num.toNat : ℕ) : ℚ) = q.num := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hq)
  rw [h1]
  exact (Rat.num_div_den q).symm

theorem exists_qWeil_eq_comb (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp ℂ) (hp : IsProjOver p) (D E : CartierDiv X) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hD : D.Eff) (hE : E.Eff) (s t : ℚ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    letI := algebraΓOfHom p
    ∃ (F : CartierDiv X) (M : ℕ), 0 < M ∧ F.Eff ∧ s • qWeil D m + t • qWeil E k = qWeil F M ∧
      ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB F] : ℚ) / M =
        s * ((interNumRed ℂ C ![toLB D] : ℚ) / m) + t * ((interNumRed ℂ C ![toLB E] : ℚ) / k) := by
  letI := algebraΓOfHom p
  obtain ⟨a, b, hb, rfl⟩ := exists_nat_div_of_nonneg s hs
  obtain ⟨a', b', hb', rfl⟩ := exists_nat_div_of_nonneg t ht
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
  have hb0' : (b' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hb'.ne'
  refine ⟨(a * b' * k) • D + (a' * b * m) • E, b * b' * m * k,
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hb hb') hm) hk,
    (eff_nsmul_of_qadd hD _).add (eff_nsmul_of_qadd hE _), ?_, ?_⟩
  · funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, qWeil, CartierDiv.mult_add,
      mult_nsmul_of_qadd]
    push_cast
    field_simp
  · intro C hC
    have e := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (toLB ((a * b' * k) • D + (a' * b * m) • E))
      (toLB D) (toLB E) (isLB_toLB _) (isLB_toLB D) (isLB_toLB E) (a * b' * k) (a' * b * m) C hC
      (by rw [← toPic_apply, ← toPic_apply, ← toPic_apply, map_add, map_nsmul, map_nsmul])
    rw [e]
    push_cast
    field_simp

theorem logCanonicalCut_lowers_centre_dimension : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (r : ℕ) (N₀ : LB X) (hN₀ : N₀.IsLB) (A F : CartierDiv X) (a : ℕ)
      (x z : X) (e : ℕ) (c' : ℝ) (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → 0 < r → IsNef ℂ N₀ →
      IsAmpleLB (toLB A) → 0 < a → toPic F = a • cls N₀ hN₀ →
      IsClosed ({x} : Set X) → z ⤳ x → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e →
      (z = genericPoint X ∨ IsNkltCentre p n (Δ + qWeil D₀ m') z) → 0 < c' →
      c' ^ e < (interNumRed ℂ (Closeds.closure ({z} : Set X)) (fun _ : Fin e => N₀) : ℝ) / (r : ℝ) ^ e →
      0 < m' → D₀.Eff → 0 < μ → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' = lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) → LcAt p n (Δ + qWeil D₀ m') x →
      ∃ (lam' μ' : ℚ) (m'' : ℕ) (D₁ : CartierDiv X), 0 < m'' ∧ D₁.Eff ∧ 0 < μ' ∧ (lam' : ℝ) < lam + e / c' ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₁] : ℚ) / m'' = lam' * interNumRed ℂ C ![N₀] / r - μ' * interNumRed ℂ C ![toLB A]) ∧ LcCut p n (Δ + qWeil D₁ m'') x (e - 1) := by
  intro hPr X _ _ _ p n hp hn
  intro Δ m G r N₀ hN₀ A F a x z e c' lam μ m' D₀ hΔ hklt hm hG hr hNnef hA ha hF hx hzx he hdim
    hcen hc' hv hm' hD₀ hμ hcurve hlc
  letI := algebraΓOfHom p

  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hre : (0 : ℝ) < (r : ℝ) ^ e := pow_pos hr0 e
  have hc'e : (0 : ℝ) < c' ^ e := pow_pos hc' e
  have hIr : c' ^ e * (r : ℝ) ^ e <
      ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℝ) := by
    rwa [lt_div_iff₀ hre] at hv
  have hIpos : (0 : ℝ) <
      ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℝ) :=
    lt_trans (mul_pos hc'e hre) hIr
  have he0 : e ≠ 0 := by omega
  have hee : (0 : ℝ) < (e : ℝ) ^ e := pow_pos (by exact_mod_cast (show 0 < e by omega)) e

  obtain ⟨κ, hκ0, hκc, hκI⟩ : ∃ κ : ℚ, (0 : ℝ) < κ ∧ (κ : ℝ) < e / c' ∧
      (e : ℝ) ^ e * (r : ℝ) ^ e < (κ : ℝ) ^ e *
        ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℝ) := by
    set I : ℝ := ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℝ)
      with hIdef
    have hx0 : 0 ≤ (e : ℝ) ^ e * (r : ℝ) ^ e / I := by positivity
    have hy0 : 0 ≤ ((e : ℝ) ^ e * (r : ℝ) ^ e / I) ^ ((e : ℝ)⁻¹) := Real.rpow_nonneg hx0 _
    have hye : (((e : ℝ) ^ e * (r : ℝ) ^ e / I) ^ ((e : ℝ)⁻¹)) ^ e = (e : ℝ) ^ e * (r : ℝ) ^ e / I :=
      Real.rpow_inv_natCast_pow hx0 he0
    have hyc : ((e : ℝ) ^ e * (r : ℝ) ^ e / I) ^ ((e : ℝ)⁻¹) < e / c' := by
      by_contra hcon
      push_neg at hcon
      have h1 := pow_le_pow_left₀ (by positivity) hcon e
      rw [hye, div_pow, div_le_div_iff₀ hc'e hIpos] at h1
      nlinarith [mul_lt_mul_of_pos_left hIr hee]
    obtain ⟨κ, hyκ, hκc⟩ := exists_rat_btwn hyc
    refine ⟨κ, lt_of_le_of_lt hy0 hyκ, hκc, ?_⟩
    have h2 := pow_lt_pow_left₀ hyκ hy0 he0
    rw [hye, div_lt_iff₀ hIpos] at h2
    exact h2
  have hκq : (0 : ℚ) < κ := by exact_mod_cast hκ0
  have hκIq : (e : ℚ) ^ e * (r : ℚ) ^ e < κ ^ e *
      ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℚ) := by
    exact_mod_cast hκI

  have hrq : (0 : ℚ) < r := by exact_mod_cast hr
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  obtain ⟨s, hs⟩ := exists_nat_gt (2 * κ / (μ * a * r))
  have hsq : (0 : ℚ) < s := lt_trans (by positivity) hs
  have hs0 : 0 < s := by exact_mod_cast hsq
  set h : ℚ := κ / ((s : ℚ) * a * r) with hhdef
  have hh : 0 < h := by positivity
  have hhμ : h < μ / 2 := by
    rw [hhdef, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hs
    nlinarith

  set A' : CartierDiv X := s • F + A with hA'def
  have hclsA' : cls (toLB A') (isLB_toLB A') = (s * a) • cls N₀ hN₀ + 1 • cls (toLB A) (isLB_toLB A) := by
    rw [← toPic_apply, ← toPic_apply, hA'def, map_add, map_nsmul, hF, one_nsmul, smul_smul]
  have hA'amp : IsAmpleLB (toLB A') := by
    refine isAmpleLB_of_cls_eq_ample_add_nef ℂ X p hp (toLB A) (lbPow N₀ (s * a)) (toLB A') hA
      (hNnef.pow hA (s * a)) (isLB_toLB A') ?_
    rw [cls_lbPow hN₀, hclsA', one_nsmul, add_comm]

  have hmix := mixExp_interNumRed nefNumerics_outright ℂ X p hp N₀ (toLB A) (toLB A') hN₀
    (isLB_toLB A) (isLB_toLB A') (s * a) 1 (Closeds.closure {z}) e hNnef (IsAmpleLB.isNef (k := ℂ) hA)
    hclsA' (by rw [Closeds.coe_closure]; exact hdim)
  have hmixQ : ((s : ℚ) * a) ^ e *
      ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℚ) ≤
      ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => toLB A' : ℤ) : ℚ) := by
    exact_mod_cast hmix
  have hcard : (({x} : Finset X).card : ℚ) * (e : ℚ) ^ e < h ^ e *
      ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => toLB A' : ℤ) : ℚ) := by
    rw [Finset.card_singleton, Nat.cast_one, one_mul]
    have hhs : h * ((s : ℚ) * a) = κ / r := by
      rw [hhdef]; field_simp
    calc (e : ℚ) ^ e < (κ / r) ^ e *
          ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℚ) := by
          rw [div_pow, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
          exact hκIq
      _ = h ^ e * (((s : ℚ) * a) ^ e *
          ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℚ)) := by
          rw [← mul_assoc, ← mul_pow, hhs]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmixQ (by positivity)

  have hDq : IsQCart (qWeil D₀ m') := ⟨m', D₀, hm', hD₀, rfl⟩
  obtain ⟨B, δ₀, hδ₀, -, hBnum, hOff, hnk, hsep⟩ := GlobalTheory.T.exists_divisor_nonKlt_points_numerically_multiple hPr X p n hp hn Δ m G A'
    (qWeil D₀ m') {x} z e h hΔ hklt hm hG hA'amp hDq
    (fun y hy => by rw [Finset.mem_singleton] at hy; subst hy; exact ⟨hx, hzx⟩) he hdim hcen hh hcard

  obtain ⟨ε, hε0, hεb⟩ := exists_rat_btwn (show (0 : ℝ) < ((e : ℝ) / c' - κ) / (|(lam : ℝ)| + 1) from
    div_pos (by linarith) (by positivity))
  set δ : ℚ := min (min δ₀ (1 / 2)) ε with hδdef
  have hδ0 : 0 < δ := lt_min (lt_min hδ₀ (by norm_num)) (by exact_mod_cast hε0)
  have hδε : δ ≤ ε := min_le_right _ _
  have hδh : δ ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδδ₀ : δ ≤ δ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := by linarith
  have hδlam : (δ : ℝ) * |(lam : ℝ)| < e / c' - κ := by
    have h1 : (δ : ℝ) ≤ ε := by exact_mod_cast hδε
    have h2 := (lt_div_iff₀ (by positivity : (0 : ℝ) < |(lam : ℝ)| + 1)).1 hεb
    nlinarith [abs_nonneg (lam : ℝ)]

  have hxk : KltAt p n Δ x := hklt x
  have hk1 : KltAt p n (Δ + (1 - δ) • qWeil D₀ m') x :=
    kltAt_add_smul_of_lcAt X p n hp hn Δ (qWeil D₀ m') δ x hDq hxk hlc hδ0 hδ1
  have hnk1 := hnk δ hδ0.le hδδ₀ x (Finset.mem_singleton_self x)
  have hsDq : IsQCart ((1 - δ) • qWeil D₀ m') := by
    obtain ⟨F₁, M₁, hM₁, hF₁, heq, -⟩ := exists_qWeil_eq_comb X p hp D₀ D₀ m' m' hm' hm' hD₀ hD₀
      (1 - δ) 0 (by linarith) le_rfl
    exact ⟨M₁, F₁, hM₁, hF₁, by rw [← heq, zero_smul, add_zero]⟩
  have hBq : IsQCart B := hBnum.isQCart
  obtain ⟨c, hc0, hc1, hlcc, hnkc⟩ := GlobalTheory.T.exists_rational_logCanonicalThreshold_at_point hPr X p n hp hn Δ m G ((1 - δ) • qWeil D₀ m') B x
    hm hG hsDq hBq hk1 hnk1
  have hcut := logCanonicalCut_of_step X p n hp hn Δ (qWeil D₀ m') B δ c x z (e - 1) hxk hDq hBq hlc hδ0 hδ1
    hc1 hOff hsep (by rw [Nat.sub_add_cancel he]; exact hdim) hlcc hnkc

  obtain ⟨m₁, B₀, hm₁, hB₀, rfl, hBn⟩ := hBnum
  obtain ⟨D₂, m'', hm'', hD₂, heq, hnum⟩ := exists_qWeil_eq_comb X p hp D₀ B₀ m' m₁ hm' hm₁ hD₀ hB₀
    (1 - δ) c (by linarith) hc0.le
  refine ⟨(1 - δ) * lam + c * κ, (1 - δ) * μ - c * h, m'', D₂, hm'', hD₂, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · have t1 : -((δ : ℝ) * lam) ≤ δ * |(lam : ℝ)| := by
      rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs _) (by exact_mod_cast hδ0.le)
    have t2 : (c : ℝ) * κ ≤ κ := by
      have : (c : ℝ) ≤ 1 := by exact_mod_cast hc1
      nlinarith
    push_cast
    nlinarith
  · intro C hC
    have eA' := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (toLB A') N₀ (toLB A) (isLB_toLB A') hN₀
      (isLB_toLB A) (s * a) 1 C hC hclsA'
    rw [hnum C hC, hcurve C hC, hBn C hC, eA']
    have hr0' : (r : ℚ) ≠ 0 := hrq.ne'
    have hs0' : (s : ℚ) ≠ 0 := hsq.ne'
    have ha0' : (a : ℚ) ≠ 0 := haq.ne'
    rw [hhdef]
    push_cast
    field_simp
    ring
  · rw [← heq, ← add_assoc]
    exact hcut

end GlobalTheory.PairStep

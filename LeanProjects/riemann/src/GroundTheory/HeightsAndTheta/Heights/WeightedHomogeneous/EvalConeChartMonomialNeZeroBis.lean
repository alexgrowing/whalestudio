import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace MonomialMapNorm

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem evalCone_mul (z : Cone n ℂ) (f f' : MvPolynomial (Coord n) ℤ) :
    evalCone z (f * f') = evalCone z f * evalCone z f' := by
  simp only [evalCone, eval₂_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem evalCone_pow (z : Cone n ℂ) (f : MvPolynomial (Coord n) ℤ) (m : ℕ) :
    evalCone z (f ^ m) = evalCone z f ^ m := by
  simp only [evalCone, eval₂_pow]

omit [DecidableEq ι] in

theorem evalCone_chartMonomial_ne_zero {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)}
    (hcz : ∀ k, z k (c k) ≠ 0) (d : ι → ℕ) : evalCone z (chartMonomial c d) ≠ 0 := by
  simp only [chartMonomial, evalCone, eval₂_prod, eval₂_pow, eval₂_X]
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hcz k)

variable (P : ArithVariety n)

omit [Fintype ι] in

theorem isLive_of_point {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)}
    (hcz : ∀ k, z k (c k) ≠ 0) : P.IsLive c := fun k hk ↦
  hcz k (by simpa only [evalCone, eval₂_X] using hz.2 _ hk)

omit [Fintype ι] in
theorem mkF_X_ne_zero {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (k : ι) :
    P.mkF (X ⟨k, c k⟩) ≠ 0 := fun h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)

theorem chartPow_ne_zero {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (a : ι → ℤ) :
    P.chartPow c a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (mkF_X_ne_zero P hc k)

theorem chartPow_add {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (a b : ι → ℤ) :
    P.chartPow c (a + b) = P.chartPow c a * P.chartPow c b := by
  rw [ArithVariety.chartPow, ArithVariety.chartPow, ArithVariety.chartPow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ ↦ by rw [Pi.add_apply, zpow_add₀ (mkF_X_ne_zero P hc k)]

theorem form_div_mem {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) {e : MvPolynomial (Coord n) ℤ}
    {δ : ι → ℕ} (he : IsWeightedHomogeneous (coordDeg n) e δ) :
    P.mkF e / P.chartPow c (fun k ↦ (δ k : ℤ)) ∈ P.chartRing c := by
  have h := P.chart_homogeneous c hc he
  have hne : (∏ k, P.mkF (X ⟨k, c k⟩) ^ δ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (mkF_X_ne_zero P hc k)
  have hp : P.chartPow c (fun k ↦ (δ k : ℤ)) = ∏ k, P.mkF (X ⟨k, c k⟩) ^ δ k := by
    simp only [ArithVariety.chartPow, zpow_natCast]
  rw [hp, ← h, mul_div_cancel_left₀ _ hne]
  exact eval₂_mem (fun i _ ↦ by rw [eq_intCast]; exact intCast_mem _ _)
    fun v ↦ Subring.subset_closure ⟨v, rfl⟩

theorem mkF_chartForm {a : ι → ℤ} (s : IntegralSection P a) {c : (k : ι) → Fin (n k + 1)} {d : ι → ℕ}
    {e : MvPolynomial (Coord n) ℤ} (he : IsChartForm P a s.num s.den c d e) :
    P.mkF e = s.toFun * P.mkF (chartMonomial c d) := by
  have h1 := (P.mkF_eq_zero_iff _).mpr he.2
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h1
  have hden : P.mkF s.den ≠ 0 := fun h ↦ s.den_not_mem ((P.mkF_eq_zero_iff _).mp h)
  rw [IntegralSection.toFun, div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination h1

theorem toFun_div_chartPow_mem {a : ι → ℤ} (s : IntegralSection P a) {c : (k : ι) → Fin (n k + 1)}
    (hc : P.IsLive c) : s.toFun / P.chartPow c a ∈ P.chartRing c := by
  obtain ⟨d, e, ⟨δ, he, hδ⟩, hmem⟩ := s.regular c hc
  have hmk := mkF_chartForm P s ⟨⟨δ, he, hδ⟩, hmem⟩
  have hM : P.mkF (chartMonomial c d) = P.chartPow c (fun k ↦ (d k : ℤ)) := by
    simp only [chartMonomial, map_prod, map_pow, ArithVariety.chartPow, zpow_natCast]
  have hδ' : (fun k ↦ (δ k : ℤ)) = a + fun k ↦ (d k : ℤ) := funext fun k ↦ hδ k
  have key : s.toFun / P.chartPow c a = P.mkF e / P.chartPow c (fun k ↦ (δ k : ℤ)) := by
    rw [hδ', chartPow_add P hc, hmk, hM, mul_div_mul_right _ _ (chartPow_ne_zero P hc _)]
  rw [key]
  exact form_div_mem P hc he

omit [Fintype ι] in
theorem isOfDegree_mul {a b : ι → ℤ} {x y : P.FunField} (hx : P.IsOfDegree a x) (hy : P.IsOfDegree b y) :
    P.IsOfDegree (a + b) (x * y) := by
  obtain ⟨f, g, δf, δg, hf, hg, hδ, hgP, rfl⟩ := hx
  obtain ⟨f', g', δf', δg', hf', hg', hδ', hgP', rfl⟩ := hy
  refine ⟨f * f', g * g', δf + δf', δg + δg', hf.mul hf', hg.mul hg', fun k ↦ ?_,
    fun h ↦ (P.isPrime.mem_or_mem h).elim hgP hgP', ?_⟩
  · simp only [Pi.add_apply, Nat.cast_add]
    linear_combination hδ k + hδ' k
  · rw [map_mul, map_mul, div_mul_div_comm]

theorem isOfDegree_toFun {a : ι → ℤ} (s : IntegralSection P a) : P.IsOfDegree a s.toFun :=
  ⟨s.num, s.den, s.numDeg, s.denDeg, s.num_isHomogeneous, s.den_isHomogeneous, s.deg_eq, s.den_not_mem, rfl⟩

theorem toFun_pow {a : ι → ℤ} (s : IntegralSection P a) (m : ℕ) : (s.pow m).toFun = s.toFun ^ m := by
  simp only [IntegralSection.toFun, IntegralSection.pow, map_pow, div_pow]

theorem toFun_mul {a b : ι → ℤ} (s : IntegralSection P a) (t : IntegralSection P b) :
    (s.mul t).toFun = s.toFun * t.toFun := by
  simp only [IntegralSection.toFun, IntegralSection.mul, map_mul, div_mul_div_comm]

theorem isNormalSection_mul {a b : ι → ℤ} {s : P.FunField} (hs : P.IsNormalSection a s)
    (u : IntegralSection P b) : P.IsNormalSection (a + b) (s * u.toFun) :=
  ⟨isOfDegree_mul P hs.degree (isOfDegree_toFun P u), fun c hc ↦ by
    rw [chartPow_add P hc, mul_div_mul_comm]
    exact Subalgebra.mul_mem _ (hs.integral c hc)
      ((integralClosure (P.chartRing c) P.FunField).algebraMap_mem
        (⟨_, toFun_div_chartPow_mem P u hc⟩ : P.chartRing c))⟩

theorem chartForm_bound {A : HermLine n} {s : IntegralSection P A.deg} (hs : s.SupNormLE A 0)
    {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)} {d : ι → ℕ}
    {e : MvPolynomial (Coord n) ℤ} (he : IsChartForm P A.deg s.num s.den c d e) (hcz : ∀ k, z k (c k) ≠ 0) :
    ‖evalCone z e‖ ≤ ‖evalCone z (chartMonomial c d)‖ * A.metric z := by
  have h := hs z hz c d e he hcz
  rwa [Real.exp_zero, div_le_one (mul_pos (norm_pos_iff.mpr (evalCone_chartMonomial_ne_zero hcz d))
    (A.metric_pos z hz.1))] at h

theorem isSmallFor_mul {L : HermLine n} {q m r : ℕ} (hrq : r < q) {g : IntegralSection P L.deg}
    {h : IntegralSection P (HermLine.standard n).deg} (hgs : g.SupNormLE L 0)
    (hhs : h.SupNormLE (HermLine.standard n) 0) {s : P.FunField} (hsS : P.IsSmallFor (L.pow (q * m + r)) s) :
    P.IsSmallFor (((L.pow q).mul (HermLine.standard n)).pow (m + 1))
      (s * g.toFun ^ (q - r) * h.toFun ^ (m + 1)) := by
  intro p₀ q₀ δp δq hp hq hδ hrep z hz
  obtain ⟨c, hcz⟩ : ∃ c : (k : ι) → Fin (n k + 1), ∀ k, z k (c k) ≠ 0 := by
    choose c hc using fun k ↦ Function.ne_iff.mp (hz.1 k)
    exact ⟨c, hc⟩
  have hc := isLive_of_point P hz hcz
  obtain ⟨dg, eg, ⟨δg, heg, hδg⟩, hmg⟩ := g.regular c hc
  obtain ⟨dh, eh, ⟨δh, heh, hδh⟩, hmh⟩ := h.regular c hc
  have hfg : IsChartForm P L.deg g.num g.den c dg eg := ⟨⟨δg, heg, hδg⟩, hmg⟩
  have hfh : IsChartForm P (HermLine.standard n).deg h.num h.den c dh eh := ⟨⟨δh, heh, hδh⟩, hmh⟩
  have bg := chartForm_bound P hgs hz hfg hcz
  have bh := chartForm_bound P hhs hz hfh hcz
  have hrepr : P.mkF (p₀ * chartMonomial c dg ^ (q - r) * chartMonomial c dh ^ (m + 1)) =
      s * P.mkF (q₀ * eg ^ (q - r) * eh ^ (m + 1)) := by
    simp only [map_mul, map_pow, mkF_chartForm P g hfg, mkF_chartForm P h hfh, hrep]
    ring
  have hdeg : ∀ k, (((δp + (q - r) • dg + (m + 1) • dh) k : ℕ) : ℤ) =
      ((δq + (q - r) • δg + (m + 1) • δh) k : ℕ) + (L.pow (q * m + r)).deg k := by
    intro k
    have e1 := hδ k
    have e2 := hδg k
    have e3 := hδh k
    simp only [HermLine.pow, HermLine.mul, HermLine.standard, Pi.add_apply, Pi.smul_apply] at e1 e2 e3 ⊢
    simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one] at e1 e2 e3 ⊢
    push_cast [Nat.cast_sub hrq.le] at e1 e2 e3 ⊢
    linear_combination e1 - ((q : ℤ) - r) * e2 - ((m : ℤ) + 1) * e3
  have hb := hsS _ _ _ _
    ((hp.mul ((isWeightedHomogeneous_chartMonomial c dg).pow (q - r))).mul
      ((isWeightedHomogeneous_chartMonomial c dh).pow (m + 1)))
    ((hq.mul (heg.pow (q - r))).mul (heh.pow (m + 1))) hdeg hrepr z hz
  have hLm : (L.pow (q * m + r)).metric z = L.metric z ^ (q * m + r) := rfl
  rw [hLm] at hb
  simp only [evalCone_mul, evalCone_pow, norm_mul, norm_pow] at hb
  change ‖evalCone z p₀‖ ≤ ‖evalCone z q₀‖ * (L.metric z ^ q * (HermLine.standard n).metric z) ^ (m + 1)
  have hA : 0 < ‖evalCone z (chartMonomial c dg)‖ := norm_pos_iff.mpr (evalCone_chartMonomial_ne_zero hcz dg)
  have hB : 0 < ‖evalCone z (chartMonomial c dh)‖ := norm_pos_iff.mpr (evalCone_chartMonomial_ne_zero hcz dh)
  have hl : 0 < L.metric z := L.metric_pos z hz.1
  have hH : 0 < (HermLine.standard n).metric z := (HermLine.standard n).metric_pos z hz.1
  set A := ‖evalCone z (chartMonomial c dg)‖
  set B := ‖evalCone z (chartMonomial c dh)‖
  set l := L.metric z
  set H := (HermLine.standard n).metric z
  have hexp : q - r + (q * m + r) = q * (m + 1) := by
    zify [hrq.le]
    ring
  have key : A ^ (q - r) * B ^ (m + 1) * ‖evalCone z p₀‖ ≤
      A ^ (q - r) * B ^ (m + 1) * (‖evalCone z q₀‖ * (l ^ q * H) ^ (m + 1)) := by
    calc A ^ (q - r) * B ^ (m + 1) * ‖evalCone z p₀‖ = ‖evalCone z p₀‖ * A ^ (q - r) * B ^ (m + 1) := by ring
      _ ≤ ‖evalCone z q₀‖ * ‖evalCone z eg‖ ^ (q - r) * ‖evalCone z eh‖ ^ (m + 1) * l ^ (q * m + r) := hb
      _ ≤ ‖evalCone z q₀‖ * (A * l) ^ (q - r) * (B * H) ^ (m + 1) * l ^ (q * m + r) := by gcongr
      _ = A ^ (q - r) * B ^ (m + 1) * (‖evalCone z q₀‖ * (l ^ q * H) ^ (m + 1)) := by
        rw [mul_pow (l ^ q), ← pow_mul, ← hexp, pow_add l (q - r)]
        ring
  exact le_of_mul_le_mul_left key (by positivity)

end MonomialMapNorm

theorem MonomialMapNorm.proof : MonomialMapNorm.Statement := by
  intro ι _ _ n P L _ q m r hrq g h hg0 hgs hh0 hhs
  refine ⟨fun s hsN hsS ↦ ⟨?_, MonomialMapNorm.isSmallFor_mul P hrq hgs hhs hsS⟩, fun s₁ s₂ e ↦ ?_⟩
  · have hdeg : (((L.pow q).mul (HermLine.standard n)).pow (m + 1)).deg =
        (L.pow (q * m + r)).deg + ((q - r) • L.deg + (m + 1) • (HermLine.standard n).deg) := by
      funext k
      simp only [HermLine.pow, HermLine.mul, Pi.add_apply, Pi.smul_apply]
      simp only [nsmul_eq_mul]
      push_cast [Nat.cast_sub hrq.le]
      ring
    rw [hdeg]
    simpa only [MonomialMapNorm.toFun_mul, MonomialMapNorm.toFun_pow, mul_assoc] using
      MonomialMapNorm.isNormalSection_mul P hsN ((g.pow (q - r)).mul (h.pow (m + 1)))
  · have hu : g.toFun ^ (q - r) * h.toFun ^ (m + 1) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hg0) (pow_ne_zero _ hh0)
    simp only [mul_assoc] at e
    exact mul_right_cancel₀ hu e

end

end GroundTheory.Heights₂.Heights

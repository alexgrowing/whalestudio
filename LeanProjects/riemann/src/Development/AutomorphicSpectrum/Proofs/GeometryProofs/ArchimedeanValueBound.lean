import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero
import Development.WeilBound.CoreStatements.HodgeTatePoints.GfForms

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ArchBd

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
open GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def chartVec {F : Type} [Field F] (x : (Σ k, ι k) → F) (c : ∀ k, ι k) : (Σ k, ι k) → F :=
  fun p => x p * (x ⟨p.1, c p.1⟩)⁻¹

theorem prod_pow_single [DecidableEq K] {F : Type} [CommMonoid F] (Y : K → F) (j : K) :
    ∏ k, Y k ^ (Pi.single j 1 : K → ℕ) k = Y j := by
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

theorem exists_form {F₁ F₂ : Type} [Field F₁] [Field F₂] (y₁ : (Σ k, ι k) → F₁) (y₂ : (Σ k, ι k) → F₂)
    (c : ∀ k, ι k) (h₁ : ∀ k, y₁ ⟨k, c k⟩ ≠ 0) (h₂ : ∀ k, y₂ ⟨k, c k⟩ ≠ 0) (f : MRing ι) :
    ∃ (d : K → ℕ) (G : MRing ι), IsMultiHomog G d ∧
      aeval y₁ G = aeval (chartVec y₁ c) f * ∏ k, y₁ ⟨k, c k⟩ ^ d k ∧
      aeval y₂ G = aeval (chartVec y₂ c) f * ∏ k, y₂ ⟨k, c k⟩ ^ d k := by
  classical
  induction f using MvPolynomial.induction_on with
  | C n => exact ⟨0, C n, homog_C n, by simp, by simp⟩
  | add f g hf hg =>
    obtain ⟨df, Gf, hGf, a₁, a₂⟩ := hf
    obtain ⟨dg, Gg, hGg, b₁, b₂⟩ := hg
    refine ⟨df + dg, Gf * PositivityTheory.HtPt.Gf.mon c dg + Gg * PositivityTheory.HtPt.Gf.mon c df,
      homog_add (homog_mul hGf (PositivityTheory.HtPt.Gf.hom_mon c dg))
        (by rw [add_comm df dg]; exact homog_mul hGg (PositivityTheory.HtPt.Gf.hom_mon c df)), ?_, ?_⟩
    · simp only [map_add, map_mul, PositivityTheory.HtPt.Gf.aeval_mon, a₁, b₁, Pi.add_apply, pow_add,
        Finset.prod_mul_distrib]
      ring
    · simp only [map_add, map_mul, PositivityTheory.HtPt.Gf.aeval_mon, a₂, b₂, Pi.add_apply, pow_add,
        Finset.prod_mul_distrib]
      ring
  | mul_X f p hf =>
    obtain ⟨df, Gf, hGf, a₁, a₂⟩ := hf
    refine ⟨df + Pi.single p.1 1, Gf * X p, homog_mul hGf (homog_X p), ?_, ?_⟩
    · simp only [map_mul, aeval_X, a₁, Pi.add_apply, pow_add, Finset.prod_mul_distrib, prod_pow_single,
        chartVec]
      field_simp [h₁ p.1]
    · simp only [map_mul, aeval_X, a₂, Pi.add_apply, pow_add, Finset.prod_mul_distrib, prod_pow_single,
        chartVec]
      field_simp [h₂ p.1]

theorem aeval_chart_eq_zero {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (c : ∀ k, ι k)
    (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) (hP : ∀ f ∈ mCoordIdeal y, aeval z f = 0)
    (f : MRing ι) (h : aeval (chartVec y c) f = 0) : aeval (chartVec z c) f = 0 := by
  obtain ⟨d, G, hG, e₁, e₂⟩ := exists_form y z c hy hz f
  have h0 : aeval z G = 0 := hP G (mem_of_aeval_eq_zero hG (by rw [e₁, h, zero_mul]))
  rw [e₂] at h0
  exact (mul_eq_zero.1 h0).resolve_right (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k))

theorem exists_bound (f : MRing ι) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : (Σ k, ι k) → ℂ, (∀ p, ‖w p‖ ≤ 1) → ‖aeval w f‖ ≤ B := by
  induction f using MvPolynomial.induction_on with
  | C n => exact ⟨|(n : ℝ)|, abs_nonneg _, fun w _ => by simp⟩
  | add f g hf hg =>
    obtain ⟨B₁, p₁, h₁⟩ := hf
    obtain ⟨B₂, p₂, h₂⟩ := hg
    refine ⟨B₁ + B₂, add_nonneg p₁ p₂, fun w hw => ?_⟩
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (h₁ w hw) (h₂ w hw))
  | mul_X f p hf =>
    obtain ⟨B, p₀, h⟩ := hf
    refine ⟨B, p₀, fun w hw => ?_⟩
    rw [map_mul, aeval_X, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hw p)).trans (h w hw)

theorem eval₂_div_eq_zero {S R T : Type} [CommRing S] [CommRing R] [Field T] (α : S →+* R) (β : S →+* T)
    (hk : ∀ f, α f = 0 → β f = 0) (P : Polynomial S) (t : R) (r s : S) (ht : P.eval₂ α t = 0)
    (hts : α s * t = α r) (hs : β s ≠ 0) : P.eval₂ β (β r / β s) = 0 := by
  have h1 : (Polynomial.scaleRoots P s).eval₂ α (α r) = 0 := by
    rw [← hts, Polynomial.scaleRoots_eval₂_mul, ht, mul_zero]
  rw [Polynomial.eval₂_at_apply] at h1
  have h2 := hk _ h1
  rw [← Polynomial.eval₂_at_apply, show β r = β s * (β r / β s) by field_simp,
    Polynomial.scaleRoots_eval₂_mul] at h2
  exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero _ hs)

theorem norm_root_le (p : Polynomial ℂ) (hp : p.Monic) (W : ℂ) (hW : p.eval W = 0) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ i, ‖p.coeff i‖ ≤ B) : ‖W‖ ≤ 1 + B := by
  have h1 := Polynomial.IsRoot.norm_lt_cauchyBound hp.ne_zero hW
  have h2 : p.cauchyBound ≤ B.toNNReal + 1 := by
    rw [Polynomial.cauchyBound, hp.leadingCoeff, nnnorm_one, div_one]
    refine add_le_add (Finset.sup_le fun i _ => ?_) le_rfl
    exact NNReal.le_toNNReal_of_coe_le (hB i)
  have h3 : (‖W‖₊ : ℝ) ≤ ((B.toNNReal + 1 : NNReal) : ℝ) := by
    exact_mod_cast h1.le.trans h2
  simpa [add_comm, Real.coe_toNNReal _ hB0] using h3

theorem exists_monic {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {t : Ω}
    (ht : t ∈ integralClosure (chartRingZ y c) Ω) :
    ∃ Q : Polynomial (MRing ι), Q.Monic ∧
      Q.eval₂ (aeval (chartVec y c) : MRing ι →ₐ[ℤ] Ω).toRingHom t = 0 := by
  obtain ⟨p, hp, hpt⟩ := ht
  have hv : chartVec y c = fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩ := by
    funext q
    simp [chartVec, div_eq_mul_inv]
  let π : MRing ι →ₐ[ℤ] chartRingZ y c :=
    aeval fun q => ⟨chartVec y c q, Algebra.subset_adjoin ⟨q, by rw [hv]⟩⟩
  have hπ : ∀ f, ((π f : chartRingZ y c) : Ω) = aeval (chartVec y c) f := by
    intro f
    have : (chartRingZ y c).val.comp π = aeval (chartVec y c) := by
      apply MvPolynomial.algHom_ext
      intro q
      simp [π]
    rw [← this]
    rfl
  have hs : Function.Surjective π.toRingHom := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ (aeval (chartVec y c) : MRing ι →ₐ[ℤ] Ω).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval, hv]
      exact hx
    obtain ⟨f, hf⟩ := hx'
    exact ⟨f, Subtype.ext ((hπ f).trans hf)⟩
  obtain ⟨Q, hmap, -, hQ⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts p).2 (Polynomial.map_surjective _ hs p)) hp
  refine ⟨Q, hQ, ?_⟩
  rw [← hmap, Polynomial.eval₂_map] at hpt
  have hc : (algebraMap (chartRingZ y c) Ω).comp π.toRingHom =
      (aeval (chartVec y c) : MRing ι →ₐ[ℤ] Ω).toRingHom := RingHom.ext hπ
  rwa [hc] at hpt

theorem chart_ratio {F : Type} [Field F] (x : (Σ k, ι k) → F) (c : ∀ k, ι k) (hx : ∀ k, x ⟨k, c k⟩ ≠ 0)
    (a : K → ℤ) (dg dh : K → ℕ) (g h : MRing ι) (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh)
    (hd : ∀ k, (dg k : ℤ) = dh k + a k) (s : F) (e : aeval x g = s * aeval x h) :
    aeval (chartVec x c) g = s * (∏ k, x ⟨k, c k⟩ ^ (-a k)) * aeval (chartVec x c) h := by
  have e₁ : aeval (chartVec x c) g = aeval x g * ∏ k, (x ⟨k, c k⟩)⁻¹ ^ dg k :=
    aeval_scaled_homog x (fun k => (x ⟨k, c k⟩)⁻¹) hg
  have e₂ : aeval (chartVec x c) h = aeval x h * ∏ k, (x ⟨k, c k⟩)⁻¹ ^ dh k :=
    aeval_scaled_homog x (fun k => (x ⟨k, c k⟩)⁻¹) hh
  have e₃ := zpow_factor_inv (a := dg) (b := dh) (fun k => x ⟨k, c k⟩) hx
  simp only [hd, add_sub_cancel_left] at e₃
  rw [e₁, e₂, e, ← e₃]
  ring

theorem prod_zpow_mul {F : Type} [Field F] (Y : K → F) (a : K → ℤ) (q : ℕ) :
    ∏ k, Y k ^ (-((q : ℤ) * a k)) = (∏ k, Y k ^ (-a k)) ^ q := by
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  ring

theorem chart_bound {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q m : ℕ) (u : Ω) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hI : (m : Ω) * u ^ q * ∏ k, y ⟨k, c k⟩ ^ (-((q : ℤ) * a k)) ∈ integralClosure (chartRingZ y c) Ω) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, z ⟨k, c k⟩ ≠ 0) → (∀ p, ‖z p‖ ≤ ‖z ⟨p.1, c p.1⟩‖) →
      (∀ f ∈ mCoordIdeal y, aeval z f = 0) → ∀ val : ℂ, HasVal y a u z val →
        ‖(m : ℂ) * val ^ q * ∏ k, z ⟨k, c k⟩ ^ (-((q : ℤ) * a k))‖ ≤ B := by
  obtain ⟨Q, hQ, hQt⟩ := exists_monic y c hI
  choose Bf hB0 hB using fun i => exists_bound (ι := ι) (Q.coeff i)
  have hT0 : 0 ≤ ∑ i ∈ Finset.range (Q.natDegree + 1), Bf i := Finset.sum_nonneg fun i _ => hB0 i
  refine ⟨1 + ∑ i ∈ Finset.range (Q.natDegree + 1), Bf i, by linarith, ?_⟩
  intro z hz hmax hP val hv
  obtain ⟨dg, dh, g, h, hg, hh, hd, e₁, hz0, e₂⟩ := hv
  have ry := chart_ratio y c hc a dg dh g h hg hh hd u e₁
  have rz := chart_ratio z c hz a dg dh g h hg hh hd val e₂
  let α : MRing ι →+* Ω := (aeval (chartVec y c) : MRing ι →ₐ[ℤ] Ω).toRingHom
  let β : MRing ι →+* ℂ := (aeval (chartVec z c) : MRing ι →ₐ[ℤ] ℂ).toRingHom
  have hα : ∀ f, α f = aeval (chartVec y c) f := fun _ => rfl
  have hβ : ∀ f, β f = aeval (chartVec z c) f := fun _ => rfl
  have hh0 : β h ≠ 0 := by
    have e : aeval (chartVec z c) h = aeval z h * ∏ k, (z ⟨k, c k⟩)⁻¹ ^ dh k :=
      aeval_scaled_homog z (fun k => (z ⟨k, c k⟩)⁻¹) hh
    rw [hβ, e]
    exact mul_ne_zero hz0 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (hz k)))
  have hroot := eval₂_div_eq_zero α β
    (fun f hf => aeval_chart_eq_zero y z c hc hz hP f hf) Q _ ((m : MRing ι) * g ^ q) (h ^ q) hQt
    (by
      rw [prod_zpow_mul (fun k => y ⟨k, c k⟩)]
      simp only [map_mul, map_pow, map_natCast, hα, ry]
      ring)
    (by rw [map_pow]; exact pow_ne_zero _ hh0)
  have hW : β ((m : MRing ι) * g ^ q) / β (h ^ q) = (m : ℂ) * val ^ q * ∏ k, z ⟨k, c k⟩ ^ (-((q : ℤ) * a k)) := by
    rw [prod_zpow_mul (fun k => z ⟨k, c k⟩)]
    simp only [map_mul, map_pow, map_natCast]
    rw [hβ g, rz, ← hβ h, div_eq_iff (pow_ne_zero _ hh0)]
    ring
  rw [hW] at hroot
  have hw1 : ∀ p, ‖chartVec z c p‖ ≤ 1 := by
    intro p
    have : ‖z ⟨p.1, c p.1⟩‖ ≠ 0 := norm_ne_zero_iff.2 (hz p.1)
    rw [chartVec, norm_mul, norm_inv, ← div_eq_mul_inv]
    exact div_le_one_of_le₀ (hmax p) (norm_nonneg _)
  refine norm_root_le (Q.map β) (hQ.map β) _ (by rwa [Polynomial.eval_map]) _ hT0 fun i => ?_
  rw [Polynomial.coeff_map]
  by_cases hi : i ∈ Finset.range (Q.natDegree + 1)
  · exact (hB i _ hw1).trans (Finset.single_le_sum (fun j _ => hB0 j) hi)
  · have : Q.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hi)
    rw [this, map_zero, norm_zero]
    exact hT0

theorem exists_lower (A : HermLine ι) (hA : IsSmoothHerm A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : (Σ k, ι k) → ℂ, (∀ p, ‖w p‖ ≤ 1) → (∀ k, ∃ i, ‖w ⟨k, i⟩‖ = 1) → δ ≤ A.h w := by
  let S : Set ((Σ k, ι k) → ℂ) := {w | (∀ p, ‖w p‖ ≤ 1) ∧ ∀ k, ∃ i, ‖w ⟨k, i⟩‖ = 1}
  have hcl : IsClosed S := by
    have e : S = (⋂ p, {w : (Σ k, ι k) → ℂ | ‖w p‖ ≤ 1}) ∩ ⋂ k, ⋃ i, {w | ‖w ⟨k, i⟩‖ = 1} := by
      ext w
      simp [S]
    rw [e]
    refine IsClosed.inter (isClosed_iInter fun p => isClosed_le (by fun_prop) continuous_const)
      (isClosed_iInter fun k => isClosed_iUnion_of_finite fun i => isClosed_eq (by fun_prop) continuous_const)
  have hS : IsCompact S := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : (Σ k, ι k) → ℂ) 1) hcl fun w hw => ?_
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    exact hw.1
  have hne : ∀ w ∈ S, ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := by
    intro w hw k
    obtain ⟨i, hi⟩ := hw.2 k
    refine ⟨i, fun h0 => ?_⟩
    simp [h0] at hi
  have hcont : ContinuousOn A.h S := hA.continuousOn.mono fun w hw => hne w hw
  by_cases hS0 : S.Nonempty
  · obtain ⟨w₀, hw₀, hmin⟩ := hS.exists_isMinOn hS0 hcont
    exact ⟨A.h w₀, A.pos w₀ (hne w₀ hw₀), fun w h₁ h₂ => hmin ⟨h₁, h₂⟩⟩
  · exact ⟨1, one_pos, fun w h₁ h₂ => absurd ⟨w, h₁, h₂⟩ hS0⟩

theorem section_bound : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ (A : HermLine ι) (q m : ℕ) (u : Ω), IsSmoothHerm A → 0 < q → 0 < m → (m : Ω) * u ^ q ∈ chartLatNm y A.a q → ∃ C : ℝ, ∀ z ∈ ptsOver ℂ (mCoordIdeal y), ∀ val : ℂ, HasVal y A.a u z val → ‖val‖ ≤ Real.exp C * A.h z := by
  intro K _ ι _ Ω _ y d _ _ A q m u hA hq hm hu
  obtain ⟨δ, hδ, hlow⟩ := exists_lower A hA
  have hc : ∀ c : ∀ k, ι k, ∃ B : ℝ, 0 ≤ B ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) →
      ∀ z : (Σ k, ι k) → ℂ, (∀ k, z ⟨k, c k⟩ ≠ 0) → (∀ p, ‖z p‖ ≤ ‖z ⟨p.1, c p.1⟩‖) →
      (∀ f ∈ mCoordIdeal y, aeval z f = 0) → ∀ val : ℂ, HasVal y A.a u z val →
        ‖(m : ℂ) * val ^ q * ∏ k, z ⟨k, c k⟩ ^ (-((q : ℤ) * A.a k))‖ ≤ B) := by
    intro c
    by_cases h : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨B, h0, hB⟩ := chart_bound y A.a q m u c h (hu c h)
      exact ⟨B, h0, fun _ => hB⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' h⟩
  choose B hB0 hB using hc
  obtain ⟨M, hM⟩ := (Set.finite_range B).bddAbove
  have hM' : ∀ c, B c ≤ 1 + |M| := fun c =>
    (hM ⟨c, rfl⟩).trans ((le_abs_self M).trans (by linarith))
  have hpos : 0 < 1 + |M| := by positivity
  refine ⟨Real.log ((1 + |M|) / δ), fun z hz val hv => ?_⟩
  rw [Real.exp_log (div_pos hpos hδ)]
  have hmax : ∀ k, ∃ i, (∀ j, ‖z ⟨k, j⟩‖ ≤ ‖z ⟨k, i⟩‖) ∧ z ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i₀, hi₀⟩ := hz.1 k
    haveI : Nonempty (ι k) := ⟨i₀⟩
    obtain ⟨i, hi⟩ := Finite.exists_max fun j => ‖z ⟨k, j⟩‖
    refine ⟨i, hi, fun h0 => hi₀ ?_⟩
    have := hi i₀
    simpa [h0] using this
  choose c hcm hc0 using hmax
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    have hX : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0]
      simp
    have := hz.2 _ hX
    rw [aeval_X] at this
    exact hc0 k this
  have hb := hB c hy z hc0 (fun p => hcm p.1 p.2) hz.2 val hv
  let τ : K → ℂ := fun k => (z ⟨k, c k⟩)⁻¹
  have hτ : ∀ k, τ k ≠ 0 := fun k => inv_ne_zero (hc0 k)
  have hsm := A.smul τ z hτ
  set e : ℝ := ∏ k, ‖τ k‖ ^ A.a k with he
  have hepos : 0 < e := Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hτ k)) _
  have hlo : δ ≤ e * A.h z := by
    rw [← hsm]
    refine hlow _ (fun p => ?_) fun k => ⟨c k, ?_⟩
    · have h0 : ‖z ⟨p.1, c p.1⟩‖ ≠ 0 := norm_ne_zero_iff.2 (hc0 p.1)
      simp only [τ, norm_mul, norm_inv]
      rw [inv_mul_le_iff₀ (norm_pos_iff.2 (hc0 p.1)), mul_one]
      exact hcm p.1 p.2
    · simp only [τ, norm_mul, norm_inv]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.2 (hc0 k))
  have hE : ‖∏ k, z ⟨k, c k⟩ ^ (-((q : ℤ) * A.a k))‖ = e ^ q := by
    rw [prod_zpow_mul (fun k => z ⟨k, c k⟩), norm_pow, norm_prod, he]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [τ, norm_zpow, norm_inv, inv_zpow']
  have hb' : (m : ℝ) * (‖val‖ * e) ^ q ≤ 1 + |M| := by
    refine le_trans (le_of_eq ?_) (hb.trans (hM' c))
    rw [norm_mul, norm_mul, norm_pow, hE, Complex.norm_natCast, mul_pow]
    ring
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnn : 0 ≤ (‖val‖ * e) ^ q := by positivity
  have hb2 : (‖val‖ * e) ^ q ≤ (1 + |M|) ^ q := by
    have h1 : (1 : ℝ) ≤ 1 + |M| := by linarith [abs_nonneg M]
    calc (‖val‖ * e) ^ q ≤ (m : ℝ) * (‖val‖ * e) ^ q := le_mul_of_one_le_left hnn hm1
      _ ≤ 1 + |M| := hb'
      _ ≤ (1 + |M|) ^ q := le_self_pow₀ h1 hq.ne'
  have hb3 : ‖val‖ * e ≤ 1 + |M| :=
    (pow_le_pow_iff_left₀ (by positivity) hpos.le hq.ne').1 hb2
  have hAz : 0 < A.h z := A.pos z hz.1
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
  calc ‖val‖ * δ ≤ ‖val‖ * (e * A.h z) := mul_le_mul_of_nonneg_left hlo (norm_nonneg _)
    _ = (‖val‖ * e) * A.h z := by ring
    _ ≤ (1 + |M|) * A.h z := mul_le_mul_of_nonneg_right hb3 hAz.le

end GlobalTheory.CompanionTheory.Ar.ArchBd

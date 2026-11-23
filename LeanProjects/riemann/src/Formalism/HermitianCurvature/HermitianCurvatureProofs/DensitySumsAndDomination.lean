import Formalism.HermitianCurvature.StatementTC

open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexInnerProductSpace ComplexOrder ComplexConjugate
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.DensitySumsAndDomination

theorem psd_congr {α : Type} {Y : Finset α} {k k' : α → α → ℂ}
    (h : ∀ x ∈ Y, ∀ y ∈ Y, k x y = k' x y) (hk : TB.PSDOn Y k) : TB.PSDOn Y k' := by
  unfold TB.PSDOn at *
  have e : (Matrix.of fun x y : Y => k x y) = Matrix.of fun x y : Y => k' x y := by
    ext x y
    simp only [Matrix.of_apply]
    exact h x x.2 y y.2
  rwa [← e]

theorem psd_smul {α : Type} {Y : Finset α} {k : α → α → ℂ} (c : ℝ) (hc : 0 ≤ c) (h : TB.PSDOn Y k) :
    TB.PSDOn Y (fun x y => (c : ℂ) * k x y) := by
  unfold TB.PSDOn at *
  first
    | (have e : (Matrix.of fun x y : Y => (c : ℂ) * k x y) = c • Matrix.of fun x y : Y => k x y := by
         ext x y
         simp [Complex.real_smul]
       rw [e]
       exact h.smul hc)
    | (have e : (Matrix.of fun x y : Y => (c : ℂ) * k x y) = (c : ℂ) • Matrix.of fun x y : Y => k x y := by
         ext x y
         simp
       rw [e]
       exact h.smul (Complex.zero_le_real.mpr hc))

theorem domScaleTop : DomScaleTop := by
  intro E W _ D T Th lam hlam he hD
  have hKr : ∀ j x y, (scaleTop D lam).Kr j x y =
      if j = D.r + 1 then (lam : ℂ) * D.Kr j x y else D.Kr j x y := fun _ _ _ => rfl
  have he' : ∀ j, (scaleTop D lam).e j = if j = D.r + 1 then lam - 1 else D.e j := fun _ => rfl
  intro i s hs hsi hir
  obtain ⟨h1, h2, h3⟩ := hD i s hs hsi hir
  have hir' : i ≤ D.r + 1 := hir
  have hne : i - s ≠ D.r + 1 := by omega
  by_cases hi : i = D.r + 1
  · refine ⟨fun t ht => ?_, fun t ht t' ht' hl x hx y hy => ?_, fun S hS hSd => ?_⟩
    · refine psd_congr (k := fun h h' => (lam : ℂ) * (Th i s t h h' - TB.blk (D.Kr i) s t t h h'))
        (fun x _ y _ => ?_) (psd_smul lam hlam (h1 t ht))
      simp only [TB.blk, hKr, if_pos hi]
      ring
    · simp only [if_pos hi]
      rw [h2 t ht t' ht' hl x hx y hy]
    · refine psd_congr
        (k := fun h h' => (lam : ℂ) * ((1 + (D.e i : ℂ)) * D.Kr (i - s) h h' - ∑ t ∈ S, Th i s t h h'))
        (fun x _ y _ => ?_) (psd_smul lam hlam (h3 S hS hSd))
      have he2 : D.e i = 0 := by rw [hi]; exact he
      simp only [hKr, he', if_pos hi, if_neg hne]
      rw [he2, ← Finset.mul_sum]
      push_cast
      ring
  · refine ⟨fun t ht => ?_, fun t ht t' ht' hl x hx y hy => ?_, fun S hS hSd => ?_⟩
    · refine psd_congr (fun x _ y _ => ?_) (h1 t ht)
      simp only [TB.blk, hKr, if_neg hi]
    · simp only [if_neg hi]
      exact h2 t ht t' ht' hl x hx y hy
    · refine psd_congr (fun x _ y _ => ?_) (h3 S hS hSd)
      simp only [hKr, he', if_neg hi, if_neg hne]

theorem recHypScaleTop : RecHypScaleTop := by
  intro hDS hSB E W _ D C₁ C₄ Θ jn H _ _ Vt c c' sd hsd he h hc1 hc2 hc3
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := h
  have hl1 : (1 : ℝ) ≤ max sd 1 := le_max_right _ _
  have hl0 : (0 : ℝ) ≤ max sd 1 := by linarith
  refine ⟨⟨a1, a2, a3, a4, a5, ?_, a7, ?_, ?_, ?_, a11, a12, a13, a14, a15, a16, ?_, ?_⟩, rfl, rfl, ?_, ?_⟩
  · intro i Y
    by_cases hit : i = D.r + 1
    · refine psd_congr (fun x _ y _ => ?_) (psd_smul _ hl0 (a6 i Y))
      simp [scaleTop, hit]
    · refine psd_congr (fun x _ y _ => ?_) (a6 i Y)
      simp [scaleTop, hit]
  · intro i s hs hsi hi x y t t' hx hy ht ht' htt hne
    refine a8 i s hs hsi hi x y t t' hx hy ht ht' htt ?_
    intro h0
    apply hne
    show (if i = D.r + 1 then ((max sd 1 : ℝ) : ℂ) * D.Kr i (TB.join x s t) (TB.join y s t')
      else D.Kr i (TB.join x s t) (TB.join y s t')) = 0
    rw [h0]; simp
  · intro i h1 hi
    by_cases hit : i = D.r + 1
    · simp only [scaleTop, hit, if_true]
      constructor
      · linarith
      · have : max sd 1 ≤ 2 := max_le hsd (by norm_num)
        linarith
    · simp only [scaleTop, hit, if_false]
      exact a9 i h1 hi
  · intro T
    obtain ⟨Th, hTh⟩ := a10 T
    exact ⟨_, hDS E W D T Th _ hl0 he hTh⟩
  · intro Y hY
    filter_upwards [a17 Y hY] with ε hε p hp q hq hne
    refine hε p hp q hq ?_
    intro h0
    apply hne
    simp [scaleTop, h0]
  · refine ⟨hc1, fun Y hY R => ?_, hc3⟩
    refine psd_congr (fun x _ y _ => ?_) (hSB _ Y (D.Kr (D.r + 1))
      (fun p q => ∑ ρ ∈ R, c' ρ p * conj (c' ρ q)) sd (a6 _ Y) (hc2 Y hY R))
    simp [scaleTop]
  · simp [scaleTop]
  · intro i hi
    have : i ≠ D.r + 1 := by have := (Finset.mem_Icc.1 hi).2; omega
    simp [scaleTop, this]

theorem domAfterOfLocal : DomAfterOfLocal := by
  intro hP hS hM E W _ D h
  have key : ∀ T : TB.Tower E, ∃ Th, DomText D T Th := by
    intro T
    have h' : ∀ i s : ℕ, ∃ Th0 : E → TB.Pt E → TB.Pt E → ℂ, 1 ≤ s → s ≤ i → i ≤ D.r + 1 →
        (∀ t : E, TB.PSDOn (T.X (i - s)) (Th0 t)) ∧
        (∀ t : E, t ≠ 0 →
          TB.PSDOn (T.X (i - s)) (fun h h' => Th0 t h h' - TB.blk (D.Kr i) s t t h h')) ∧
        (∀ t t' : E, t - t' ∈ D.La (i - s + 1) s →
          ∀ h ∈ T.X (i - s), ∀ h' ∈ T.X (i - s), Th0 t h h' = Th0 t' h h') ∧
        (∀ S : Finset E, (∀ t ∈ S, ∀ t' ∈ S, t - t' ∈ D.La (i - s + 1) s → t = t') →
          TB.PSDOn (T.X (i - s))
            (fun h h' => (1 + (D.e i : ℂ)) * D.Kr (i - s) h h' - ∑ t ∈ S, Th0 t h h')) := by
      intro i s
      by_cases hr : 1 ≤ s ∧ s ≤ i ∧ i ≤ D.r + 1
      · obtain ⟨P, _, S, a, hok, hN, hB, hL⟩ := h T i s hr.1 hr.2.1 hr.2.2
        obtain ⟨_, _, o3, o4, o5, o6⟩ := hS _ _ a _ _ (hP _ _ _ S _ hok)
        have hL' : D.La (i - s + 1) s = (J.scaleSys a (J.prodSys S)).L := hL
        refine ⟨(J.scaleSys a (J.prodSys S)).Th, fun _ _ _ => ⟨o4, fun t ht => ?_, fun t t' htt => ?_,
          fun R hR => ?_⟩⟩
        · refine psd_congr (fun x hx y hy => ?_) (o5 t ht)
          rw [← hN t ht x hx y hy]; rfl
        · exact o3 t t' (hL' ▸ htt)
        · refine psd_congr (fun x hx y hy => ?_) (o6 R (fun t ht t' ht' htt => hR t ht t' ht' (hL' ▸ htt)))
          rw [← hB x hx y hy]; rfl
      · exact ⟨fun _ _ _ => 0, fun a b c => absurd ⟨a, b, c⟩ hr⟩
    choose Th0 hTh0 using h'
    exact ⟨fun i s => Th0 i s, fun i s hs hsi hi => hTh0 i s hs hsi hi⟩
  refine ⟨key, fun T => ?_⟩
  obtain ⟨Th, hTh⟩ := key T
  exact ⟨Th, hM E W D T Th hTh⟩

theorem sq_sum (M : ℕ) : ∑ m ∈ Icc 2 (M + 2), (((m : ℕ) : ℝ) ^ 2)⁻¹ ≤ 3 / 4 - ((M : ℝ) + 2)⁻¹ := by
  induction M with
  | zero => norm_num [Finset.Icc_self]
  | succ M ih =>
    have hs : ∑ m ∈ Icc 2 (M + 1 + 2), (((m : ℕ) : ℝ) ^ 2)⁻¹
        = ∑ m ∈ Icc 2 (M + 2), (((m : ℕ) : ℝ) ^ 2)⁻¹ + (((M : ℝ) + 3) ^ 2)⁻¹ := by
      rw [show M + 1 + 2 = (M + 2) + 1 by omega, Finset.sum_Icc_succ_top (by omega)]
      first
        | (push_cast; ring)
        | (congr 1; push_cast; ring)
    have hc2 : ((M + 1 : ℕ) : ℝ) + 2 = (M : ℝ) + 3 := by push_cast; ring
    rw [hs, hc2]
    have h2 : (0 : ℝ) < (M : ℝ) + 2 := by positivity
    have h3 : (0 : ℝ) < (M : ℝ) + 3 := by positivity
    have h2' := h2.ne'
    have h3' := h3.ne'
    have e : ((M : ℝ) + 2)⁻¹ - ((M : ℝ) + 3)⁻¹ - (((M : ℝ) + 3) ^ 2)⁻¹
        = (((M : ℝ) + 2) * ((M : ℝ) + 3) ^ 2)⁻¹ := by
      field_simp
      ring
    have hpos : 0 ≤ (((M : ℝ) + 2) * ((M : ℝ) + 3) ^ 2)⁻¹ := by positivity
    linarith

theorem pow_bd (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (((m : ℕ) : ℝ) ^ n)⁻¹ ≤ 4 * ((2 : ℝ) ^ n)⁻¹ * (((m : ℕ) : ℝ) ^ 2)⁻¹ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hm' : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpk : (2 : ℝ) ^ k ≤ (m : ℝ) ^ k := by gcongr
  have hL : ((m : ℝ) ^ (2 + k))⁻¹ = ((m : ℝ) ^ 2)⁻¹ * ((m : ℝ) ^ k)⁻¹ := by
    rw [pow_add, mul_inv]
  have hR : 4 * ((2 : ℝ) ^ (2 + k))⁻¹ * ((m : ℝ) ^ 2)⁻¹ = ((m : ℝ) ^ 2)⁻¹ * ((2 : ℝ) ^ k)⁻¹ := by
    rw [pow_add, mul_inv]
    first
      | ring
      | (norm_num; ring)
  rw [hL, hR]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hpk) (by positivity)

theorem densSum : DensSum := by
  intro P S q l f n hn hS hf
  have hA : ∀ p ∈ S, (q p ^ n)⁻¹ ≤ (((l p : ℕ) : ℝ) ^ n)⁻¹ := by
    intro p hp
    obtain ⟨hpr, hle⟩ := hS p hp
    have h0 : (0 : ℝ) < (l p : ℝ) := by exact_mod_cast hpr.pos
    exact inv_anti₀ (by positivity) (by gcongr)
  have hB : ∑ p ∈ S, (((l p : ℕ) : ℝ) ^ n)⁻¹ ≤
      (f : ℝ) * ∑ m ∈ S.image l, (((m : ℕ) : ℝ) ^ n)⁻¹ := by
    rw [Finset.sum_comp (fun m : ℕ => (((m : ℕ) : ℝ) ^ n)⁻¹) l, Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => ?_
    rw [nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h := hf m
    first
      | exact_mod_cast h
      | (norm_cast; convert h)
      | norm_cast
  have hC : ∑ m ∈ S.image l, (((m : ℕ) : ℝ) ^ n)⁻¹ ≤
      ∑ m ∈ Icc 2 (S.sup l + 2), (((m : ℕ) : ℝ) ^ n)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨p, hp, rfl⟩ := hm
      rw [Finset.mem_Icc]
      have h1 : l p ≤ S.sup l := Finset.le_sup hp
      exact ⟨(hS p hp).1.two_le, by omega⟩
    · intro m _ _
      positivity
  have hD : ∑ m ∈ Icc 2 (S.sup l + 2), (((m : ℕ) : ℝ) ^ n)⁻¹ ≤ 3 * ((2 : ℝ) ^ n)⁻¹ := by
    calc ∑ m ∈ Icc 2 (S.sup l + 2), (((m : ℕ) : ℝ) ^ n)⁻¹
        ≤ ∑ m ∈ Icc 2 (S.sup l + 2), 4 * ((2 : ℝ) ^ n)⁻¹ * (((m : ℕ) : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun m hm => ?_
          exact pow_bd m n (Finset.mem_Icc.mp hm).1 hn
      _ = 4 * ((2 : ℝ) ^ n)⁻¹ * ∑ m ∈ Icc 2 (S.sup l + 2), (((m : ℕ) : ℝ) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ 4 * ((2 : ℝ) ^ n)⁻¹ * (3 / 4 - (((S.sup l : ℕ) : ℝ) + 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (sq_sum _) (by positivity)
      _ ≤ 3 * ((2 : ℝ) ^ n)⁻¹ := by
          have h1 : 0 ≤ (((S.sup l : ℕ) : ℝ) + 2)⁻¹ := by positivity
          have h2 : 0 ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
          nlinarith
  have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  calc ∑ p ∈ S, (q p ^ n)⁻¹ ≤ ∑ p ∈ S, (((l p : ℕ) : ℝ) ^ n)⁻¹ := Finset.sum_le_sum hA
    _ ≤ (f : ℝ) * ∑ m ∈ S.image l, (((m : ℕ) : ℝ) ^ n)⁻¹ := hB
    _ ≤ (f : ℝ) * (3 * ((2 : ℝ) ^ n)⁻¹) := mul_le_mul_of_nonneg_left (hC.trans hD) hf0
    _ = 3 * (f : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by ring

theorem densChain : DensChain := by
  intro hSum hLe hSize P q l k r f sd hk hl hfib hsd
  have hn : 2 ≤ k - 2 * r - 2 := by omega
  have hB : ∀ S : Finset P, ∏ p ∈ S, Real.exp (4 * (q p ^ (k - 2 * r - 2))⁻¹) ≤
      Real.exp (12 * (f : ℝ) * ((2 : ℝ) ^ (k - 2 * r - 2))⁻¹) := by
    intro S
    have h1 := hSum P S q l f (k - 2 * r - 2) hn (fun p _ => hl p)
      (fun m => hfib m _ (fun p hp => (Finset.mem_filter.mp hp).2))
    rw [← Real.exp_sum, Real.exp_le_exp, ← Finset.mul_sum]
    linarith
  have hmain : sd ≤ Real.exp (12 * (f : ℝ) * ((2 : ℝ) ^ (k - 2 * r - 2))⁻¹) := by
    by_contra hc
    push_neg at hc
    obtain ⟨x, hx1, hx2⟩ := exists_between hc
    obtain ⟨S, hS⟩ := hsd x hx2
    linarith [hB S]
  exact ⟨hmain, hmain.trans (hLe f _ (hSize k r f hk))⟩

end Formalism.FourierDecayAlt.P.DensitySumsAndDomination

namespace Formalism.FourierDecayAlt.P

theorem domination_scale_top : Formalism.FourierDecayAlt.TC.DomScaleTop := DensitySumsAndDomination.domScaleTop

theorem recursion_hypothesis_scale_top : Formalism.FourierDecayAlt.TC.RecHypScaleTop := DensitySumsAndDomination.recHypScaleTop

theorem domination_after_of_local : Formalism.FourierDecayAlt.TC.DomAfterOfLocal := DensitySumsAndDomination.domAfterOfLocal

theorem density_sum : Formalism.FourierDecayAlt.TC.DensSum := DensitySumsAndDomination.densSum

theorem density_chain : Formalism.FourierDecayAlt.TC.DensChain := DensitySumsAndDomination.densChain

end Formalism.FourierDecayAlt.P

end

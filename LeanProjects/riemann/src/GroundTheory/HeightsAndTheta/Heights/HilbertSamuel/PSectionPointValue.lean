import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionPointValue
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SectionBounded

noncomputable section

set_option linter.unusedSectionVars false

namespace SectionPointValue

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def IsRep (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) (s : Ω) (g h : MRing ι) : Prop :=
  ∃ dg dh : K → ℕ, IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + n * a k) ∧
    aeval y g = s * aeval y h

theorem y_ne_zero {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    {p : Σ k, ι k} (hp : z p ≠ 0) : y p ≠ 0 := by
  intro h0
  apply hp
  have hX : (X p : MRing ι) ∈ mCoordIdeal y := by
    show X p ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    simp [mConeMap, h0]
  simpa using hz.2 _ hX

theorem cross {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n : ℕ} {s : Ω} {g h g' h' : MRing ι}
    (hr : IsRep y a n s g h) (hr' : IsRep y a n s g' h') {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) :
    eval z (map (Int.castRingHom ℂ) g) * eval z (map (Int.castRingHom ℂ) h') =
      eval z (map (Int.castRingHom ℂ) g') * eval z (map (Int.castRingHom ℂ) h) := by
  obtain ⟨dg, dh, hg, hh, hd, hy⟩ := hr
  obtain ⟨dg', dh', hg', hh', hd', hy'⟩ := hr'
  have hF : IsMultiHomog (g * h' - g' * h) (dg + dh') :=
    homog_sub (homog_mul hg hh') (homog_congr (homog_mul hg' hh) fun k => by
      simp only [Pi.add_apply]
      zify
      linear_combination hd' k - hd k)
  have hFy : aeval y (g * h' - g' * h) = 0 := by
    rw [map_sub, map_mul, map_mul, hy, hy']
    ring
  have := vanish hz hF hFy
  simp only [map_sub, map_mul, sub_eq_zero] at this
  exact this

theorem exists_rep_at {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    ∃ gh : MRing ι × MRing ι, IsRep y a n s gh.1 gh.2 ∧ eval z (map (Int.castRingHom ℂ) gh.2) ≠ 0 := by
  choose c hc using hz.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => y_ne_zero hz (hc k)
  obtain ⟨N, δ, G, hG, hdeg, hGv⟩ := exists_chartForm y c hyc (fun k => (n : ℤ) * a k) (hs c hyc)
  refine ⟨(G, chartMon c N), ⟨δ, N, hG, homog_chartMon c N, fun k => ?_, ?_⟩, ?_⟩
  · linear_combination hdeg k
  · rw [aeval_chartMon]
    exact hGv
  · rw [eval_chartMon]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)

theorem metric_ne {A : HermLine ι} {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (n : ℕ) :
    (A.h z : ℂ) ^ n ≠ 0 :=
  pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (A.pos z hz.1).ne')

def val (y : (Σ k, ι k) → Ω) (A : HermLine ι) (n : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ) : ℂ := by
  classical
  exact if hsz : s ∈ chartLat y A.a n ∧ z ∈ mcPts (mCoordIdeal y) then
    eval z (map (Int.castRingHom ℂ) (exists_rep_at hsz.1 hsz.2).choose.1) /
      (eval z (map (Int.castRingHom ℂ) (exists_rep_at hsz.1 hsz.2).choose.2) * (A.h z : ℂ) ^ n)
  else 0

theorem val_spec {y : (Σ k, ι k) → Ω} {A : HermLine ι} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {g h : MRing ι} (hr : IsRep y A.a n s g h) :
    eval z (map (Int.castRingHom ℂ) g) =
      val y A n s z * eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n := by
  have H := (exists_rep_at hs hz).choose_spec
  rw [val, dif_pos ⟨hs, hz⟩]
  have hc := cross hr H.1 hz
  have h1 := H.2
  have h2 := metric_ne (A := A) hz n
  rw [eq_comm, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero h1 h2)]
  linear_combination (-(A.h z : ℂ) ^ n) * hc

theorem val_eq {y : (Σ k, ι k) → Ω} {A : HermLine ι} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {g h : MRing ι} (hr : IsRep y A.a n s g h)
    (hh : eval z (map (Int.castRingHom ℂ) h) ≠ 0) :
    val y A n s z = eval z (map (Int.castRingHom ℂ) g) /
      (eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n) := by
  rw [eq_div_iff (mul_ne_zero hh (metric_ne hz n)), val_spec hs hz hr]
  ring

theorem rep_add {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n : ℕ} {s t : Ω} {g₁ h₁ g₂ h₂ : MRing ι}
    (r₁ : IsRep y a n s g₁ h₁) (r₂ : IsRep y a n t g₂ h₂) :
    IsRep y a n (s + t) (g₁ * h₂ + g₂ * h₁) (h₁ * h₂) := by
  obtain ⟨dg₁, dh₁, hg₁, hh₁, hd₁, hy₁⟩ := r₁
  obtain ⟨dg₂, dh₂, hg₂, hh₂, hd₂, hy₂⟩ := r₂
  refine ⟨dg₁ + dh₂, dh₁ + dh₂, homog_add (homog_mul hg₁ hh₂) (homog_congr (homog_mul hg₂ hh₁) fun k => ?_),
    homog_mul hh₁ hh₂, fun k => ?_, ?_⟩
  · simp only [Pi.add_apply]
    zify
    linear_combination hd₂ k - hd₁ k
  · simp only [Pi.add_apply]
    push_cast
    linear_combination hd₁ k
  · rw [map_add, map_mul, map_mul, map_mul, hy₁, hy₂]
    ring

theorem rep_mul {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n m : ℕ} {s t : Ω} {g₁ h₁ g₂ h₂ : MRing ι}
    (r₁ : IsRep y a n s g₁ h₁) (r₂ : IsRep y a m t g₂ h₂) :
    IsRep y a (n + m) (s * t) (g₁ * g₂) (h₁ * h₂) := by
  obtain ⟨dg₁, dh₁, hg₁, hh₁, hd₁, hy₁⟩ := r₁
  obtain ⟨dg₂, dh₂, hg₂, hh₂, hd₂, hy₂⟩ := r₂
  refine ⟨dg₁ + dg₂, dh₁ + dh₂, homog_mul hg₁ hg₂, homog_mul hh₁ hh₂, fun k => ?_, ?_⟩
  · simp only [Pi.add_apply]
    push_cast
    linear_combination hd₁ k + hd₂ k
  · rw [map_mul, map_mul, hy₁, hy₂]
    ring

def w (y : (Σ k, ι k) → Ω) (A : HermLine ι) (n : ℕ) : chartLat y A.a n →+ (((Σ k, ι k) → ℂ) → ℂ) :=
  AddMonoidHom.mk' (fun s => val y A n s) fun s t => by
    funext z
    show val y A n ((s + t : chartLat y A.a n) : Ω) z = val y A n s z + val y A n t z
    by_cases hz : z ∈ mcPts (mCoordIdeal y)
    · obtain ⟨⟨g₁, h₁⟩, r₁, n₁⟩ := exists_rep_at s.2 hz
      obtain ⟨⟨g₂, h₂⟩, r₂, n₂⟩ := exists_rep_at t.2 hz
      have hT := metric_ne (A := A) hz n
      rw [AddSubgroup.coe_add, val_eq (add_mem s.2 t.2) hz (rep_add r₁ r₂) (by simpa using mul_ne_zero n₁ n₂),
        val_eq s.2 hz r₁ n₁, val_eq t.2 hz r₂ n₂]
      simp only [map_add, map_mul]
      field_simp
    · simp [val, hz]

theorem val_continuousOn {y : (Σ k, ι k) → Ω} {A : HermLine ι}
    (hA : ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) {n : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a n) :
    ContinuousOn (val y A n s) (mcPts (mCoordIdeal y)) := by
  intro z₀ hz₀
  obtain ⟨⟨g, h⟩, r, hne⟩ := exists_rep_at hs hz₀
  have hcont : ∀ f : MRing ι, Continuous fun z : (Σ k, ι k) → ℂ => eval z (map (Int.castRingHom ℂ) f) :=
    fun f => MvPolynomial.continuous_eval _
  have hAc : ContinuousWithinAt (fun z => (A.h z : ℂ) ^ n) (mcPts (mCoordIdeal y)) z₀ :=
    (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
      ((hA z₀ hz₀.1).mono fun z hz => hz.1)).pow n
  have hF : ContinuousWithinAt (fun z => eval z (map (Int.castRingHom ℂ) g) /
      (eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n)) (mcPts (mCoordIdeal y)) z₀ :=
    (hcont g).continuousWithinAt.div ((hcont h).continuousWithinAt.mul hAc)
      (mul_ne_zero hne (metric_ne hz₀ n))
  refine hF.congr_of_eventuallyEq ?_ (val_eq hs hz₀ r hne)
  have hopen : {z | eval z (map (Int.castRingHom ℂ) h) ≠ 0} ∈ nhds z₀ :=
    (isOpen_ne_fun (hcont h) continuous_const).mem_nhds hne
  filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with z hz hz'
  exact val_eq hs hz' r hz

theorem secNormAt_eq {y : (Σ k, ι k) → Ω} {A : HermLine ι} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) : secNormAt y A n s z = ‖val y A n s z‖ := by
  have hT : 0 < A.h z := A.pos z hz.1
  have hnT : ‖(A.h z : ℂ) ^ n‖ = A.h z ^ n := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hT.le]
  have hb : IsBoundedAt y A n ‖val y A n s z‖ s z := by
    intro dg dh g h hg hh hd hy
    rw [val_spec hs hz ⟨dg, dh, hg, hh, hd, hy⟩, norm_mul, norm_mul, hnT]
  refine le_antisymm (secNormAt_le (norm_nonneg _) hb) ?_
  rw [secNormAt]
  refine le_csInf ⟨_, norm_nonneg _, hb⟩ ?_
  rintro c ⟨-, hc⟩
  obtain ⟨⟨g, h⟩, ⟨dg, dh, hg, hh, hd, hy⟩, hne⟩ := exists_rep_at hs hz
  have := hc dg dh g h hg hh hd hy
  rw [val_spec hs hz ⟨dg, dh, hg, hh, hd, hy⟩, norm_mul, norm_mul, hnT, mul_assoc, mul_assoc] at this
  exact le_of_mul_le_mul_right this (mul_pos (norm_pos_iff.mpr hne) (pow_pos hT n))

theorem val_mul {y : (Σ k, ι k) → Ω} {A : HermLine ι} {n m : ℕ} {s t st : Ω} (hs : s ∈ chartLat y A.a n)
    (ht : t ∈ chartLat y A.a m) (hst : st ∈ chartLat y A.a (n + m)) (he : st = s * t)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    val y A (n + m) st z = val y A n s z * val y A m t z := by
  obtain ⟨⟨g₁, h₁⟩, r₁, n₁⟩ := exists_rep_at hs hz
  obtain ⟨⟨g₂, h₂⟩, r₂, n₂⟩ := exists_rep_at ht hz
  have r := rep_mul r₁ r₂
  rw [← he] at r
  rw [val_eq hst hz r (by simpa using mul_ne_zero n₁ n₂), val_eq hs hz r₁ n₁, val_eq ht hz r₂ n₂]
  simp only [map_mul]
  rw [pow_add]
  ring

theorem exists_chart {y : (Σ k, ι k) → Ω} (hrel : IsRelevant (mCoordIdeal y)) :
    ∃ c : ∀ k, ι k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  refine ⟨fun k => (hrel k).choose, fun k h0 => (hrel k).choose_spec ?_⟩
  show X _ ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem common_denom {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n r : ℕ} (hrel : IsRelevant (mCoordIdeal y))
    (s : Fin r → Ω) (hs : ∀ i, s i ∈ chartLat y a n) :
    ∃ (e e' : K → ℕ) (h : MRing ι) (g : Fin r → MRing ι),
      IsMultiHomog h e' ∧ (∀ i, IsMultiHomog (g i) e) ∧ (∀ k, (e k : ℤ) = e' k + n * a k) ∧
      aeval y h ≠ 0 ∧ ∀ i, aeval y (g i) = s i * aeval y h := by
  obtain ⟨c, hc⟩ := exists_chart hrel
  choose N δ G hG hdeg hGv using fun i => exists_chartForm y c hc (fun k => (n : ℤ) * a k) (hs i c hc)
  have hN : ∀ i k, N i k ≤ ∑ j, N j k := fun i k =>
    Finset.single_le_sum (f := fun j => N j k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  set L : K → ℕ := fun k => ∑ j, N j k + ((n : ℤ) * a k).natAbs with hL
  refine ⟨fun k => ((L k : ℤ) + n * a k).toNat, L, chartMon c L, fun i => G i * chartMon c (L - N i),
    homog_chartMon c L, fun i => homog_congr (homog_mul (hG i) (homog_chartMon c _)) fun k => ?_,
    fun k => ?_, ?_, fun i => ?_⟩
  · have h1 := hdeg i k
    have h2 := hN i k
    simp only [Pi.add_apply, Pi.sub_apply, hL]
    generalize (n : ℤ) * a k = q at *
    generalize ∑ j, N j k = S at *
    omega
  · simp only [hL]
    generalize (n : ℤ) * a k = q
    generalize ∑ j, N j k = S
    omega
  · rw [aeval_chartMon]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  · rw [map_mul, hGv i, aeval_chartMon, aeval_chartMon, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_add, Pi.sub_apply]
    congr 1
    have h2 := hN i k
    simp only [hL]
    omega

end SectionPointValue

open SectionPointValue in

theorem SectionPointValue.proof : SectionPointValue.Statement := by
  intro K _ ι _ Ω _ y A hrel hA
  refine ⟨fun n => w y A n, fun n s => val_continuousOn hA s.2, ?_, ?_, ?_, ?_⟩
  · intro n s dg dh g h z hg hh hd hy hz
    exact val_spec s.2 hz ⟨dg, dh, hg, hh, hd, hy⟩
  · intro n s z hz
    exact secNormAt_eq s.2 hz
  · intro n k s t st he z hz
    exact val_mul s.2 t.2 st.2 he hz
  · intro n r s
    exact common_denom hrel (fun i => s i) fun i => (s i).2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

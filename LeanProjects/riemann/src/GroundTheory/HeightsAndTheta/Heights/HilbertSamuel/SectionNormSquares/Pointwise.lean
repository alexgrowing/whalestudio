import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SectionNormSquares.EventuallyDifferentiableAt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace SectionNormSqExtension

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev ev (F : MRing ι) (x : (Σ k, ι k) → ℂ) : ℂ := eval x (map (Int.castRingHom ℂ) F)

def nrm (k : K) (x : (Σ k, ι k) → ℂ) : ℝ := ∑ i, ‖x ⟨k, i⟩‖ ^ 2

def Nd (d : K → ℕ) (x : (Σ k, ι k) → ℂ) : ℝ := ∏ k, nrm k x ^ d k

variable (ι) in

def blockNZ : Set ((Σ k, ι k) → ℂ) := {x | ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0}

theorem isOpen_blockNZ : IsOpen (blockNZ ι) := by
  have h : blockNZ ι = ⋂ k, ⋃ i, {x : (Σ k, ι k) → ℂ | x ⟨k, i⟩ ≠ 0} := by
    ext x
    simp [blockNZ]
  rw [h]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem nrm_pos {x : (Σ k, ι k) → ℂ} (hx : x ∈ blockNZ ι) (k : K) : 0 < nrm k x := by
  obtain ⟨i, hi⟩ := hx k
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩

theorem Nd_pos (d : K → ℕ) {x : (Σ k, ι k) → ℂ} (hx : x ∈ blockNZ ι) : 0 < Nd d x :=
  Finset.prod_pos fun k _ => pow_pos (nrm_pos hx k) _

theorem contDiff_nrm (k : K) {n : WithTop ℕ∞} : ContDiff ℝ n (nrm (ι := ι) k) := by
  unfold nrm
  exact ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ _)

theorem contDiff_Nd (d : K → ℕ) {n : WithTop ℕ∞} : ContDiff ℝ n (Nd (ι := ι) d) := by
  unfold Nd
  exact contDiff_prod fun k _ => (contDiff_nrm k).pow _

theorem contDiffOn_term (F : MRing ι) (d : K → ℕ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun x => ‖ev F x‖ ^ 2 / Nd d x) (blockNZ ι) :=
  (contDiff_normSq_eval _).contDiffOn.div (contDiff_Nd d).contDiffOn fun _ hx => (Nd_pos d hx).ne'

variable {N : ℕ}

def Qf (d : (∀ k, ι k) → K → ℕ) (G : (∀ k, ι k) → Fin N → MRing ι) (x : (Σ k, ι k) → ℂ) : ℝ :=
  ∑ c, ∑ j, ‖ev (G c j) x‖ ^ 2 / Nd (d c) x

def Rf (d : (∀ k, ι k) → K → ℕ) (x : (Σ k, ι k) → ℂ) : ℝ :=
  ∑ c, ‖ev (chartMon c (d c)) x‖ ^ 2 / Nd (d c) x

def Ef (A : HermLine ι) (m : ℕ) (F : Finset (MRing ι × (K → ℕ))) (x : (Σ k, ι k) → ℂ) : ℝ :=
  A.h x ^ (2 * m) * ∑ p ∈ F, ‖ev p.1 x‖ ^ 2 / Nd p.2 x

def Sf (d : (∀ k, ι k) → K → ℕ) (G : (∀ k, ι k) → Fin N → MRing ι) (A : HermLine ι) (m : ℕ)
    (F : Finset (MRing ι × (K → ℕ))) (x : (Σ k, ι k) → ℂ) : ℝ :=
  (Qf d G x + Ef A m F x) / (Rf d x * A.h x ^ (2 * m))

theorem Rf_pos (d : (∀ k, ι k) → K → ℕ) {x : (Σ k, ι k) → ℂ} (hx : x ∈ blockNZ ι) : 0 < Rf d x := by
  obtain ⟨c, hc⟩ : ∃ c : ∀ k, ι k, ∀ k, x ⟨k, c k⟩ ≠ 0 := ⟨fun k => (hx k).choose, fun k => (hx k).choose_spec⟩
  refine Finset.sum_pos' (fun c' _ => div_nonneg (sq_nonneg _) (Nd_pos _ hx).le)
    ⟨c, Finset.mem_univ _, div_pos (pow_pos (norm_pos_iff.mpr ?_) 2) (Nd_pos _ hx)⟩
  rw [ev, eval_chartMon]
  exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)

theorem Qf_nonneg (d : (∀ k, ι k) → K → ℕ) (G : (∀ k, ι k) → Fin N → MRing ι) {x : (Σ k, ι k) → ℂ}
    (hx : x ∈ blockNZ ι) : 0 ≤ Qf d G x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nd_pos _ hx).le

section Data

variable {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {A : HermLine ι} {m : ℕ} {v : Fin N → Ω}
  {d e : (∀ k, ι k) → K → ℕ} {G : (∀ k, ι k) → Fin N → MRing ι} {F : Finset (MRing ι × (K → ℕ))}

theorem QE_pos (hgen : KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v)
    (he : ∀ c k, (e c k : ℤ) = d c k + m * A.a k) (hG : ∀ c j, IsMultiHomog (G c j) (e c))
    (hGy : ∀ c j, aeval y (G c j) = v j * aeval y (chartMon c (d c)))
    (hFspan : mCoordIdeal y ≤ Ideal.span ((fun p => p.1) '' (F : Set (MRing ι × (K → ℕ)))))
    {x : (Σ k, ι k) → ℂ} (hx : x ∈ blockNZ ι) : 0 < Qf d G x + Ef A m F x := by
  have hQ := Qf_nonneg d G hx
  have hh : 0 < A.h x ^ (2 * m) := pow_pos (A.pos x hx) _
  have hE : 0 ≤ Ef A m F x :=
    mul_nonneg hh.le (Finset.sum_nonneg fun p _ => div_nonneg (sq_nonneg _) (Nd_pos _ hx).le)
  by_cases h0 : ∀ p ∈ F, ev p.1 x = 0
  · have hxm := mem_mcPts_of_gens hFspan hx h0
    obtain ⟨c, hc⟩ : ∃ c : ∀ k, ι k, ∀ k, x ⟨k, c k⟩ ≠ 0 := ⟨fun k => (hx k).choose, fun k => (hx k).choose_spec⟩
    have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => y_ne_zero hxm (hc k)
    obtain ⟨j, hj⟩ := exists_G_ne hgen hyc (he c) (hG c) (hGy c) hxm hc
    have hpos : 0 < Qf d G x := by
      refine Finset.sum_pos' (fun c' _ => Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nd_pos _ hx).le)
        ⟨c, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => div_nonneg (sq_nonneg _) (Nd_pos _ hx).le)
          ⟨j, Finset.mem_univ _, div_pos (pow_pos (norm_pos_iff.mpr hj) 2) (Nd_pos _ hx)⟩⟩
    linarith
  · push Not at h0
    obtain ⟨p, hp, hpx⟩ := h0
    have hpos : 0 < Ef A m F x := mul_pos hh (Finset.sum_pos' (fun _ _ => div_nonneg (sq_nonneg _) (Nd_pos _ hx).le)
      ⟨p, hp, div_pos (pow_pos (norm_pos_iff.mpr hpx) 2) (Nd_pos _ hx)⟩)
    linarith

theorem Sf_pos (hgen : KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v)
    (he : ∀ c k, (e c k : ℤ) = d c k + m * A.a k) (hG : ∀ c j, IsMultiHomog (G c j) (e c))
    (hGy : ∀ c j, aeval y (G c j) = v j * aeval y (chartMon c (d c)))
    (hFspan : mCoordIdeal y ≤ Ideal.span ((fun p => p.1) '' (F : Set (MRing ι × (K → ℕ)))))
    {x : (Σ k, ι k) → ℂ} (hx : x ∈ blockNZ ι) : 0 < Sf d G A m F x :=
  div_pos (QE_pos hgen he hG hGy hFspan hx) (mul_pos (Rf_pos d hx) (pow_pos (A.pos x hx) _))

theorem contDiffOn_Sf (hsm : IsSmoothHerm A) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Sf d G A m F) (blockNZ ι) := by
  have hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => A.h x ^ (2 * m)) (blockNZ ι) := hsm.pow _
  have hQ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Qf d G) (blockNZ ι) := by
    unfold Qf
    exact ContDiffOn.sum fun c _ => ContDiffOn.sum fun j _ => contDiffOn_term _ _
  have hR : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Rf d) (blockNZ ι) := by
    unfold Rf
    exact ContDiffOn.sum fun c _ => contDiffOn_term _ _
  have hE : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ef A m F) (blockNZ ι) := by
    unfold Ef
    exact hh.mul (ContDiffOn.sum fun p _ => contDiffOn_term _ _)
  unfold Sf
  exact (hQ.add hE).div (hR.mul hh) fun x hx => (mul_pos (Rf_pos d hx) (pow_pos (A.pos x hx) _)).ne'

end Data

section Scaling

def wt (c : K → ℂ) (n : K → ℤ) : ℝ := ∏ k, ‖c k‖ ^ n k

theorem wt_ne_zero {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (n : K → ℤ) : wt c n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))

theorem eval_smul_of_isMultiHomog {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) (c : K → ℂ)
    (u : (Σ k, ι k) → ℂ) :
    eval (fun p ↦ c p.1 * u p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval u (map (Int.castRingHom ℂ) s) := by
  rw [eval_map, eval_map, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hprod : ∏ p, (c p.1 * u p) ^ d p = (∏ k, c k ^ a k) * ∏ p, u p ^ d p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    show ∏ i, c k ^ d ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
  rw [hprod]
  ring

theorem norm_ev_smul {F : MRing ι} {a : K → ℕ} (hF : IsMultiHomog F a) (c : K → ℂ) (x : (Σ k, ι k) → ℂ) :
    ‖ev F (fun p => c p.1 * x p)‖ ^ 2 = (∏ k, ‖c k‖ ^ (2 * a k)) * ‖ev F x‖ ^ 2 := by
  rw [ev, eval_smul_of_isMultiHomog hF, norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [norm_pow, ← pow_mul, mul_comm]

theorem nrm_smul (c : K → ℂ) (x : (Σ k, ι k) → ℂ) (k : K) :
    nrm k (fun p => c p.1 * x p) = ‖c k‖ ^ 2 * nrm k x := by
  unfold nrm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_mul, mul_pow]

theorem Nd_smul (d : K → ℕ) (c : K → ℂ) (x : (Σ k, ι k) → ℂ) :
    Nd d (fun p => c p.1 * x p) = (∏ k, ‖c k‖ ^ (2 * d k)) * Nd d x := by
  unfold Nd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [nrm_smul, mul_pow, ← pow_mul]

theorem prod_norm_pow_eq_wt (c : K → ℂ) (a : K → ℕ) :
    (∏ k, ‖c k‖ ^ (2 * a k)) = wt c (fun k => 2 * (a k : ℤ)) := by
  unfold wt
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast]
  push_cast
  rfl

theorem term_smul {F : MRing ι} {a b : K → ℕ} (hF : IsMultiHomog F a) (t : K → ℤ)
    (hab : ∀ k, (a k : ℤ) = b k + t k) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (x : (Σ k, ι k) → ℂ) :
    ‖ev F (fun p => c p.1 * x p)‖ ^ 2 / Nd b (fun p => c p.1 * x p) =
      wt c (fun k => 2 * t k) * (‖ev F x‖ ^ 2 / Nd b x) := by
  have hw : wt c (fun k => 2 * (a k : ℤ)) = wt c (fun k => 2 * (b k : ℤ)) * wt c (fun k => 2 * t k) := by
    unfold wt
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (norm_ne_zero_iff.mpr (hc k))]
    congr 1
    simp only [hab k]
    ring
  rw [norm_ev_smul hF, Nd_smul, prod_norm_pow_eq_wt, prod_norm_pow_eq_wt, hw, mul_assoc,
    mul_div_mul_left _ _ (wt_ne_zero hc _), mul_div_assoc]

theorem h_pow_smul (A : HermLine ι) (m : ℕ) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (x : (Σ k, ι k) → ℂ) :
    A.h (fun p => c p.1 * x p) ^ (2 * m) = wt c (fun k => 2 * ((m : ℤ) * A.a k)) * A.h x ^ (2 * m) := by
  rw [A.smul c x hc, mul_pow]
  congr 1
  unfold wt
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  push_cast
  ring

theorem Sf_smul {m : ℕ} {A : HermLine ι} {d e : (∀ k, ι k) → K → ℕ} {G : (∀ k, ι k) → Fin N → MRing ι}
    {F : Finset (MRing ι × (K → ℕ))} (he : ∀ c k, (e c k : ℤ) = d c k + m * A.a k)
    (hG : ∀ c j, IsMultiHomog (G c j) (e c)) (hF : ∀ p ∈ F, IsMultiHomog p.1 p.2)
    {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (x : (Σ k, ι k) → ℂ) :
    Sf d G A m F (fun p => c p.1 * x p) = Sf d G A m F x := by
  set lam := wt c (fun k => 2 * ((m : ℤ) * A.a k)) with hlam
  have hQ : Qf d G (fun p => c p.1 * x p) = lam * Qf d G x := by
    unfold Qf
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => term_smul (hG c' j) _ (he c') hc x
  have hR : Rf d (fun p => c p.1 * x p) = Rf d x := by
    unfold Rf
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [term_smul (homog_chartMon c' (d c')) (0 : K → ℤ) (fun k => by simp) hc x]
    simp [wt]
  have hE : Ef A m F (fun p => c p.1 * x p) = lam * Ef A m F x := by
    unfold Ef
    rw [h_pow_smul A m hc x, mul_assoc]
    congr 2
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [term_smul (hF p hp) (0 : K → ℤ) (fun k => by simp) hc x]
    simp [wt]
  unfold Sf
  rw [hQ, hE, hR, h_pow_smul A m hc x, ← mul_add, mul_left_comm, mul_div_mul_left _ _ (wt_ne_zero hc _)]

end Scaling

section Conj

theorem ev_conj (F : MRing ι) (x : (Σ k, ι k) → ℂ) :
    ev F (fun p => starRingEnd ℂ (x p)) = starRingEnd ℂ (ev F x) := by
  simp only [ev, eval_map]
  rw [eval₂_comp_left, RingHom.ext_int ((starRingEnd ℂ).comp (Int.castRingHom ℂ)) (Int.castRingHom ℂ)]
  rfl

theorem Nd_conj (d : K → ℕ) (x : (Σ k, ι k) → ℂ) : Nd d (fun p => starRingEnd ℂ (x p)) = Nd d x := by
  simp [Nd, nrm]

theorem Sf_conj {A : HermLine ι} (hconj : IsConjInvariantH A) (m : ℕ) (d : (∀ k, ι k) → K → ℕ)
    (G : (∀ k, ι k) → Fin N → MRing ι) (F : Finset (MRing ι × (K → ℕ))) (x : (Σ k, ι k) → ℂ) :
    Sf d G A m F (fun p => starRingEnd ℂ (x p)) = Sf d G A m F x := by
  simp only [Sf, Qf, Rf, Ef, ev_conj, Complex.norm_conj, Nd_conj, hconj x]

end Conj

section Value

variable {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {A : HermLine ι} {m : ℕ} {v : Fin N → Ω}
  {d e : (∀ k, ι k) → K → ℕ} {G : (∀ k, ι k) → Fin N → MRing ι} {F : Finset (MRing ι × (K → ℕ))}

theorem Sf_value (hv : ∀ j, v j ∈ chartLat y A.a m)
    (he : ∀ c k, (e c k : ℤ) = d c k + m * A.a k) (hG : ∀ c j, IsMultiHomog (G c j) (e c))
    (hGy : ∀ c j, aeval y (G c j) = v j * aeval y (chartMon c (d c)))
    (hF : ∀ p ∈ F, IsMultiHomog p.1 p.2 ∧ p.1 ∈ mCoordIdeal y)
    {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) :
    Sf d G A m F x = ∑ j, secNormAt y A m (v j) x ^ 2 := by
  have hx' : x ∈ blockNZ ι := hx.1
  have hE : Ef A m F x = 0 := by
    unfold Ef
    rw [Finset.sum_eq_zero fun p hp => by rw [show ev p.1 x = 0 from hx.2 _ (hF p hp).2]; simp, mul_zero]
  have hQ : Qf d G x = (∑ j, secNormAt y A m (v j) x ^ 2) * A.h x ^ (2 * m) * Rf d x := by
    unfold Qf Rf
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_congr rfl fun j _ => by rw [norm_eval_rep (hv j) (he c) (hG c j) (hGy c j) hx]]
    rw [← Finset.sum_div]
    have h1 : ∀ j, (secNormAt y A m (v j) x * ‖ev (chartMon c (d c)) x‖ * A.h x ^ m) ^ 2 =
        secNormAt y A m (v j) x ^ 2 * (‖ev (chartMon c (d c)) x‖ ^ 2 * A.h x ^ (2 * m)) := fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => h1 j, ← Finset.sum_mul]
    ring
  have hR := Rf_pos d hx'
  have hh : 0 < A.h x ^ (2 * m) := pow_pos (A.pos x hx') _
  unfold Sf
  rw [hE, hQ, add_zero]
  field_simp

end Value

end SectionNormSqExtension

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

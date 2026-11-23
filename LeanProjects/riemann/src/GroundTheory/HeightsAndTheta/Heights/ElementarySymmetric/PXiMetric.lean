import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.XiPluckerCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace XiMetricSmoothness

section Tens

variable {κ : Type} [Fintype κ]

def tensQ (G : Matrix κ κ ℂ) (u : κ × κ → ℂ) : ℝ :=
  (star u ⬝ᵥ (Matrix.kronecker G G *ᵥ u)).re

theorem tensQ_smul (G : Matrix κ κ ℂ) (c : ℂ) (u : κ × κ → ℂ) :
    tensQ G (c • u) = ‖c‖ ^ 2 * tensQ G u := by
  unfold tensQ
  rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul]
  have : star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  rw [this, Complex.re_ofReal_mul]

theorem tensQ_pos {G : Matrix κ κ ℂ} (hG : G.PosDef) {u : κ × κ → ℂ} (hu : u ≠ 0) : 0 < tensQ G u :=
  (Complex.pos_iff.1 ((hG.kronecker hG).dotProduct_mulVec_pos hu)).1

theorem tensQ_nonneg {G : Matrix κ κ ℂ} (hG : G.PosDef) (u : κ × κ → ℂ) : 0 ≤ tensQ G u := by
  by_cases hu : u = 0
  · subst hu
    simp [tensQ]
  · exact (tensQ_pos hG hu).le

theorem kron_pair (G : Matrix κ κ ℂ) (a b c d : κ → ℂ) :
    star (fun p : κ × κ => a p.1 * b p.2) ⬝ᵥ (Matrix.kronecker G G *ᵥ fun p => c p.1 * d p.2) =
      hermG G a c * hermG G b d := by
  simp only [hermG, dotProduct, mulVec, Matrix.kronecker, kroneckerMap_apply, Pi.star_apply, star_mul',
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ m, ∑ k, ∑ k', ∑ m', star (a k) * star (b m) * (G k k' * G m m' * (c k' * d m')) :=
        Finset.sum_comm
    _ = ∑ m, ∑ m', ∑ k, ∑ k', star (a k) * star (b m) * (G k k' * G m m' * (c k' * d m')) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        calc _ = ∑ k, ∑ m', ∑ k', star (a k) * star (b m) * (G k k' * G m m' * (c k' * d m')) :=
              Finset.sum_congr rfl fun k _ => Finset.sum_comm
          _ = _ := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ =>
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
        ring

theorem hermG_swap {G : Matrix κ κ ℂ} (hG : G.IsHermitian) (a b : κ → ℂ) :
    hermG G b a = star (hermG G a b) := by
  unfold hermG
  rw [Matrix.star_dotProduct, Matrix.star_mulVec, hG.eq, Matrix.dotProduct_mulVec]

theorem tensQ_pluck {G : Matrix κ κ ℂ} (hG : G.IsHermitian) (a b : κ → ℂ) :
    tensQ G (fun p => a p.1 * b p.2 - a p.2 * b p.1) =
      2 * ((hermG G a a).re * (hermG G b b).re - ‖hermG G a b‖ ^ 2) := by
  have hs : (fun p : κ × κ => a p.1 * b p.2 - a p.2 * b p.1) =
      (fun p => a p.1 * b p.2) - (fun p => b p.1 * a p.2) := by
    funext p
    simp only [Pi.sub_apply]
    ring
  have hA : (hermG G a a).im = 0 := Complex.conj_eq_iff_im.1 (hermG_swap hG a a).symm
  have hB : (hermG G b b).im = 0 := Complex.conj_eq_iff_im.1 (hermG_swap hG b b).symm
  rw [tensQ, hs, star_sub, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, kron_pair, kron_pair,
    kron_pair, kron_pair, hermG_swap hG a b]
  simp only [Complex.sub_re, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, hA, hB,
    Complex.sq_norm, Complex.normSq_apply]
  ring

end Tens

section Form

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {n : WithTop ℕ∞}

theorem contDiffOn_formRe {ι' : Type*} [Fintype ι'] {M : E → Matrix ι' ι' ℂ} {u v : E → ι' → ℂ}
    (hM : ∀ p q, ContDiffOn ℝ n (fun x => M x p q) s) (hu : ∀ p, ContDiffOn ℝ n (fun x => u x p) s)
    (hv : ∀ p, ContDiffOn ℝ n (fun x => v x p) s) :
    ContDiffOn ℝ n (fun x => (star (u x) ⬝ᵥ (M x *ᵥ v x)).re) s := by
  have h : ContDiffOn ℝ n (fun x => star (u x) ⬝ᵥ (M x *ᵥ v x)) s := by
    simp only [dotProduct, mulVec, Pi.star_apply]
    refine ContDiffOn.sum fun p _ => ContDiffOn.mul ?_ (ContDiffOn.sum fun q _ => (hM p q).mul (hv q))
    exact Complex.conjCLE.contDiff.comp_contDiffOn (hu p)
  exact Complex.reCLM.contDiff.comp_contDiffOn h

end Form

section Poly

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def evC (f : MRing ι) (w : (Σ k, ι k) → ℂ) : ℂ :=
  eval w (map (Int.castRingHom ℂ) f)

theorem contDiff_evC (f : MRing ι) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (evC f) := by
  unfold evC
  induction f using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p v hp => simpa using hp.mul (contDiff_apply ℝ ℂ v)

theorem evC_congr {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) {w w' : (Σ k, ι k) → ℂ}
    (h : ∀ p : Σ k, ι k, a p.1 ≠ 0 → w p = w' p) : evC f w = evC f w' := by
  unfold evC
  rw [eval_map, eval_map, eval₂_eq', eval₂_eq']
  refine Finset.sum_congr rfl fun d hd => ?_
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  by_cases hp : a p.1 = 0
  · have h0 : d p = 0 := by
      have hs := hf d hd p.1
      rw [hp] at hs
      exact (Finset.sum_eq_zero_iff.1 hs) p.2 (Finset.mem_univ _)
    rw [h0, pow_zero, pow_zero]
  · rw [h p hp]

theorem evC_smul {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (c : K → ℂ) (w : (Σ k, ι k) → ℂ) :
    evC f (fun p => c p.1 * w p) = (∏ k, c k ^ a k) * evC f w := by
  unfold evC
  rw [eval_map, eval_map, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ i : (Σ k, ι k), c i.1 ^ d i) = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem evC_rename_eval {K' : Type*} {ι' : K' → Type*} (e : (Σ k, ι k) → (Σ k, ι' k)) (f : MRing ι)
    (z : (Σ k, ι' k) → ℂ) : eval z (map (Int.castRingHom ℂ) (rename e f)) = evC f (fun p => z (e p)) := by
  unfold evC
  rw [map_rename, eval_rename]
  rfl

end Poly

section Line

variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]

abbrev YPt (ι ν κ : Type) := (Σ k, T.yyIdx ι ν κ k) → ℂ

def ynorm (w : YPt ι ν κ) : ℝ := ∑ i : ι, ‖w ⟨.base, i⟩‖ ^ 2

def dnorm (w : YPt ι ν κ) : ℝ := ∑ l : ν, ‖w ⟨.det, l⟩‖ ^ 2

def ypow (N : ℕ) (w : YPt ι ν κ) : ℝ := ∑ i : ι, (‖w ⟨.base, i⟩‖ ^ 2) ^ N

def lineV (w : YPt ι ν κ) : κ → ℂ := fun k => w ⟨.line, k⟩

def hv (G : YPt ι ν κ → Matrix κ κ ℂ) (w : YPt ι ν κ) : ℝ := (hermG (G w) (lineV w) (lineV w)).re

def numF (G : YPt ι ν κ → Matrix κ κ ℂ) (F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)) (w : YPt ι ν κ) : ℝ :=
  ∑ i, ∑ l, tensQ (G w) (fun p => evC (F i l p.1 p.2) w)

def remR (N : ℕ) {q : ℕ} (r : Fin q → MRing (T.yyIdx ι ν κ)) (b : Fin q → T.YBlk → ℕ) (w : YPt ι ν κ) : ℝ :=
  ynorm w ^ (N + 3) * ∑ j, ‖evC (r j) w‖ ^ 2 / (ynorm w ^ b j .base * dnorm w ^ b j .det)

def ratio (G : YPt ι ν κ → Matrix κ κ ℂ) (N : ℕ) (F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)) {q : ℕ}
    (r : Fin q → MRing (T.yyIdx ι ν κ)) (b : Fin q → T.YBlk → ℕ) (w : YPt ι ν κ) : ℝ :=
  (numF G F w + remR N r b w) / (2 * (ypow N w * dnorm w))

def xiH (G : YPt ι ν κ → Matrix κ κ ℂ) (N : ℕ) (F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)) {q : ℕ}
    (r : Fin q → MRing (T.yyIdx ι ν κ)) (b : Fin q → T.YBlk → ℕ) (w : YPt ι ν κ) : ℝ :=
  Real.sqrt (ratio G N F r b w) / hv G w

theorem prodY {M : Type*} [CommMonoid M] (f : T.YBlk → M) : ∏ k, f k = f .base * (f .det * f .line) := by
  rw [show (Finset.univ : Finset T.YBlk) = {.base, .det, .line} from rfl]
  simp

section Pos

variable {w : YPt ι ν κ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0)
include hw

theorem ynorm_pos : 0 < ynorm w := by
  obtain ⟨i, hi⟩ := hw .base
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩

theorem dnorm_pos : 0 < dnorm w := by
  obtain ⟨i, hi⟩ := hw .det
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩

theorem ypow_pos (N : ℕ) : 0 < ypow N w := by
  obtain ⟨i, hi⟩ := hw .base
  exact Finset.sum_pos' (fun j _ => pow_nonneg (sq_nonneg _) _)
    ⟨i, Finset.mem_univ _, pow_pos (pow_pos (norm_pos_iff.2 hi) 2) N⟩

theorem lineV_ne : lineV w ≠ 0 := by
  obtain ⟨i, hi⟩ := hw .line
  intro h0
  exact hi (congrFun h0 i)

theorem hv_pos {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : ∀ w, (G w).PosDef) : 0 < hv G w :=
  (Complex.pos_iff.1 ((hG w).dotProduct_mulVec_pos (lineV_ne hw))).1

end Pos

theorem remR_nonneg (N : ℕ) {q : ℕ} (r : Fin q → MRing (T.yyIdx ι ν κ)) (b : Fin q → T.YBlk → ℕ) (w : YPt ι ν κ) :
    0 ≤ remR N r b w := by
  have hy : 0 ≤ ynorm w := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hd : 0 ≤ dnorm w := Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact mul_nonneg (pow_nonneg hy _) (Finset.sum_nonneg fun j _ =>
    div_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg hy _) (pow_nonneg hd _)))

theorem numF_nonneg {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : ∀ w, (G w).PosDef) (F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ))
    (w : YPt ι ν κ) : 0 ≤ numF G F w :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => tensQ_nonneg (hG w) _

theorem num_add_rem_pos {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : ∀ w, (G w).PosDef) (N : ℕ)
    (F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)) {q : ℕ} (r : Fin q → MRing (T.yyIdx ι ν κ)) (b : Fin q → T.YBlk → ℕ)
    (hcov : ∀ w : YPt ι ν κ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ j, evC (r j) w = 0) → ∃ i l k m, evC (F i l k m) w ≠ 0)
    {w : YPt ι ν κ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) : 0 < numF G F w + remR N r b w := by
  by_cases hr : ∀ j, evC (r j) w = 0
  · obtain ⟨i, l, k, m, hF⟩ := hcov w hw hr
    have hu : (fun p : κ × κ => evC (F i l p.1 p.2) w) ≠ 0 := fun h0 => hF (congrFun h0 (k, m))
    have hpos : 0 < numF G F w := by
      refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun i => ∑ l, tensQ (G w) (fun p => evC (F i l p.1 p.2) w))
        (fun _ _ => Finset.sum_nonneg fun _ _ => tensQ_nonneg (hG w) _) (Finset.mem_univ i))
      exact lt_of_lt_of_le (tensQ_pos (hG w) hu) (Finset.single_le_sum
        (f := fun l => tensQ (G w) (fun p => evC (F i l p.1 p.2) w))
        (fun l _ => tensQ_nonneg (hG w) _) (Finset.mem_univ l))
    linarith [remR_nonneg N r b w]
  · obtain ⟨j, hj⟩ := not_forall.1 hr
    have hy := ynorm_pos hw
    have hd := dnorm_pos hw
    have hterm : 0 < ‖evC (r j) w‖ ^ 2 / (ynorm w ^ b j .base * dnorm w ^ b j .det) :=
      div_pos (pow_pos (norm_pos_iff.2 hj) 2) (mul_pos (pow_pos hy _) (pow_pos hd _))
    have hsum : 0 < ∑ j, ‖evC (r j) w‖ ^ 2 / (ynorm w ^ b j .base * dnorm w ^ b j .det) :=
      lt_of_lt_of_le hterm (Finset.single_le_sum
        (f := fun j => ‖evC (r j) w‖ ^ 2 / (ynorm w ^ b j .base * dnorm w ^ b j .det))
        (fun j _ => div_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg hy.le _) (pow_nonneg hd.le _)))
        (Finset.mem_univ j))
    have hrem : 0 < remR N r b w := mul_pos (pow_pos hy _) hsum
    linarith [numF_nonneg hG F w]

end Line

section Scale

variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] (c : T.YBlk → ℂ) (w : YPt ι ν κ)

theorem ynorm_smul : ynorm (fun p => c p.1 * w p) = ‖c .base‖ ^ 2 * ynorm w := by
  simp only [ynorm, Finset.mul_sum, norm_mul, mul_pow]

theorem dnorm_smul : dnorm (fun p => c p.1 * w p) = ‖c .det‖ ^ 2 * dnorm w := by
  simp only [dnorm, Finset.mul_sum, norm_mul, mul_pow]

theorem ypow_smul (N : ℕ) : ypow N (fun p => c p.1 * w p) = (‖c .base‖ ^ 2) ^ N * ypow N w := by
  simp only [ypow, Finset.mul_sum, norm_mul, mul_pow]

theorem hermG_smul (G : Matrix κ κ ℂ) (a : ℂ) (v : κ → ℂ) :
    (hermG G (a • v) (a • v)).re = ‖a‖ ^ 2 * (hermG G v v).re := by
  unfold hermG
  rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul]
  have : star a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  rw [this, Complex.re_ofReal_mul]

theorem hv_smul {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : G (fun p => c p.1 * w p) = G w) :
    hv G (fun p => c p.1 * w p) = ‖c .line‖ ^ 2 * hv G w := by
  unfold hv
  rw [hG]
  exact hermG_smul (G w) (c .line) (lineV w)

theorem prod_single_base (n : ℕ) : ∏ k, c k ^ (Pi.single T.YBlk.base n : T.YBlk → ℕ) k = c .base ^ n := by
  rw [prodY]
  simp

theorem numF_smul {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : G (fun p => c p.1 * w p) = G w) (N : ℕ)
    {F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)}
    (hF : ∀ i l k m, IsMultiHomog (F i l k m) (Pi.single T.YBlk.base (N + 3))) :
    numF G F (fun p => c p.1 * w p) = (‖c .base‖ ^ 2) ^ (N + 3) * numF G F w := by
  unfold numF
  rw [hG, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have e : (fun p : κ × κ => evC (F i l p.1 p.2) (fun p => c p.1 * w p)) =
      c .base ^ (N + 3) • fun p : κ × κ => evC (F i l p.1 p.2) w := by
    funext p
    rw [evC_smul (hF i l p.1 p.2), prod_single_base]
    rfl
  rw [e, tensQ_smul, norm_pow, ← pow_mul, ← pow_mul, mul_comm 2]

theorem normSq_evC_smul {f : MRing (T.yyIdx ι ν κ)} {a : T.YBlk → ℕ} (hf : IsMultiHomog f a) (ha : a .line = 0) :
    ‖evC f (fun p => c p.1 * w p)‖ ^ 2 =
      (‖c .base‖ ^ 2) ^ a .base * (‖c .det‖ ^ 2) ^ a .det * ‖evC f w‖ ^ 2 := by
  rw [evC_smul hf, prodY, ha, pow_zero, mul_one, norm_mul, norm_mul, norm_pow, norm_pow]
  ring

theorem remR_smul (hc : ∀ k, c k ≠ 0) (N : ℕ) {q : ℕ} {r : Fin q → MRing (T.yyIdx ι ν κ)} {b : Fin q → T.YBlk → ℕ}
    (hr : ∀ j, IsMultiHomog (r j) (b j)) (hrl : ∀ j, b j .line = 0) :
    remR N r b (fun p => c p.1 * w p) = (‖c .base‖ ^ 2) ^ (N + 3) * remR N r b w := by
  unfold remR
  rw [ynorm_smul, dnorm_smul, mul_pow, mul_assoc]
  refine congrArg _ (congrArg _ (Finset.sum_congr rfl fun j _ => ?_))
  have hA : (‖c .base‖ ^ 2) ^ b j .base * (‖c .det‖ ^ 2) ^ b j .det ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.2 (hc _))))
      (pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.2 (hc _))))
  rw [normSq_evC_smul c w (hr j) (hrl j), mul_pow, mul_pow,
    show (‖c .base‖ ^ 2) ^ b j .base * ynorm w ^ b j .base * ((‖c .det‖ ^ 2) ^ b j .det * dnorm w ^ b j .det) =
      ((‖c .base‖ ^ 2) ^ b j .base * (‖c .det‖ ^ 2) ^ b j .det) * (ynorm w ^ b j .base * dnorm w ^ b j .det) by ring,
    mul_div_mul_left _ _ hA]

theorem ratio_smul (hc : ∀ k, c k ≠ 0) {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : G (fun p => c p.1 * w p) = G w) (N : ℕ)
    {F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)}
    (hF : ∀ i l k m, IsMultiHomog (F i l k m) (Pi.single T.YBlk.base (N + 3)))
    {q : ℕ} {r : Fin q → MRing (T.yyIdx ι ν κ)} {b : Fin q → T.YBlk → ℕ}
    (hr : ∀ j, IsMultiHomog (r j) (b j)) (hrl : ∀ j, b j .line = 0) :
    ratio G N F r b (fun p => c p.1 * w p) = (‖c .base‖ ^ 3 / ‖c .det‖) ^ 2 * ratio G N F r b w := by
  unfold ratio
  rw [numF_smul c w hG N hF, remR_smul c w hc N hr hrl, ypow_smul, dnorm_smul, ← mul_add]
  have hAN : (‖c .base‖ ^ 2) ^ N ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.2 (hc _)))
  rw [show (‖c .base‖ ^ 2) ^ (N + 3) * (numF G F w + remR N r b w) =
      (‖c .base‖ ^ 2) ^ N * ((‖c .base‖ ^ 3) ^ 2 * (numF G F w + remR N r b w)) by ring,
    show 2 * ((‖c .base‖ ^ 2) ^ N * ypow N w * (‖c .det‖ ^ 2 * dnorm w)) =
      (‖c .base‖ ^ 2) ^ N * (‖c .det‖ ^ 2 * (2 * (ypow N w * dnorm w))) by ring,
    mul_div_mul_left _ _ hAN, mul_div_mul_comm, div_pow]

theorem xiH_smul (hc : ∀ k, c k ≠ 0) {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : G (fun p => c p.1 * w p) = G w) (N : ℕ)
    {F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)}
    (hF : ∀ i l k m, IsMultiHomog (F i l k m) (Pi.single T.YBlk.base (N + 3)))
    {q : ℕ} {r : Fin q → MRing (T.yyIdx ι ν κ)} {b : Fin q → T.YBlk → ℕ}
    (hr : ∀ j, IsMultiHomog (r j) (b j)) (hrl : ∀ j, b j .line = 0) :
    xiH G N F r b (fun p => c p.1 * w p) = (∏ k, ‖c k‖ ^ T.twoXiDegY k) * xiH G N F r b w := by
  unfold xiH
  have hK : 0 ≤ ‖c .base‖ ^ 3 / ‖c .det‖ := by positivity
  rw [ratio_smul c w hc hG N hF hr hrl, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK, hv_smul c w hG,
    mul_div_mul_comm, prodY]
  simp only [T.twoXiDegY, _root_.zpow_neg, zpow_ofNat]
  ring

end Scale

section Smooth

variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]

abbrev goodY (ι ν κ : Type) : Set (YPt ι ν κ) := {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0}

theorem contDiff_normSq_coord (p : Σ k, T.yyIdx ι ν κ k) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : YPt ι ν κ => ‖w p‖ ^ 2) :=
  (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ p)

theorem contDiff_ynorm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ynorm : YPt ι ν κ → ℝ) :=
  ContDiff.sum fun i _ => contDiff_normSq_coord ⟨.base, i⟩

theorem contDiff_dnorm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dnorm : YPt ι ν κ → ℝ) :=
  ContDiff.sum fun l _ => contDiff_normSq_coord ⟨.det, l⟩

theorem contDiff_ypow (N : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ypow N : YPt ι ν κ → ℝ) :=
  ContDiff.sum fun i _ => (contDiff_normSq_coord ⟨.base, i⟩).pow N

variable {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : IsEEMetric G)
include hG

theorem contDiffOn_hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hv G) (goodY ι ν κ) :=
  contDiffOn_formRe (fun m n => hG.2.2.2 m n) (fun _ => (contDiff_apply ℝ ℂ _).contDiffOn)
    (fun _ => (contDiff_apply ℝ ℂ _).contDiffOn)

theorem contDiffOn_numF (F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (numF G F) (goodY ι ν κ) := by
  unfold numF tensQ
  refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun l _ => ?_
  refine contDiffOn_formRe (M := fun w => Matrix.kronecker (G w) (G w)) (fun p q => ?_)
    (fun p => (contDiff_evC _).contDiffOn) (fun p => (contDiff_evC _).contDiffOn)
  simp only [Matrix.kronecker, kroneckerMap_apply]
  exact (hG.2.2.2 p.1 q.1).mul (hG.2.2.2 p.2 q.2)

omit hG in
theorem contDiffOn_remR (N : ℕ) {q : ℕ} (r : Fin q → MRing (T.yyIdx ι ν κ)) (b : Fin q → T.YBlk → ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (remR N r b) (goodY ι ν κ) := by
  unfold remR
  refine (contDiff_ynorm.pow _).contDiffOn.mul (ContDiffOn.sum fun j _ => ?_)
  refine ContDiffOn.div ((contDiff_norm_sq ℝ).comp (contDiff_evC (r j))).contDiffOn
    ((contDiff_ynorm.pow _).mul (contDiff_dnorm.pow _)).contDiffOn fun w hw => ?_
  exact mul_ne_zero (pow_ne_zero _ (ynorm_pos hw).ne') (pow_ne_zero _ (dnorm_pos hw).ne')

end Smooth

section Herm

variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {G : YPt ι ν κ → Matrix κ κ ℂ} {N : ℕ}
  {F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)} {q : ℕ} {r : Fin q → MRing (T.yyIdx ι ν κ)} {b : Fin q → T.YBlk → ℕ}

theorem ratio_pos (hG : IsEEMetric G)
    (hcov : ∀ w : YPt ι ν κ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ j, evC (r j) w = 0) → ∃ i l k m, evC (F i l k m) w ≠ 0)
    {w : YPt ι ν κ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) : 0 < ratio G N F r b w :=
  div_pos (num_add_rem_pos hG.1 N F r b hcov hw)
    (mul_pos two_pos (mul_pos (ypow_pos hw N) (dnorm_pos hw)))

def xiLine (hG : IsEEMetric G) (hF : ∀ i l k m, IsMultiHomog (F i l k m) (Pi.single T.YBlk.base (N + 3)))
    (hr : ∀ j, IsMultiHomog (r j) (b j)) (hrl : ∀ j, b j .line = 0)
    (hcov : ∀ w : YPt ι ν κ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ j, evC (r j) w = 0) → ∃ i l k m, evC (F i l k m) w ≠ 0) :
    HermLine (T.yyIdx ι ν κ) where
  a := T.twoXiDegY
  h := xiH G N F r b
  pos _ hz := div_pos (Real.sqrt_pos.2 (ratio_pos hG hcov hz)) (hv_pos hz hG.1)
  smul c z hc := xiH_smul c z hc (hG.2.2.1 c z hc) N hF hr hrl

theorem isSmoothHerm_xiLine (hG : IsEEMetric G)
    (hF : ∀ i l k m, IsMultiHomog (F i l k m) (Pi.single T.YBlk.base (N + 3)))
    (hr : ∀ j, IsMultiHomog (r j) (b j)) (hrl : ∀ j, b j .line = 0)
    (hcov : ∀ w : YPt ι ν κ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ j, evC (r j) w = 0) → ∃ i l k m, evC (F i l k m) w ≠ 0) :
    IsSmoothHerm (xiLine hG hF hr hrl hcov) := by
  unfold IsSmoothHerm
  show ContDiffOn ℝ _ (xiH G N F r b) (goodY ι ν κ)
  unfold xiH
  have hrat : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ratio G N F r b) (goodY ι ν κ) := by
    unfold ratio
    refine ((contDiffOn_numF hG F).add (contDiffOn_remR N r b)).div
      (contDiffOn_const.mul ((contDiff_ypow N).mul contDiff_dnorm).contDiffOn) fun w hw => ?_
    exact (mul_pos two_pos (mul_pos (ypow_pos hw N) (dnorm_pos hw))).ne'
  exact (hrat.sqrt fun w hw => (ratio_pos hG hcov hw).ne').div (contDiffOn_hv hG) fun w hw => (hv_pos hw hG.1).ne'

end Herm

section Identity

variable {D : ℕ} (S : ProjectiveLineBundle D) {N : ℕ} {F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx} {q : ℕ}
  {r : Fin q → MRing S.YIdx} {b : Fin q → T.YBlk → ℕ}

theorem lineV_yyEmb0 (z : (Σ k, S.WIdx k) → ℂ) :
    lineV (fun p => z (T.yyEmb 0 p)) = fun k : S.κ => z ⟨.line0, k⟩ := by
  funext k
  simp [lineV, T.yyEmb]

theorem lineV_yyEmb1 (z : (Σ k, S.WIdx k) → ℂ) :
    lineV (fun p => z (T.yyEmb 1 p)) = fun k : S.κ => z ⟨.line1, k⟩ := by
  funext k
  simp [lineV, T.yyEmb]

theorem good_yyEmb {z : (Σ k, S.WIdx k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (j : Fin 2) :
    ∀ k, ∃ i, (fun p => z (T.yyEmb j p)) ⟨k, i⟩ ≠ 0 := by
  intro k
  rcases k with _ | _ | _
  · exact hz .base
  · exact hz .det
  · fin_cases j
    · obtain ⟨i, hi⟩ := hz .line0
      exact ⟨i, by simpa [T.yyEmb] using hi⟩
    · obtain ⟨i, hi⟩ := hz .line1
      exact ⟨i, by simpa [T.yyEmb] using hi⟩

theorem xiH_identity (hF : S.IsPluckerRel N F) (hr : ∀ j, IsMultiHomog (r j) (b j)) (hrl : ∀ j, b j .line = 0)
    (hrW : ∀ j, rename (T.yyEmb 0) (r j) ∈ S.WW) {z : (Σ k, S.WIdx k) → ℂ} (hz : z ∈ mcPts S.WW) :
    ‖eval z (map (Int.castRingHom ℂ) S.g)‖ ^ 2 * xiH S.G N F r b (fun p => z (T.yyEmb 0 p)) *
        xiH S.G N F r b (fun p => z (T.yyEmb 1 p)) =
      ‖eval z (map (Int.castRingHom ℂ) S.h)‖ ^ 2 *
        sinSqG (S.G fun p => z (T.yyEmb 0 p)) (fun k => z ⟨.line0, k⟩) (fun k => z ⟨.line1, k⟩) := by
  set w0 : (Σ k, S.YIdx k) → ℂ := fun p => z (T.yyEmb 0 p) with hw0def
  set w1 : (Σ k, S.YIdx k) → ℂ := fun p => z (T.yyEmb 1 p) with hw1def
  set gz := eval z (map (Int.castRingHom ℂ) S.g)
  set hz' := eval z (map (Int.castRingHom ℂ) S.h)
  set v0 : S.κ → ℂ := fun k => z ⟨.line0, k⟩
  set v1 : S.κ → ℂ := fun k => z ⟨.line1, k⟩
  have hw0 := good_yyEmb S hz.1 0
  have hw1 := good_yyEmb S hz.1 1
  have hG01 : S.G w1 = S.G w0 := S.metric.2.1 w1 w0 (fun i => rfl) (fun l => rfl)
  have hFe : ∀ i l k m, evC (F i l k m) w1 = evC (F i l k m) w0 := fun i l k m =>
    evC_congr (hF.1 i l k m) fun p hp => by
      rcases p with ⟨_ | _ | _, i⟩
      · rfl
      · simp at hp
      · simp at hp
  have hre : ∀ j, evC (r j) w1 = evC (r j) w0 := fun j =>
    evC_congr (hr j) fun p hp => by
      rcases p with ⟨_ | _ | _, i⟩
      · rfl
      · rfl
      · exact absurd (hrl j) hp
  have hratio : ratio S.G N F r b w1 = ratio S.G N F r b w0 := by
    simp only [ratio, numF, remR, hG01, hFe, hre]
    rfl
  have hr0 : ∀ j, evC (r j) w0 = 0 := fun j => by
    have h0 := hz.2 _ (hrW j)
    rwa [evC_rename_eval] at h0
  have hrem0 : remR N r b w0 = 0 := by
    simp [remR, hr0]
  have hrelz : ∀ i l k m, gz * evC (F i l k m) w0 =
      (hz' * z ⟨.det, l⟩ * z ⟨.base, i⟩ ^ N) * (v0 k * v1 m - v0 m * v1 k) := fun i l k m => by
    have h0 := hz.2 _ (hF.2 i l k m)
    simp only [map_sub, map_mul, map_pow, map_X, eval_X, ProjectiveLineBundle.pluckerWW,
      evC_rename_eval] at h0
    rw [← hw0def] at h0
    linear_combination h0
  have hherm : (S.G w0).IsHermitian := (S.metric.1 w0).isHermitian
  have hv0 : lineV w0 = v0 := lineV_yyEmb0 S z
  have hv1 : lineV w1 = v1 := lineV_yyEmb1 S z
  set H0 := (hermG (S.G w0) v0 v0).re
  set H1 := (hermG (S.G w0) v1 v1).re
  set C := hermG (S.G w0) v0 v1
  have hterm : ∀ i l, ‖gz‖ ^ 2 * tensQ (S.G w0) (fun p => evC (F i l p.1 p.2) w0) =
      (2 * ‖hz'‖ ^ 2 * (H0 * H1 - ‖C‖ ^ 2)) * ((‖z ⟨.base, i⟩‖ ^ 2) ^ N * ‖z ⟨.det, l⟩‖ ^ 2) := fun i l => by
    rw [← tensQ_smul]
    have e : gz • (fun p : S.κ × S.κ => evC (F i l p.1 p.2) w0) =
        (hz' * z ⟨.det, l⟩ * z ⟨.base, i⟩ ^ N) • fun p : S.κ × S.κ => v0 p.1 * v1 p.2 - v0 p.2 * v1 p.1 := by
      funext p
      simp only [Pi.smul_apply, smul_eq_mul]
      exact hrelz i l p.1 p.2
    rw [e, tensQ_smul, tensQ_pluck hherm, norm_mul, norm_mul, norm_pow]
    ring
  have hnum : ‖gz‖ ^ 2 * numF S.G F w0 = 2 * ‖hz'‖ ^ 2 * (H0 * H1 - ‖C‖ ^ 2) * (ypow N w0 * dnorm w0) := by
    rw [numF, ypow, dnorm, Finset.sum_mul_sum]
    simp_rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => hterm i l
  have hH0 : 0 < H0 := by
    have := hv_pos (w := w0) hw0 S.metric.1
    rwa [hv, hv0] at this
  have hH1 : 0 < H1 := by
    have := hv_pos (w := w1) hw1 S.metric.1
    rwa [hv, hv1, hG01] at this
  have hY : 0 < ypow N w0 := ypow_pos (w := w0) hw0 N
  have hD : 0 < dnorm w0 := dnorm_pos (w := w0) hw0
  have hrat0 : 0 ≤ ratio S.G N F r b w0 :=
    div_nonneg (add_nonneg (numF_nonneg S.metric.1 F w0) (remR_nonneg N r b w0)) (by positivity)
  have hxi1 : xiH S.G N F r b w1 = Real.sqrt (ratio S.G N F r b w0) / H1 := by
    rw [xiH, hratio, hv, hv1, hG01]
  have hxi0 : xiH S.G N F r b w0 = Real.sqrt (ratio S.G N F r b w0) / H0 := by
    rw [xiH, hv, hv0]
  rw [hxi0, hxi1, sinSqG]
  change _ = ‖hz'‖ ^ 2 * (1 - ‖C‖ ^ 2 / (H0 * H1))
  have hs : Real.sqrt (ratio S.G N F r b w0) / H0 * (Real.sqrt (ratio S.G N F r b w0) / H1) =
      ratio S.G N F r b w0 / (H0 * H1) := by
    rw [div_mul_div_comm, Real.mul_self_sqrt hrat0]
  rw [mul_assoc, hs, ratio, hrem0, add_zero]
  calc _ = 2 * ‖hz'‖ ^ 2 * (H0 * H1 - ‖C‖ ^ 2) * (ypow N w0 * dnorm w0) / (2 * (ypow N w0 * dnorm w0)) /
        (H0 * H1) := by rw [← hnum]; ring
    _ = _ := by
      field_simp

end Identity

end XiMetricSmoothness

theorem XiMetric.proof (hRel : PluckerRel.Statement) (hCov : PluckerCover.Statement) : XiMetric.Statement := by
  intro D S
  obtain ⟨N, F, hF⟩ := hRel D S
  obtain ⟨q, r, b, hr, hrl, hrW, hcov⟩ := hCov D S N F hF
  exact ⟨XiMetricSmoothness.xiLine S.metric hF.1 hr hrl hcov, rfl,
    XiMetricSmoothness.isSmoothHerm_xiLine S.metric hF.1 hr hrl hcov, fun z hz => XiMetricSmoothness.xiH_identity S hF hr hrl hrW hz⟩

end

end GroundTheory.Heights₂.Heights.Inter

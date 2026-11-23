import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

namespace RRCentre

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

variable {k r : ℕ}

def genW (k r : ℕ) (w : Fin (k + 1) → ℝ) : Q.Mx k r :=
  Matrix.diagonal fun i =>
    if h : r ≤ i.val ∧ i.val ≤ r + k then Complex.I * ((w ⟨i.val - r, by omega⟩ : ℝ) : ℂ) else 0

def dW (k : ℕ) (w : Fin (k + 1) → ℝ) (t : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j => Complex.exp (Complex.I * ((t * w j : ℝ) : ℂ))

theorem exp_genW (w : Fin (k + 1) → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • genW k r w) = B2.embWb k r (dW k w t) := by
  unfold genW
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext i j
  unfold dW B2.embWb
  by_cases hij : i = j
  · subst hij
    by_cases h : r ≤ i.val ∧ i.val ≤ r + k
    · rw [dif_pos ⟨h, h⟩, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      simp only [Pi.coe_exp, Pi.smul_apply, dif_pos h, smul_eq_mul]
      rw [← Complex.exp_eq_exp_ℂ]
      congr 1
      push_cast
      ring
    · rw [dif_neg (fun h' => h h'.1), if_pos ⟨rfl, h⟩, Matrix.diagonal_apply_eq]
      simp only [Pi.coe_exp, Pi.smul_apply, dif_neg h, smul_zero]
      exact NormedSpace.exp_zero
  · rw [Matrix.diagonal_apply_ne _ hij]
    by_cases h1 : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
    · rw [dif_pos h1, Matrix.diagonal_apply_ne]
      intro he
      apply hij
      ext
      have := congrArg Fin.val he
      simp only at this
      omega
    · rw [dif_neg h1, if_neg (fun h2 => hij h2.1)]

theorem dW_uh (w : Fin (k + 1) → ℝ) (t : ℝ) : dW k w t ∈ UH (Hb k) := by
  show Matrix.conjTranspose (dW k w t) * Hb k * dW k w t = Hb k
  unfold dW Hb
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  have h : star (Complex.exp (Complex.I * ((t * w j : ℝ) : ℂ))) * Complex.exp (Complex.I * ((t * w j : ℝ) : ℂ)) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    simp
  simp only [Pi.star_apply]
  linear_combination (if j = Fin.last k then (-1 : ℂ) else 1) * h

theorem glev_mul_exp {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r)) (w : Fin (k + 1) → ℝ) (t : ℝ) :
    g * NormedSpace.exp ((t : ℂ) • genW k r w) ∈ Q.Glev k r (Fin.last r) := by
  rw [exp_genW]
  obtain ⟨μ, hμ, rfl⟩ := (TwoByOneBlock.UWb_iff g).1 (NFRadRedA.glev_uwb hg)
  rw [← TwoByOneBlock.emb_mul]
  exact NFRadRedA.uwb_glev (TwoByOneBlock.emb_mem_UWb (TwoByOneBlock.UH_mul hμ (dW_uh w t)))

theorem hasDerivAt_genW {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Φ : (Fin r → ℂ) → Q.Mx k r → E} {U : Set ((Fin r → ℂ) × Q.Mx k r)} {F : (Fin r → ℂ) × Q.Mx k r → E}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (he : ∀ y ∈ U, y.2 ∈ Q.Glev k r (Fin.last r) → Φ y.1 y.2 = F y)
    {x : (Fin r → ℂ) × Q.Mx k r} (hx : x ∈ U) (hxG : x.2 ∈ Q.Glev k r (Fin.last r)) (w : Fin (k + 1) → ℝ) :
    HasDerivAt (fun t : ℝ => Φ x.1 (x.2 * NormedSpace.exp ((t : ℂ) • genW k r w)))
      (fderiv ℝ F x ((0 : Fin r → ℂ), x.2 * genW k r w)) 0 := by
  have hγ : HasDerivAt (fun t : ℝ => (x.1, x.2 * NormedSpace.exp ((t : ℂ) • genW k r w)))
      ((0 : Fin r → ℂ), x.2 * genW k r w) 0 :=
    (hasDerivAt_const (0 : ℝ) x.1).prodMk (hasDerivAt_mul_exp_smul_zero x.2 _)
  have hγ0 : (fun t : ℝ => (x.1, x.2 * NormedSpace.exp ((t : ℂ) • genW k r w))) 0 = x := by
    simp [NormedSpace.exp_zero]
  have hd : DifferentiableAt ℝ F x := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have hcomp := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.congr_of_eventuallyEq ?_
  have hc : Filter.Tendsto (fun t : ℝ => (x.1, x.2 * NormedSpace.exp ((t : ℂ) • genW k r w))) (nhds 0) (nhds x) := by
    have h := hγ.continuousAt.tendsto
    first | (rw [hγ0] at h; exact h) | exact hγ0 ▸ h | (simp only [hγ0] at h; exact h)
  filter_upwards [hc (hU.mem_nhds hx)] with t ht
  exact he _ ht (glev_mul_exp hxG w t)

theorem hpk_col (p i : Fin (2 * r + k + 1)) (hp : r ≤ p.val ∧ p.val ≤ r + k) :
    Hpk k r i p = if i = p then (if p.val = r + k then -1 else 1) else 0 := by
  unfold Hpk
  by_cases hip : i = p
  · subst hip
    rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hp.1, hp.2, rfl⟩, if_pos rfl]
  · have hv : i.val ≠ p.val := fun h => hip (Fin.ext h)
    rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => hip h.2.2), if_neg hip]

theorem hpk_row (p j : Fin (2 * r + k + 1)) (hp : r ≤ p.val ∧ p.val ≤ r + k) :
    Hpk k r p j = if j = p then (if p.val = r + k then -1 else 1) else 0 := by
  unfold Hpk
  by_cases hip : j = p
  · subst hip
    rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hp.1, hp.2, rfl⟩, if_pos rfl]
  · have hv : j.val ≠ p.val := fun h => hip (Fin.ext h)
    rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => hip h.2.2.symm), if_neg hip]

theorem hs_apply (p i m : Fin (2 * r + k + 1)) :
    (Hpk k r * Matrix.single p p (1 : ℂ)) i m = if m = p then Hpk k r i p else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · by_cases hm : m = p
    · subst hm; simp [Matrix.single_apply]
    · simp [Matrix.single_apply, Ne.symm hm, hm]
  · intro l _ hl; simp [Matrix.single_apply, Ne.symm hl]
  · intro h; exact absurd (Finset.mem_univ p) h

theorem hpk_single (p : Fin (2 * r + k + 1)) (hp : r ≤ p.val ∧ p.val ≤ r + k) :
    (Hpk k r)⁻¹ * (Matrix.single p p (1 : ℂ)).conjTranspose * Hpk k r = Matrix.single p p 1 := by
  rw [Qx2.hpk_inv, Matrix.conjTranspose_single, star_one]
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · rw [hs_apply, if_pos rfl, hpk_col p i hp, hpk_row p j hp, Matrix.single_apply]
    by_cases hi : i = p <;> by_cases hj : j = p
    · subst hi; subst hj; simp only [if_true, and_self]; split_ifs <;> norm_num
    · simp [hi, hj, Ne.symm hj]
    · simp [hi, hj, Ne.symm hi]
    · simp [hi, hj, Ne.symm hi]
  · intro m _ hm
    rw [hs_apply, if_neg hm, zero_mul]
  · intro h; exact absurd (Finset.mem_univ p) h

theorem hpart1_single (p : Fin (2 * r + k + 1)) (hp : r ≤ p.val ∧ p.val ≤ r + k) :
    hpart1 (Hpk k r) (Matrix.single p p (1 : ℂ)) = 0 := by
  unfold hpart1
  rw [hpk_single p hp, sub_self, smul_zero]

theorem hpart2_single (n : ℕ) (p : Fin (2 * r + k + 1)) (hpn : p.val = r + n) (hn : n ≤ k) :
    hpart2 (Hpk k r) (Matrix.single p p (1 : ℂ)) = genW k r (fun j' => if j'.val = n then -1 else 0) := by
  have hp : r ≤ p.val ∧ p.val ≤ r + k := ⟨by omega, by omega⟩
  unfold hpart2
  rw [hpk_single p hp]
  ext i l
  unfold genW
  rw [Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul, Matrix.diagonal_apply]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  by_cases hil : i = l
  · subst hil
    rw [if_pos rfl]
    by_cases hi : i = p
    · subst hi
      rw [if_pos ⟨rfl, rfl⟩, dif_pos hp]
      dsimp only
      rw [if_pos (by omega)]
      field_simp
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    · rw [if_neg (fun h => hi h.1.symm)]
      dsimp only
      split_ifs with h1 h2
      · exfalso; apply hi; apply Fin.ext; omega
      all_goals simp
  · rw [if_neg (fun h => hil (h.1.symm.trans h.2)), if_neg hil]
    simp

theorem rdV_zero' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Q.Mx k r → E) (g : Q.Mx k r) :
    RdV (0 : Q.Mx k r) f g = 0 := by
  unfold RdV
  simp [NormedSpace.exp_zero]

theorem genW_sum : ∑ a : Fin (Q.mdim k r (Fin.last r)),
    genW k r (fun j' : Fin (k + 1) => if j'.val = a.val then (-1 : ℝ) else 0) = -genW k r (fun _ => 1) := by
  ext i l
  rw [Matrix.sum_apply, Matrix.neg_apply]
  unfold genW
  simp only [Matrix.diagonal_apply]
  by_cases hil : i = l
  · subst hil
    simp only [if_true]
    by_cases h : r ≤ i.val ∧ i.val ≤ r + k
    · simp only [dif_pos h]
      have hm : i.val - r < Q.mdim k r (Fin.last r) := by unfold Q.mdim; simp; omega
      rw [Finset.sum_eq_single ⟨i.val - r, hm⟩]
      · simp
      · intro b _ hb
        rw [if_neg]
        · simp
        · intro hh; apply hb; ext; simp only at hh ⊢; omega
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · simp [dif_neg h]
  · simp [hil]

theorem zc_eq (φ : ℝ) : zc k r φ = NormedSpace.exp ((φ : ℂ) • genW k r (fun _ => 1)) := by
  rw [exp_genW]
  unfold zc dW
  congr 1
  ext i j
  rw [Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · simp [h, mul_comm]
  · simp [h]

theorem eh_pp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Φ : (Fin r → ℂ) → Q.Mx k r → E} {U : Set ((Fin r → ℂ) × Q.Mx k r)} {F : (Fin r → ℂ) × Q.Mx k r → E}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (he : ∀ y ∈ U, y.2 ∈ Q.Glev k r (Fin.last r) → Φ y.1 y.2 = F y)
    {x : (Fin r → ℂ) × Q.Mx k r} (hx : x ∈ U) (hxG : x.2 ∈ Q.Glev k r (Fin.last r))
    (a : Fin (Q.mdim k r (Fin.last r))) :
    Q.EH k r (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) a) (Φ x.1) x.2 =
      Complex.I • fderiv ℝ F x ((0 : Fin r → ℂ),
        x.2 * genW k r (fun j' : Fin (k + 1) => if j'.val = a.val then (-1 : ℝ) else 0)) := by
  have ha : a.val ≤ k := by have := a.isLt; unfold Q.mdim at this; simp at this; omega
  have hpn : (Q.posL k r (Fin.last r) a).val = r + a.val := by simp [Q.posL]; omega
  have hp : r ≤ (Q.posL k r (Fin.last r) a).val ∧ (Q.posL k r (Fin.last r) a).val ≤ r + k :=
    ⟨by omega, by omega⟩
  show RdV _ _ _ + Complex.I • RdV _ _ _ = _
  rw [hpart1_single _ hp, hpart2_single a.val _ hpn ha, rdV_zero', zero_add]
  congr 1
  exact (hasDerivAt_genW hU hF he hx hxG _).deriv

end

end RRCentre

open RRCentre in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem rotation_centre_condition : GTRRCentre := by
  intro k r z z' Wp Wq _ _ _ _ π π' Φ x hx
  obtain ⟨U, F, hU, hxU, hF, he⟩ := Φ.2.2.1 x hx
  have hxG : x.2 ∈ Q.Glev k r (Fin.last r) := hx.2.1
  have hfun : (fun φ : ℝ => (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 (x.2 * zc k r φ)) =
      fun φ : ℝ => (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1
        (x.2 * NormedSpace.exp ((φ : ℂ) • genW k r (fun _ => 1))) := by
    funext φ; rw [zc_eq]
  rw [hfun]
  have hd := hasDerivAt_genW hU hF he hxU hxG (fun _ => 1)
  refine hd.congr_deriv ?_
  symm
  rw [Finset.sum_congr rfl (fun a _ => eh_pp hU hF he hxU hxG a), ← Finset.smul_sum, ← map_sum]
  have hs : ∑ a : Fin (Q.mdim k r (Fin.last r)), ((0 : Fin r → ℂ),
      x.2 * genW k r (fun j' : Fin (k + 1) => if j'.val = a.val then (-1 : ℝ) else 0)) =
      -((0 : Fin r → ℂ), x.2 * genW k r (fun _ => 1)) := by
    ext1
    · rw [Prod.fst_sum]; simp
    · rw [Prod.snd_sum, ← Finset.mul_sum, genW_sum]
      simp
  rw [hs, map_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

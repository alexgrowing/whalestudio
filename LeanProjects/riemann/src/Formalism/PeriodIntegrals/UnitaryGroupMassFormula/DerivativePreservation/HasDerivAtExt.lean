import Formalism.HermitianCurvature.StatementQ
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.EabLie

open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma hpk_inv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv (Hpk_sq k r)

lemma hpk_unit : IsUnit (Hpk k r) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, Hpk_sq, Matrix.det_one]))

lemma hpk_hh (A : Mx k r) : Hpk k r * (Hpk k r * A) = A := by
  rw [← Matrix.mul_assoc, Hpk_sq, Matrix.one_mul]

lemma hpk_hh' (A : Mx k r) : A * Hpk k r * Hpk k r = A := by
  rw [Matrix.mul_assoc, Hpk_sq, Matrix.mul_one]

lemma hpart1_skew (Z : Mx k r) :
    (hpart1 (Hpk k r) Z)ᴴ = -(Hpk k r * hpart1 (Hpk k r) Z * Hpk k r) := by
  unfold hpart1
  rw [hpk_inv]
  simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, Hpk_herm,
    conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc, hpk_hh]
  simp only [← Matrix.mul_assoc, hpk_hh']
  have : star (1 / 2 : ℂ) = 1 / 2 := by rw [star_div₀, star_one, Complex.star_def, map_ofNat]
  rw [this, ← smul_neg, neg_sub]

lemma hpart2_skew (Z : Mx k r) :
    (hpart2 (Hpk k r) Z)ᴴ = -(Hpk k r * hpart2 (Hpk k r) Z * Hpk k r) := by
  unfold hpart2
  rw [hpk_inv]
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, Hpk_herm,
    conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc, hpk_hh]
  simp only [← Matrix.mul_assoc, hpk_hh']
  have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    rw [star_div₀, star_one, star_mul', Complex.star_def, Complex.conj_I, map_ofNat]
    rw [mul_neg, div_neg]
  rw [this, neg_smul]
  exact congrArg (fun M : Mx k r => -((1 / (2 * Complex.I)) • M)) (add_comm _ _)

lemma skew_real (X : Mx k r) (hX : Xᴴ = -(Hpk k r * X * Hpk k r)) (t : ℝ) :
    ((t : ℂ) • X)ᴴ = -(Hpk k r * ((t : ℂ) • X) * Hpk k r) := by
  rw [Matrix.conjTranspose_smul, hX, Complex.star_def, Complex.conj_ofReal]
  simp [Matrix.smul_mul, Matrix.mul_smul]

lemma exp_mem_UH (Y : Mx k r) (hY : Yᴴ = -(Hpk k r * Y * Hpk k r)) :
    NormedSpace.exp Y ∈ UH (Hpk k r) := by
  have hYh : Yᴴ = Hpk k r * (-Y) * (Hpk k r)⁻¹ := by
    rw [hY, hpk_inv, Matrix.mul_neg, Matrix.neg_mul]
  have hexp : (NormedSpace.exp Y)ᴴ = Hpk k r * NormedSpace.exp (-Y) * Hpk k r := by
    rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hpk_unit, hpk_inv]
  have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  show (NormedSpace.exp Y)ᴴ * Hpk k r * NormedSpace.exp Y = Hpk k r
  rw [hexp, Matrix.mul_assoc (Hpk k r * NormedSpace.exp (-Y)) (Hpk k r) (Hpk k r), Hpk_sq,
    Matrix.mul_one, Matrix.mul_assoc, hc, Matrix.mul_one]

lemma exp_fix (Y : Mx k r) (c : Fin (2 * r + k + 1)) (hY : ∀ x, Y x c = 0) :
    NormedSpace.exp Y *ᵥ bvec c = bvec c := by
  set P : Mx k r := Matrix.single c c 1 with hPdef
  have hYP : Y * P = 0 := by
    ext x y
    simp only [hPdef, Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    split_ifs with h
    · rw [← h.1, hY, mul_one]
    · exact mul_zero _
  have hne : NormedSpace.exp Y ≠ 0 := by
    intro h0
    have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
        NormedSpace.exp_zero]
    rw [h0, Matrix.mul_zero] at hc
    have := congrFun (congrFun hc ⟨0, by omega⟩) ⟨0, by omega⟩
    simp at this
  have hsum : Summable (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n) := by
    by_contra hns
    apply hne
    rw [congrFun (NormedSpace.exp_eq_tsum ℂ) Y]
    exact tsum_eq_zero_of_not_summable hns
  have hhas : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n) (NormedSpace.exp Y) := by
    have := hsum.hasSum
    rwa [← congrFun (NormedSpace.exp_eq_tsum ℂ) Y] at this
  have h1 := hhas.mul_right P
  have h2 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n * P) P := by
    have := hasSum_single (f := fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n * P) 0 (by
      intro m hm
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
      rw [Matrix.smul_mul, pow_succ, Matrix.mul_assoc, hYP, Matrix.mul_zero, smul_zero])
    simpa using this
  have hEP : NormedSpace.exp Y * P = P := h1.unique h2
  have hPv : P *ᵥ bvec c = bvec c := by
    ext x
    by_cases h : x = c
    · subst h; simp [hPdef, bvec, Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply]
    · simp [hPdef, bvec, Matrix.mulVec, dotProduct, Pi.single_apply, h, Ne.symm h]
  rw [← hPv, Matrix.mulVec_mulVec, hEP]

lemma glev_mul {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  obtain ⟨hgU, hgv⟩ := hg
  obtain ⟨hhU, hhv⟩ := hh
  refine ⟨?_, fun a ha => ?_⟩
  · show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    have e1 : gᴴ * Hpk k r * g = Hpk k r := hgU
    have e2 : hᴴ * Hpk k r * h = Hpk k r := hhU
    rw [conjTranspose_mul]
    calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [e1, e2]
  · obtain ⟨h1, h2⟩ := hhv a ha
    obtain ⟨g1, g2⟩ := hgv a ha
    exact ⟨by rw [← Matrix.mulVec_mulVec, h1, g1], by rw [← Matrix.mulVec_mulVec, h2, g2]⟩

lemma exp_mem_glev (i : Fin (r + 1)) (X : Mx k r) (hX : Xᴴ = -(Hpk k r * X * Hpk k r))
    (hc : ∀ a : Fin r, a.val < i.val → ∀ x, X x (eI k r a) = 0 ∧ X x (esI k r a) = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  refine ⟨exp_mem_UH _ (skew_real X hX t), fun a ha => ⟨?_, ?_⟩⟩
  · exact exp_fix _ _ (fun x => by rw [Matrix.smul_apply, (hc a ha x).1, smul_zero])
  · exact exp_fix _ _ (fun x => by rw [Matrix.smul_apply, (hc a ha x).2, smul_zero])

lemma hpk_zero (i : Fin (r + 1)) (p : Fin (mdim k r i)) (a : Fin r) (ha : a.val < i.val) :
    Hpk k r (posL k r i p) (eI k r a) = 0 ∧ Hpk k r (posL k r i p) (esI k r a) = 0 := by
  have hp := p.isLt
  have hi := i.isLt
  unfold mdim at hp
  constructor
  · simp only [Hpk, posL, eI, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  · simp only [Hpk, posL, esI, Fin.ext_iff]
    split_ifs <;> first | rfl | omega

lemma unit_col (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (c : Fin (2 * r + k + 1))
    (hcq : c ≠ posL k r i q) (hHc : Hpk k r (posL k r i p) c = 0) (x : Fin (2 * r + k + 1)) :
    (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ)) x c = 0 ∧
    (Hpk k r * (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ * Hpk k r) x c = 0 := by
  constructor
  · simp [Ne.symm hcq]
  · rw [Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    have : ((Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ * Hpk k r) y c = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun z _ => ?_)
      rw [conjTranspose_apply, Matrix.single_apply]
      split_ifs with h
      · rw [← h.1, hHc, mul_zero]
      · simp
    rw [this, mul_zero]

lemma posL_ne (i : Fin (r + 1)) (q : Fin (mdim k r i)) (a : Fin r) (ha : a.val < i.val) :
    eI k r a ≠ posL k r i q ∧ esI k r a ≠ posL k r i q := by
  have hq := q.isLt
  have hi := i.isLt
  unfold mdim at hq
  constructor <;> · intro h; rw [Fin.ext_iff] at h; simp [eI, esI, posL] at h; omega

lemma hpart_cols (i : Fin (r + 1)) (p q : Fin (mdim k r i)) :
    (∀ a : Fin r, a.val < i.val → ∀ x,
      hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (eI k r a) = 0 ∧
      hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (esI k r a) = 0) ∧
    (∀ a : Fin r, a.val < i.val → ∀ x,
      hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (eI k r a) = 0 ∧
      hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (esI k r a) = 0) := by
  have key : ∀ a : Fin r, a.val < i.val → ∀ x c, (c = eI k r a ∨ c = esI k r a) →
      (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ)) x c = 0 ∧
      (Hpk k r * (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ * Hpk k r) x c = 0 := by
    intro a ha x c hc
    obtain ⟨n1, n2⟩ := posL_ne i q a ha
    obtain ⟨z1, z2⟩ := hpk_zero i p a ha
    rcases hc with rfl | rfl
    · exact unit_col i p q _ n1 z1 x
    · exact unit_col i p q _ n2 z2 x
  refine ⟨fun a ha x => ?_, fun a ha x => ?_⟩ <;>
  · obtain ⟨e1, e2⟩ := key a ha x _ (Or.inl rfl)
    obtain ⟨e3, e4⟩ := key a ha x _ (Or.inr rfl)
    simp only [hpart1, hpart2]
    rw [hpk_inv]
    refine ⟨?_, ?_⟩ <;>
    · first
      | rw [Matrix.smul_apply, Matrix.sub_apply]
      | rw [Matrix.smul_apply, Matrix.add_apply]
      simp only [e1, e2, e3, e4, sub_zero, add_zero, smul_zero]

theorem exp_hpart1_mem (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1))
      ∈ Glev k r i :=
  exp_mem_glev i _ (hpart1_skew _) (hpart_cols i p q).1 t

theorem exp_hpart2_mem (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1))
      ∈ Glev k r i :=
  exp_mem_glev i _ (hpart2_skew _) (hpart_cols i p q).2 t

theorem hasDerivAt_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (i : Fin (r + 1)) (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    (f F : Mx k r → E) (U : Set (Mx k r)) (g : Mx k r) (hU : IsOpen U) (hg : g ∈ U)
    (hgG : g ∈ Glev k r i) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ x ∈ U, x ∈ Glev k r i → f x = F x) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have hγ := hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
    filter_upwards [hmem] with t ht
    exact hfF _ ht (glev_mul hgG (hX t))
  exact hcomp.congr_of_eventuallyEq hev

theorem rdV_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (i : Fin (r + 1)) (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    (f F : Mx k r → E) (U : Set (Mx k r)) (g : Mx k r) (hU : IsOpen U) (hg : g ∈ U)
    (hgG : g ∈ Glev k r i) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ x ∈ U, x ∈ Glev k r i → f x = F x) :
    RdV X f g = fderiv ℝ F g (g * X) :=
  (hasDerivAt_ext i X hX f F U g hU hg hgG hF hfF).deriv

end Formalism.FourierDecayAlt.Q.EabLie

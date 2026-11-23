import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorusInvariance.TransferInvarianceRestriction
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated

open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.TInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma hpk_inv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_right_inv (Hpk_sq k r)

lemma hpk_unit : IsUnit (Hpk k r) := ⟨⟨Hpk k r, Hpk k r, Hpk_sq k r, Hpk_sq k r⟩, rfl⟩

lemma hpk_hh (A : Mx k r) : Hpk k r * (Hpk k r * A) = A := by rw [← mul_assoc, Hpk_sq, one_mul]

lemma hpart1_skew (Z : Mx k r) :
    (hpart1 (Hpk k r) Z)ᴴ = -(Hpk k r * hpart1 (Hpk k r) Z * Hpk k r) := by
  unfold hpart1
  rw [hpk_inv]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm, hs,
    mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_assoc, hpk_hh, Hpk_sq, mul_one]
  rw [← smul_neg, neg_sub]

lemma hpart2_skew (Z : Mx k r) :
    (hpart2 (Hpk k r) Z)ᴴ = -(Hpk k r * hpart2 (Hpk k r) Z * Hpk k r) := by
  unfold hpart2
  rw [hpk_inv]
  have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm, hs,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_assoc, hpk_hh, Hpk_sq, mul_one]
  rw [neg_smul, add_comm Zᴴ]

lemma skew_real (X : Mx k r) (hX : Xᴴ = -(Hpk k r * X * Hpk k r)) (t : ℝ) :
    ((t : ℂ) • X)ᴴ = -(Hpk k r * ((t : ℂ) • X) * Hpk k r) := by
  rw [conjTranspose_smul, hX]
  simp [Complex.star_def, Complex.conj_ofReal, mul_smul_comm, smul_mul_assoc]

lemma exp_mem_UH (Y : Mx k r) (hY : Yᴴ = -(Hpk k r * Y * Hpk k r)) :
    NormedSpace.exp Y ∈ UH (Hpk k r) := by
  show (NormedSpace.exp Y)ᴴ * Hpk k r * NormedSpace.exp Y = Hpk k r
  have e1 : Yᴴ = Hpk k r * (-Y) * (Hpk k r)⁻¹ := by
    rw [hY, hpk_inv, mul_neg, neg_mul]
  rw [← Matrix.exp_conjTranspose, e1, Matrix.exp_conj _ _ hpk_unit, hpk_inv]
  simp only [mul_assoc, hpk_hh]
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel, NormedSpace.exp_zero, mul_one]

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
    · simp [hPdef, bvec, Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply, h, Ne.symm h]
  rw [← hPv, Matrix.mulVec_mulVec, hEP]

lemma exp_mem_glev (i : Fin (r + 1)) (X : Mx k r) (hX : Xᴴ = -(Hpk k r * X * Hpk k r))
    (hc : ∀ a : Fin r, a.val < i.val → ∀ x, X x (eI k r a) = 0 ∧ X x (esI k r a) = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  simp only [Glev, Set.mem_setOf_eq]
  refine ⟨exp_mem_UH _ (skew_real X hX t), fun a ha => ⟨exp_fix _ _ fun x => ?_, exp_fix _ _ fun x => ?_⟩⟩
  · rw [Matrix.smul_apply, (hc a ha x).1, smul_zero]
  · rw [Matrix.smul_apply, (hc a ha x).2, smul_zero]

lemma hpk_zero (i : Fin (r + 1)) (p : Fin (mdim k r i)) (a : Fin r) (ha : a.val < i.val) :
    Hpk k r (posL k r i p) (eI k r a) = 0 ∧ Hpk k r (posL k r i p) (esI k r a) = 0 := by
  have hp := p.isLt
  have ha' := a.isLt
  have hi := i.isLt
  unfold mdim at hp
  simp only [Hpk, posL, eI, esI, Fin.mk.injEq]
  constructor <;> split_ifs <;> first | rfl | (exfalso; omega)

lemma unit_col (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (c : Fin (2 * r + k + 1))
    (hcq : c ≠ posL k r i q) (hHc : Hpk k r (posL k r i p) c = 0) (x : Fin (2 * r + k + 1)) :
    (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ)) x c = 0 ∧
    (Hpk k r * (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ * Hpk k r) x c = 0 := by
  constructor
  · simp [Matrix.single_apply, hcq, Ne.symm hcq]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = posL k r i p
    · rw [hl, hHc, mul_zero]
    · have h0 : (Hpk k r * (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ) x l = 0 := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun m _ => ?_
        simp [Matrix.conjTranspose_apply, Matrix.single_apply, hl, Ne.symm hl]
      rw [h0, zero_mul]

lemma posL_ne (i : Fin (r + 1)) (q : Fin (mdim k r i)) (a : Fin r) (ha : a.val < i.val) :
    eI k r a ≠ posL k r i q ∧ esI k r a ≠ posL k r i q := by
  have hq := q.isLt
  have ha' := a.isLt
  unfold mdim at hq
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
  · have h2 := congrArg Fin.val h
    simp only [eI, esI, posL] at h2
    omega

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
      ∈ Glev k r i := exp_mem_glev i _ (hpart1_skew _) (hpart_cols i p q).1 t

theorem exp_hpart2_mem (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1))
      ∈ Glev k r i := exp_mem_glev i _ (hpart2_skew _) (hpart_cols i p q).2 t

theorem rdV_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (i : Fin (r + 1)) (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    (f F : Mx k r → E) (U : Set (Mx k r)) (g : Mx k r) (hU : IsOpen U) (hg : g ∈ U)
    (hgG : g ∈ Glev k r i) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ x ∈ U, x ∈ Glev k r i → f x = F x) :
    RdV X f g = fderiv ℝ F g (g * X) := by
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
    exact hfF _ ht (glev_mul' hgG (hX t))
  exact (hcomp.congr_of_eventuallyEq hev).deriv

theorem transfer_invariance_congruence : StepCongr := by
  intro E _ _ k r i D a b f f' g hD hg hff
  have key : ∀ X : Mx k r, (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i) →
      RdV X f g = RdV X f' g := by
    intro X hX
    unfold RdV
    apply Filter.EventuallyEq.deriv_eq
    have hγ := hasDerivAt_mul_exp_smul_zero g X
    have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp [NormedSpace.exp_zero]
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ D :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hD.mem_nhds hg.2)
    filter_upwards [hmem] with t ht
    exact hff _ ⟨glev_mul' hg.1 (hX t), ht⟩
  show RdV _ f g + Complex.I • RdV _ f g = RdV _ f' g + Complex.I • RdV _ f' g
  rw [key _ (exp_hpart1_mem i a b), key _ (exp_hpart2_mem i a b)]

lemma rdV_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (X s' g : Mx k r) (f : Mx k r → E)
    (hu1 : s' * s'⁻¹ = 1) (hu2 : s'⁻¹ * s' = 1) :
    RdV X (fun x => f (x * s')) g = RdV (s'⁻¹ * X * s') f (g * s') := by
  have hU : IsUnit s' := ⟨⟨s', s'⁻¹, hu1, hu2⟩, rfl⟩
  simp only [RdV]
  congr 1
  funext t
  congr 1
  rw [show ((t : ℂ) • (s'⁻¹ * X * s')) = s'⁻¹ * ((t : ℂ) • X) * s' by rw [mul_smul_comm, smul_mul_assoc],
    Matrix.exp_conj' _ _ hU]
  simp only [mul_assoc]
  rw [← mul_assoc s' s'⁻¹, hu1, one_mul]

lemma uh_inv_eq {s : Mx k r} (hs : s ∈ UH (Hpk k r)) : s⁻¹ = Hpk k r * sᴴ * Hpk k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  refine Matrix.inv_eq_left_inv ?_
  rw [show Hpk k r * sᴴ * Hpk k r * s = Hpk k r * (sᴴ * Hpk k r * s) by simp only [mul_assoc], hs', Hpk_sq]

lemma conj_part {s : Mx k r} (hs : s ∈ UH (Hpk k r)) (Z : Mx k r) :
    (Hpk k r)⁻¹ * (s⁻¹ * Z * s)ᴴ * Hpk k r = s⁻¹ * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) * s := by
  have hi := uh_inv_eq hs
  have h1 : sᴴ = Hpk k r * s⁻¹ * Hpk k r := by
    rw [hi]
    simp only [mul_assoc, hpk_hh, Hpk_sq, mul_one]
  have h2 : (s⁻¹)ᴴ = Hpk k r * s * Hpk k r := by
    rw [hi, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm]
    simp only [mul_assoc]
  rw [hpk_inv, conjTranspose_mul, conjTranspose_mul, h2, h1]
  simp only [mul_assoc, hpk_hh, Hpk_sq, mul_one]

lemma hpart1_conj {s : Mx k r} (hs : s ∈ UH (Hpk k r)) (Z : Mx k r) :
    hpart1 (Hpk k r) (s⁻¹ * Z * s) = s⁻¹ * hpart1 (Hpk k r) Z * s := by
  unfold hpart1
  rw [conj_part hs Z]
  simp only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_assoc]

lemma hpart2_conj {s : Mx k r} (hs : s ∈ UH (Hpk k r)) (Z : Mx k r) :
    hpart2 (Hpk k r) (s⁻¹ * Z * s) = s⁻¹ * hpart2 (Hpk k r) Z * s := by
  unfold hpart2
  rw [conj_part hs Z]
  simp only [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_assoc]

lemma exp_conj_mem {i : Fin (r + 1)} {s : Mx k r} (hs : s ∈ Glev k r i) {X : Mx k r}
    (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • (s⁻¹ * X * s)) ∈ Glev k r i := by
  have hu := glev_unit hs
  have hU : IsUnit s := ⟨⟨s, s⁻¹, hu.1, hu.2⟩, rfl⟩
  rw [show ((t : ℂ) • (s⁻¹ * X * s)) = s⁻¹ * ((t : ℂ) • X) * s by rw [mul_smul_comm, smul_mul_assoc],
    Matrix.exp_conj' _ _ hU]
  exact glev_mul' (glev_mul' (glev_inv hs) (hX t)) hs

lemma hpart1_add (Z W : Mx k r) :
    hpart1 (Hpk k r) (Z + W) = hpart1 (Hpk k r) Z + hpart1 (Hpk k r) W := by
  unfold hpart1
  rw [conjTranspose_add, mul_add, add_mul, ← smul_add]
  congr 1
  abel

lemma hpart2_add (Z W : Mx k r) :
    hpart2 (Hpk k r) (Z + W) = hpart2 (Hpk k r) Z + hpart2 (Hpk k r) W := by
  unfold hpart2
  rw [conjTranspose_add, mul_add, add_mul, ← smul_add]
  congr 1
  abel

lemma hpart1_real (a : ℝ) (Z : Mx k r) :
    hpart1 (Hpk k r) ((a : ℂ) • Z) = (a : ℂ) • hpart1 (Hpk k r) Z := by
  unfold hpart1
  have hst : star (a : ℂ) = a := Complex.conj_ofReal a
  rw [conjTranspose_smul, hst, mul_smul_comm, smul_mul_assoc, ← smul_sub, smul_comm]

lemma hpart2_real (a : ℝ) (Z : Mx k r) :
    hpart2 (Hpk k r) ((a : ℂ) • Z) = (a : ℂ) • hpart2 (Hpk k r) Z := by
  unfold hpart2
  have hst : star (a : ℂ) = a := Complex.conj_ofReal a
  rw [conjTranspose_smul, hst, mul_smul_comm, smul_mul_assoc, ← smul_add, smul_comm]

lemma hpart1_I (Z : Mx k r) : hpart1 (Hpk k r) (Complex.I • Z) = -hpart2 (Hpk k r) Z := by
  unfold hpart1 hpart2
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hc : (1 / (2 * Complex.I) : ℂ) = -((1 / 2 : ℂ) * Complex.I) := by
    rw [one_div, mul_inv, Complex.inv_I]; ring
  rw [conjTranspose_smul, hI, hc]
  simp only [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, neg_smul, smul_add, smul_sub, smul_neg, smul_smul,
    neg_add, neg_neg, sub_neg_eq_add]

lemma hpart2_I (Z : Mx k r) : hpart2 (Hpk k r) (Complex.I • Z) = hpart1 (Hpk k r) Z := by
  unfold hpart1 hpart2
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hc2 : (1 / (2 * Complex.I) : ℂ) * Complex.I = 1 / 2 := by
    rw [one_div, mul_inv, Complex.inv_I]
    linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  rw [conjTranspose_smul, hI]
  simp only [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, neg_smul, smul_add, smul_sub, smul_neg, smul_smul,
    ← sub_eq_add_neg, hc2]

section abelian₂

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def lam (Φ : Mx k r →L[ℝ] E) (g Z : Mx k r) : E :=
  Φ (g * hpart1 (Hpk k r) Z) + Complex.I • Φ (g * hpart2 (Hpk k r) Z)

lemma real_smul_mx (a : ℝ) (N : Mx k r) : (a : ℂ) • N = a • N := by
  ext i j
  simp [Complex.real_smul]

lemma lam_add (Φ : Mx k r →L[ℝ] E) (g Z W : Mx k r) : lam Φ g (Z + W) = lam Φ g Z + lam Φ g W := by
  unfold lam
  rw [hpart1_add, hpart2_add, mul_add, mul_add, map_add, map_add, smul_add]
  abel

lemma lam_real (Φ : Mx k r →L[ℝ] E) (g Z : Mx k r) (a : ℝ) :
    lam Φ g ((a : ℂ) • Z) = (a : ℂ) • lam Φ g Z := by
  unfold lam
  rw [hpart1_real, hpart2_real, mul_smul_comm, mul_smul_comm, real_smul_mx, real_smul_mx, map_smul, map_smul,
    ← Complex.coe_smul, ← Complex.coe_smul, smul_add, smul_comm Complex.I]

lemma lam_I (Φ : Mx k r →L[ℝ] E) (g Z : Mx k r) :
    lam Φ g (Complex.I • Z) = Complex.I • lam Φ g Z := by
  unfold lam
  rw [hpart1_I, hpart2_I, mul_neg, map_neg, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel

lemma lam_smul (Φ : Mx k r →L[ℝ] E) (g Z : Mx k r) (c : ℂ) :
    lam Φ g (c • Z) = c • lam Φ g Z := by
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  rw [hc, add_smul, lam_add, mul_smul, lam_real, lam_real, lam_I, add_smul, mul_smul]

def lamL (Φ : Mx k r →L[ℝ] E) (g : Mx k r) : Mx k r →ₗ[ℂ] E where
  toFun := lam Φ g
  map_add' := lam_add Φ g
  map_smul' c Z := lam_smul Φ g Z c

end abelian₂

theorem transfer_invariance_right : StepRight := by
  intro E _ _ k r i D a b f s' g hD hf hs' hg hgs
  have hgs'G : g * s' ∈ Glev k r i := glev_mul' hg hs'
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (g * s') ⟨hgs'G, hgs⟩
  have hu := glev_unit hs'
  have hiG := glev_inv hs'
  have hsU : s' ∈ UH (Hpk k r) := by
    have h0 := hs'
    simp only [Glev, Set.mem_setOf_eq] at h0
    exact h0.1
  have hEH : ∀ Z : Mx k r, (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • hpart1 (Hpk k r) Z) ∈ Glev k r i) →
      (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • hpart2 (Hpk k r) Z) ∈ Glev k r i) →
      RdV (hpart1 (Hpk k r) Z) f (g * s') + Complex.I • RdV (hpart2 (Hpk k r) Z) f (g * s') =
        lam (fderiv ℝ F (g * s')) (g * s') Z := by
    intro Z h1 h2
    rw [rdV_ext i _ h1 f F U (g * s') hU hgU hgs'G hF hfF, rdV_ext i _ h2 f F U (g * s') hU hgU hgs'G hF hfF]
    rfl
  have hinj : ∀ c c' : Fin (mdim k r i), posL k r i c = posL k r i c' ↔ c = c' :=
    fun c c' => ⟨posL_inj, congrArg _⟩
  have hconj : s'⁻¹ * Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) * s' =
      ∑ c, ∑ d, (blk i s'⁻¹ c a * blk i s' b d) • Matrix.single (posL k r i c) (posL k r i d) (1 : ℂ) := by
    ext x y
    have hL : (s'⁻¹ * Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) * s') x y =
        s'⁻¹ x (posL k r i a) * s' (posL k r i b) y := by
      simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_mul]
    rw [hL]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, blk]
    by_cases hx : ∃ c, posL k r i c = x
    · by_cases hy : ∃ d, posL k r i d = y
      · obtain ⟨c0, rfl⟩ := hx
        obtain ⟨d0, rfl⟩ := hy
        simp [hinj, ite_and]
      · push_neg at hy
        have h0 : s' (posL k r i b) y = 0 := by
          rw [glev_col hs' _ y (fun d e => hy d e.symm), (bvec_posL_outer b y (fun d e => hy d e.symm)).1]
        simp [h0, hy]
    · push_neg at hx
      have h0 : s'⁻¹ x (posL k r i a) = 0 := by
        rw [glev_row' hiG x _ (fun c e => hx c e.symm), (bvec_posL_outer a x (fun c e => hx c e.symm)).2]
      simp [h0, hx]
  calc EH k r (posL k r i a) (posL k r i b) (fun x => f (x * s')) g
      = lam (fderiv ℝ F (g * s')) (g * s') (s'⁻¹ * Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) * s') := by
        show RdV _ (fun x => f (x * s')) g + Complex.I • RdV _ (fun x => f (x * s')) g = _
        rw [rdV_right _ _ _ _ hu.1 hu.2, rdV_right _ _ _ _ hu.1 hu.2, ← hpart1_conj hsU, ← hpart2_conj hsU]
        exact hEH _ (fun t => by rw [hpart1_conj hsU]; exact exp_conj_mem hs' (exp_hpart1_mem i a b) t)
          (fun t => by rw [hpart2_conj hsU]; exact exp_conj_mem hs' (exp_hpart2_mem i a b) t)
    _ = ∑ c, ∑ d, (blk i s'⁻¹ c a * blk i s' b d) •
          lam (fderiv ℝ F (g * s')) (g * s') (Matrix.single (posL k r i c) (posL k r i d) (1 : ℂ)) := by
        rw [hconj]
        change lamL (fderiv ℝ F (g * s')) (g * s')
          (∑ c, ∑ d, (blk i s'⁻¹ c a * blk i s' b d) • Matrix.single (posL k r i c) (posL k r i d) (1 : ℂ)) = _
        simp only [map_sum, map_smul]
        rfl
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [← hEH _ (exp_hpart1_mem i c d) (exp_hpart2_mem i c d)]
        rfl

end Formalism.FourierDecayAlt.Q.TInvW

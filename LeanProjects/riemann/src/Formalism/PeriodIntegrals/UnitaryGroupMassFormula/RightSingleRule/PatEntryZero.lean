import Formalism.HermitianCurvature.StatementQ
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace Formalism.FourierDecayAlt.Q.QRR

variable {k r : ℕ}

def Pat (k r : ℕ) (l : Fin r) (Z : Mx k r) : Prop :=
  ∀ i j : Fin (2 * r + k + 1), Z i j ≠ 0 →
    (i.val = l.val ∧ l.val < j.val ∧ j.val ≤ 2 * r + k - l.val) ∨
    (j.val = 2 * r + k - l.val ∧ l.val ≤ i.val ∧ i.val < 2 * r + k - l.val)

def dag (k r : ℕ) (Z : Mx k r) : Mx k r := (Hpk k r)⁻¹ * Zᴴ * Hpk k r

lemma hpk_inv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv (hermitian_pos_facts_hold k r).2.1

lemma mul_hpk_apply (A : Mx k r) (i j : Fin (2 * r + k + 1)) :
    (A * Hpk k r) i j = A i (WeylGroupFacts.tau k r j) * WeylGroupFacts.sgn k r j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (WeylGroupFacts.tau k r j)]
  · congr 1
    have := j.isLt
    simp only [Hpk, WeylGroupFacts.tau, WeylGroupFacts.sgn, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | rfl | (exfalso; omega) | norm_num
  · intro b _ hb
    have hb' : b.val ≠ (WeylGroupFacts.tau k r j).val := fun e => hb (Fin.ext e)
    have := j.isLt
    have := b.isLt
    simp only [WeylGroupFacts.tau, Fin.val_mk] at hb'
    have h0 : Hpk k r b j = 0 := by
      simp only [Hpk, Fin.ext_iff]
      split_ifs at hb' ⊢ <;> first | rfl | (exfalso; omega)
    rw [h0, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma hpk_mul_lemma (A : Mx k r) (i j : Fin (2 * r + k + 1)) :
    (Hpk k r * A) i j = WeylGroupFacts.sgn k r i * A (WeylGroupFacts.tau k r i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (WeylGroupFacts.tau k r i)]
  · congr 1
    have := i.isLt
    simp only [Hpk, WeylGroupFacts.tau, WeylGroupFacts.sgn, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | rfl | (exfalso; omega) | norm_num
  · intro b _ hb
    have hb' : b.val ≠ (WeylGroupFacts.tau k r i).val := fun e => hb (Fin.ext e)
    have := i.isLt
    have := b.isLt
    simp only [WeylGroupFacts.tau, Fin.val_mk] at hb'
    have h0 : Hpk k r i b = 0 := by
      simp only [Hpk, Fin.ext_iff]
      split_ifs at hb' ⊢ <;> first | rfl | (exfalso; omega)
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma dag_apply (Z : Mx k r) (i j : Fin (2 * r + k + 1)) :
    dag k r Z i j = WeylGroupFacts.sgn k r i * star (Z (WeylGroupFacts.tau k r j) (WeylGroupFacts.tau k r i)) * WeylGroupFacts.sgn k r j := by
  unfold dag
  rw [hpk_inv, mul_hpk_apply, hpk_mul_lemma, Matrix.conjTranspose_apply]

lemma tau_val (i : Fin (2 * r + k + 1)) :
    (WeylGroupFacts.tau k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := rfl

lemma pat_dag {l : Fin r} {Z : Mx k r} (hZ : Pat k r l Z) : Pat k r l (dag k r Z) := by
  intro i j h
  rw [dag_apply] at h
  have hZ' : Z (WeylGroupFacts.tau k r j) (WeylGroupFacts.tau k r i) ≠ 0 := by
    intro h0
    apply h
    rw [h0, star_zero, mul_zero, zero_mul]
  have hp := hZ _ _ hZ'
  rw [tau_val, tau_val] at hp
  have := l.isLt
  have := i.isLt
  have := j.isLt
  split_ifs at hp <;> omega

lemma pat_add {l : Fin r} {A B : Mx k r} (hA : Pat k r l A) (hB : Pat k r l B) : Pat k r l (A + B) := by
  intro i j h
  by_cases hA' : A i j = 0
  · apply hB
    intro h0
    apply h
    rw [Matrix.add_apply, hA', h0, add_zero]
  · exact hA i j hA'

lemma pat_smul {l : Fin r} {A : Mx k r} (c : ℂ) (hA : Pat k r l A) : Pat k r l (c • A) := by
  intro i j h
  apply hA
  intro h0
  apply h
  rw [Matrix.smul_apply, h0, smul_zero]

lemma pat_neg {l : Fin r} {A : Mx k r} (hA : Pat k r l A) : Pat k r l (-A) := by
  intro i j h
  apply hA
  intro h0
  apply h
  rw [Matrix.neg_apply, h0, neg_zero]

lemma pat_sub {l : Fin r} {A B : Mx k r} (hA : Pat k r l A) (hB : Pat k r l B) : Pat k r l (A - B) := by
  intro i j h
  by_cases hA' : A i j = 0
  · apply hB
    intro h0
    apply h
    rw [Matrix.sub_apply, hA', h0, sub_zero]
  · exact hA i j hA'

lemma pat_entry_zero {l : Fin r} {Y : Mx k r} (hY : Pat k r l Y) (i j : Fin (2 * r + k + 1))
    (h : ¬ ((i.val = l.val ∧ l.val < j.val ∧ j.val ≤ 2 * r + k - l.val) ∨
      (j.val = 2 * r + k - l.val ∧ l.val ≤ i.val ∧ i.val < 2 * r + k - l.val))) : Y i j = 0 := by
  by_contra h0
  exact h (hY i j h0)

lemma pat_sq_apply {l : Fin r} {Y : Mx k r} (hY : Pat k r l Y) (i j : Fin (2 * r + k + 1))
    (h : ¬ (i.val = l.val ∧ j.val = 2 * r + k - l.val)) : (Y * Y) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro m _
  by_cases h1 : Y i m = 0
  · rw [h1, zero_mul]
  · by_cases h2 : Y m j = 0
    · rw [h2, mul_zero]
    · exfalso
      have e1 := hY i m h1
      have e2 := hY m j h2
      have := l.isLt
      omega

lemma pat_cube {l : Fin r} {Y : Mx k r} (hY : Pat k r l Y) : Y ^ 3 = 0 := by
  ext i j
  rw [pow_three', Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro m _
  by_cases h1 : i.val = l.val ∧ m.val = 2 * r + k - l.val
  · have h2 : Y m j = 0 := by
      by_contra h0
      have e := hY m j h0
      have := l.isLt
      omega
    rw [h2, mul_zero]
  · rw [pat_sq_apply hY i m h1, zero_mul]

lemma exp_of_cube {Y : Mx k r} (h3 : Y ^ 3 = 0) :
    NormedSpace.exp Y = 1 + Y + (1 / 2 : ℂ) • (Y * Y) := by
  have h3' : ∀ n, 3 ≤ n → Y ^ n = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add, h3, zero_mul]
  have hz : ∀ n ∉ Finset.range 3, ((n.factorial : ℂ))⁻¹ • Y ^ n = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [h3' n hn, smul_zero]
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  dsimp only
  rw [tsum_eq_sum hz]
  simp [Finset.sum_range_succ, Nat.factorial, sq, one_div]

lemma dag_smul (c : ℂ) (A : Mx k r) : dag k r (c • A) = star c • dag k r A := by
  unfold dag
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]

lemma dag_add (A B : Mx k r) : dag k r (A + B) = dag k r A + dag k r B := by
  unfold dag
  rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

lemma dag_sub (A B : Mx k r) : dag k r (A - B) = dag k r A - dag k r B := by
  unfold dag
  rw [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]

lemma dag_dag (A : Mx k r) : dag k r (dag k r A) = A := by
  have h2 : Hpk k r * Hpk k r = 1 := (hermitian_pos_facts_hold k r).2.1
  have h2' : ∀ M : Mx k r, Hpk k r * (Hpk k r * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hH : (Hpk k r)ᴴ = Hpk k r := (hermitian_pos_facts_hold k r).1
  unfold dag
  rw [hpk_inv]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH, Matrix.mul_assoc, h2', h2,
    Matrix.mul_one]

lemma star_half : star (1 / 2 : ℂ) = 1 / 2 := by
  first | simp | (rw [Complex.star_def]; simp)

lemma star_inv2I : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
  rw [Complex.star_def, map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat]
  ring

lemma skew_hpart1 (Z : Mx k r) : dag k r (hpart1 (Hpk k r) Z) = -hpart1 (Hpk k r) Z := by
  have e : hpart1 (Hpk k r) Z = (1 / 2 : ℂ) • (Z - dag k r Z) := rfl
  rw [e, dag_smul, dag_sub, dag_dag, star_half, ← smul_neg, neg_sub]

lemma skew_hpart2 (Z : Mx k r) : dag k r (hpart2 (Hpk k r) Z) = -hpart2 (Hpk k r) Z := by
  have e : hpart2 (Hpk k r) Z = (1 / (2 * Complex.I) : ℂ) • (Z + dag k r Z) := rfl
  rw [e, dag_smul, dag_add, dag_dag, star_inv2I, neg_smul, add_comm (dag k r Z) Z]

lemma pat_hpart1 {l : Fin r} {Z : Mx k r} (hZ : Pat k r l Z) : Pat k r l (hpart1 (Hpk k r) Z) :=
  pat_smul (1 / 2 : ℂ) (pat_sub hZ (pat_dag hZ))

lemma pat_hpart2 {l : Fin r} {Z : Mx k r} (hZ : Pat k r l Z) : Pat k r l (hpart2 (Hpk k r) Z) :=
  pat_smul (1 / (2 * Complex.I) : ℂ) (pat_add hZ (pat_dag hZ))

lemma mulVec_bvec (M : Mx k r) (c : Fin (2 * r + k + 1)) : M *ᵥ bvec c = fun i => M i c := by
  funext p
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

private lemma gent_lemma_2 {l : Fin r} {Y : Mx k r} (hY : Pat k r l Y) (i j : Fin (2 * r + k + 1))
    (h1 : ¬ ((i.val = l.val ∧ l.val < j.val ∧ j.val ≤ 2 * r + k - l.val) ∨
      (j.val = 2 * r + k - l.val ∧ l.val ≤ i.val ∧ i.val < 2 * r + k - l.val)))
    (h2 : ¬ (i.val = l.val ∧ j.val = 2 * r + k - l.val)) :
    (1 + Y + (1 / 2 : ℂ) • (Y * Y)) i j = (1 : Mx k r) i j := by
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, pat_entry_zero hY i j h1,
    pat_sq_apply hY i j h2, smul_zero, add_zero, add_zero]

lemma exp_mem_nlev {l : Fin r} {Y : Mx k r} (hY : Pat k r l Y) (hS : dag k r Y = -Y) :
    NormedSpace.exp Y ∈ Nlev k r l.castSucc := by
  have h2 : Hpk k r * Hpk k r = 1 := (hermitian_pos_facts_hold k r).2.1
  have h2' : ∀ M : Mx k r, Hpk k r * (Hpk k r * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hYc : Yᴴ = Hpk k r * (-Y) * Hpk k r := by
    have e : (Hpk k r)⁻¹ * Yᴴ * Hpk k r = -Y := hS
    rw [hpk_inv] at e
    calc Yᴴ = Hpk k r * (Hpk k r * Yᴴ * Hpk k r) * Hpk k r := by
          simp only [Matrix.mul_assoc, h2', h2, Matrix.mul_one]
      _ = _ := by rw [e]
  have hU : IsUnit (Hpk k r) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h2)
  have hc := Matrix.exp_conj (Hpk k r) (-Y) hU
  rw [hpk_inv] at hc
  have hUH : NormedSpace.exp Y ∈ UH (Hpk k r) := by
    show (NormedSpace.exp Y)ᴴ * Hpk k r * NormedSpace.exp Y = Hpk k r
    rw [← Matrix.exp_conjTranspose, hYc, hc,
      Matrix.mul_assoc (Hpk k r * NormedSpace.exp (-Y)) (Hpk k r) (Hpk k r), h2, Matrix.mul_one,
      Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)),
      neg_add_cancel, NormedSpace.exp_zero, Matrix.mul_one]
  rw [exp_of_cube (pat_cube hY)] at hUH ⊢
  have hl := l.isLt
  refine ⟨⟨hUH, fun a i hai => ?_, fun i j hj1 hj2 hi => ?_⟩, hUH, fun a ha => ⟨?_, ?_⟩⟩
  · have ha := a.isLt
    have e1 : (eI k r a).val = a.val := rfl
    rw [gent_lemma_2 hY _ _ (by rw [e1]; omega) (by rw [e1]; omega)]
    exact Matrix.one_apply
  · rw [gent_lemma_2 hY _ _ (by omega) (by omega)]
    exact Matrix.one_apply
  · have ha' : a.val < l.val := ha
    have ha2 := a.isLt
    have e1 : (eI k r a).val = a.val := rfl
    rw [mulVec_bvec]
    funext p
    rw [gent_lemma_2 hY _ _ (by rw [e1]; omega) (by rw [e1]; omega)]
    simp [bvec, Pi.single_apply, Matrix.one_apply]
  · have ha' : a.val < l.val := ha
    have ha2 := a.isLt
    have e1 : (esI k r a).val = 2 * r + k - a.val := rfl
    rw [mulVec_bvec]
    funext p
    rw [gent_lemma_2 hY _ _ (by rw [e1]; omega) (by rw [e1]; omega)]
    simp [bvec, Pi.single_apply, Matrix.one_apply]

lemma ell_add (z : Fin (2 * r + k + 1) → ℂ) (A B : Mx k r) :
    ell k r z (A + B) = ell k r z A + ell k r z B := by
  unfold ell
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp [Matrix.add_mulVec]

lemma ell_smul (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (A : Mx k r) :
    ell k r z (c • A) = c * ell k r z A := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp [Matrix.smul_mulVec]

lemma ell_rsmul (z : Fin (2 * r + k + 1) → ℂ) (c : ℝ) (A : Mx k r) :
    ell k r z (c • A) = (c : ℂ) * ell k r z A := by
  rw [← ell_smul, Complex.coe_smul]

lemma ell_one (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) : ell k r z 1 = 0 := by
  unfold ell
  apply Finset.sum_eq_zero
  intro a _
  split_ifs with h
  · apply Matrix.one_apply_ne
    intro he
    have := congrArg Fin.val he
    have e1 : (eI k r a).val = a.val := rfl
    have e2 : (eI k r ⟨a.val + 1, h⟩).val = a.val + 1 := rfl
    rw [e1, e2] at this
    omega
  · rw [Matrix.one_mulVec]
    exact hz _ (Or.inl a.isLt)

def ellL (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Mx k r →ₗ[ℝ] ℂ where
  toFun := ell k r z
  map_add' := ell_add z
  map_smul' c A := by rw [ell_rsmul, RingHom.id_apply, Complex.real_smul]

lemma hasDerivAt_psi (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (X : Mx k r) :
    HasDerivAt (fun t : ℝ => psi k r z cStd (NormedSpace.exp ((t : ℂ) • X)))
      (ell k r z X - star (ell k r z X)) 0 := by
  have hE := Formalism.REAL.hasDerivAt_matrix_exp_smul_at_zero X
  have hL : HasDerivAt (fun t : ℝ => ell k r z (NormedSpace.exp ((t : ℂ) • X))) (ell k r z X) 0 := by
    have := (LinearMap.toContinuousLinearMap (ellL k r z)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hE
    exact this
  have hre : HasDerivAt (fun t : ℝ => (cStd * ell k r z (NormedSpace.exp ((t : ℂ) • X))).re)
      (cStd * ell k r z X).re 0 := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hL.const_mul cStd)
    exact this
  have h1 := ((hre.ofReal_comp).const_mul Complex.I).cexp
  unfold psi
  convert h1 using 1
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, ell_one z hz, mul_zero, Complex.zero_re,
    Complex.exp_zero, one_mul]
  unfold cStd
  rw [Complex.star_def]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

lemma rdV_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z) (l : Fin r) (D : Set (Mx k r)) (f : Mx k r → E) (hR : RightEq k r z l.castSucc D f)
    (g : Mx k r) (hg : g ∈ Glev k r l.castSucc ∩ D) (X : Mx k r) (hX : Pat k r l X) (hS : dag k r X = -X) :
    RdV X f g = (ell k r z X - star (ell k r z X)) • f g := by
  have hfun : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => psi k r z cStd (NormedSpace.exp ((t : ℂ) • X)) • f g := by
    funext t
    apply hR g hg
    apply exp_mem_nlev (pat_smul _ hX)
    rw [dag_smul, hS, Complex.star_def, Complex.conj_ofReal, smul_neg]
  show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 = _
  rw [hfun]
  exact ((hasDerivAt_psi z hz X).smul_const (f g)).deriv

theorem lam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z) (l : Fin r) (D : Set (Mx k r)) (f : Mx k r → E) (hR : RightEq k r z l.castSucc D f)
    (g : Mx k r) (hg : g ∈ Glev k r l.castSucc ∩ D) (Z : Mx k r) (hZ : Pat k r l Z) :
    RdV (hpart1 (Hpk k r) Z) f g + Complex.I • RdV (hpart2 (Hpk k r) Z) f g =
      (ell k r z Z + star (ell k r z (dag k r Z))) • f g := by
  have hP := skew_hpart1 Z
  have hQ := skew_hpart2 Z
  have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    have := Complex.I_ne_zero
    field_simp
    try ring
  have hZ1 : Z = hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z := by
    unfold hpart1 hpart2
    rw [smul_smul, hI]
    module
  have hZ2 : dag k r Z = -hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z := by
    conv_lhs => rw [hZ1]
    rw [dag_add, dag_smul, hP, hQ, Complex.star_def, Complex.conj_I, neg_smul, smul_neg, neg_neg]
  have hE : ell k r z Z = ell k r z (hpart1 (Hpk k r) Z) + Complex.I * ell k r z (hpart2 (Hpk k r) Z) := by
    conv_lhs => rw [hZ1]
    rw [ell_add, ell_smul]
  have hE2 : ell k r z (dag k r Z) =
      -ell k r z (hpart1 (Hpk k r) Z) + Complex.I * ell k r z (hpart2 (Hpk k r) Z) := by
    rw [hZ2, show -hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z =
      (-1 : ℂ) • hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z by rw [neg_one_smul],
      ell_add, ell_smul, ell_smul]
    ring
  rw [rdV_eq z hz l D f hR g hg _ (pat_hpart1 hZ) hP, rdV_eq z hz l D f hR g hg _ (pat_hpart2 hZ) hQ,
    hE, hE2, smul_smul, ← add_smul]
  congr 1
  rw [Complex.star_def]
  simp only [map_add, map_mul, map_neg, Complex.conj_I]
  ring

end Formalism.FourierDecayAlt.Q.QRR

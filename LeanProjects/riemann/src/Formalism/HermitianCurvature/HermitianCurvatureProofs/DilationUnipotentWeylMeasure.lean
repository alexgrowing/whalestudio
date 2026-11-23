import Formalism.HermitianCurvature.StatementB
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul

open Matrix Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.B4

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable def dg (k r : ℕ) (t : ℝ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then ((t ^ (r - i.val) : ℝ) : ℂ)
    else if i.val ≤ r + k then 1 else (((t ^ (i.val - (r + k)))⁻¹ : ℝ) : ℂ)

lemma aDil_eq (k r : ℕ) (t : ℝ) : aDil k r t = Matrix.diagonal (dg k r t) := rfl

lemma dg_mid (k r : ℕ) (t : ℝ) (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) :
    dg k r t i = 1 := by
  unfold dg
  rw [if_neg (by omega), if_pos h2]

lemma dg_mul_inv (k r : ℕ) (t : ℝ) (ht : t ≠ 0) (i : Fin (2 * r + k + 1)) :
    dg k r t i * dg k r t⁻¹ i = 1 := by
  unfold dg
  split_ifs with h1 h2
  · rw [← Complex.ofReal_mul, ← mul_pow, mul_inv_cancel₀ ht, one_pow, Complex.ofReal_one]
  · rw [one_mul]
  · rw [← Complex.ofReal_mul, inv_pow, inv_inv, inv_mul_cancel₀ (pow_ne_zero _ ht), Complex.ofReal_one]

theorem aDil_inv (k r : ℕ) (t : ℝ) (ht : t ≠ 0) : (aDil k r t)⁻¹ = aDil k r t⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [aDil_eq, aDil_eq, Matrix.diagonal_mul_diagonal]
  have e : (fun i => dg k r t⁻¹ i * dg k r t i) = fun _ => (1 : ℂ) := by
    funext i
    rw [mul_comm]
    exact dg_mul_inv k r t ht i
  rw [e, Matrix.diagonal_one]

private lemma dg_pair_lemma (k r : ℕ) (t : ℝ) (ht : t ≠ 0) (i j : Fin (2 * r + k + 1))
    (hi : i.val < r) (hij : i.val + j.val = 2 * r + k) : dg k r t i * dg k r t j = 1 := by
  have hj1 : ¬ j.val < r := by omega
  have hj2 : ¬ j.val ≤ r + k := by omega
  have e : j.val - (r + k) = r - i.val := by omega
  unfold dg
  rw [if_pos hi, if_neg hj1, if_neg hj2, e, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (pow_ne_zero _ ht), Complex.ofReal_one]

theorem aDil_mem (k r : ℕ) (t : ℝ) (ht : t ≠ 0) : aDil k r t ∈ GV k r := by
  show (aDil k r t)ᴴ * Hpk k r * aDil k r t = Hpk k r
  have hs : ∀ l, star (dg k r t l) = dg k r t l := by
    intro l
    unfold dg
    split_ifs <;> simp
  have hD : (Matrix.diagonal (dg k r t))ᴴ = Matrix.diagonal (dg k r t) := by
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      exact hs i
    · rw [if_neg (Ne.symm h), if_neg h, star_zero]
  rw [aDil_eq, hD]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk
  split_ifs with h1 h2 h3 h4
  · rw [mul_one, dg_pair_lemma k r t ht i j h1.1 h1.2]
  · rw [mul_one, mul_comm, dg_pair_lemma k r t ht j i h2.1 (by omega)]
  · obtain ⟨ha, hb, rfl⟩ := h3
    rw [dg_mid k r t i ha hb]
    simp
  · obtain ⟨ha, hb, rfl⟩ := h3
    rw [dg_mid k r t i ha hb]
    simp
  · rw [mul_zero, zero_mul]

lemma conj_apply (k r : ℕ) (t : ℝ) (ht : t ≠ 0) (n : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (aDil k r t * n * (aDil k r t)⁻¹) i j = dg k r t i * n i j * dg k r t⁻¹ j := by
  rw [aDil_inv k r t ht, aDil_eq, aDil_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]

lemma dg_step (k r : ℕ) (t : ℝ) (ht : t ≠ 0) (a : Fin r) (h : a.val + 1 < r) :
    dg k r t (eI k r a) * dg k r t⁻¹ (eI k r ⟨a.val + 1, h⟩) = (t : ℂ) := by
  have e : r - a.val = (r - (a.val + 1)) + 1 := by omega
  simp only [dg, eI, Fin.is_lt, h, ↓reduceIte]
  rw [← Complex.ofReal_mul, e, pow_succ, inv_pow]
  congr 1
  rw [mul_comm (t ^ _) t, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht), mul_one]

lemma dg_last (k r : ℕ) (t : ℝ) (a : Fin r) (h : ¬ a.val + 1 < r) :
    dg k r t (eI k r a) = (t : ℂ) := by
  have e : r - a.val = 1 := by have := a.isLt; omega
  simp only [dg, eI, Fin.is_lt, ↓reduceIte, e, pow_one]

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma inLie_zero : inLie k r (0 : Mat k r) := by
  unfold inLie
  simp

lemma inLie_add {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) : inLie k r (X + Y) := by
  unfold inLie at *
  rw [Matrix.conjTranspose_add, add_mul, mul_add]
  calc _ = (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
    _ = 0 := by rw [hX, hY, add_zero]

lemma inLie_rsmul {X : Mat k r} (hX : inLie k r X) (c : ℝ) : inLie k r ((c : ℂ) • X) := by
  unfold inLie at *
  have hc : star (c : ℂ) = (c : ℂ) := Complex.conj_ofReal c
  rw [Matrix.conjTranspose_smul, hc, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

lemma inLie_neg {X : Mat k r} (hX : inLie k r X) : inLie k r (-X) := by
  unfold inLie at *
  rw [Matrix.conjTranspose_neg, neg_mul, mul_neg, ← neg_add, hX, neg_zero]

lemma inLie_sub {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) : inLie k r (X - Y) := by
  rw [sub_eq_add_neg]
  exact inLie_add hX (inLie_neg hY)

private lemma hpk_sq_lemma : Hpk k r * Hpk k r = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.mul_apply, Matrix.one_apply]
  have key : ∀ l : Fin (2 * r + k + 1),
      l.val ≠ (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) →
      Hpk k r i l = 0 := by
    intro l hl
    have hl' := l.isLt
    unfold Hpk
    simp only [Fin.ext_iff]
    split_ifs at hl ⊢ <;> first | rfl | (exfalso; omega)
  rw [Finset.sum_eq_single_of_mem
    ⟨(if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val), by split_ifs <;> omega⟩
    (Finset.mem_univ _)]
  · unfold Hpk
    simp only [Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | norm_num
  · intro l _ hl
    rw [key l (fun h => hl (Fin.ext h)), MulZeroClass.zero_mul]

lemma hpk_inv : (Hpk k r)⁻¹ = Hpk k r := by
  exact Matrix.inv_eq_left_inv hpk_sq_lemma

lemma hpk_isUnit : IsUnit (Hpk k r) := by
  exact ⟨⟨Hpk k r, Hpk k r, hpk_sq_lemma, hpk_sq_lemma⟩, rfl⟩

lemma exp_mem {Y : Mat k r} (hY : inLie k r Y) : NormedSpace.exp Y ∈ GV k r := by
  have hU : IsUnit (Hpk k r) := hpk_isUnit
  have hHH : Hpk k r * Hpk k r = 1 := by
    calc Hpk k r * Hpk k r = Hpk k r * (Hpk k r)⁻¹ := by rw [hpk_inv]
      _ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  have hY' : Yᴴ = Hpk k r * (-Y) * (Hpk k r)⁻¹ := by
    have h1 : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left hY
    rw [hpk_inv]
    calc Yᴴ = Yᴴ * (Hpk k r * Hpk k r) := by rw [hHH, Matrix.mul_one]
      _ = Yᴴ * Hpk k r * Hpk k r := by rw [Matrix.mul_assoc]
      _ = Hpk k r * (-Y) * Hpk k r := by rw [h1, _root_.neg_mul, _root_.mul_neg, _root_.neg_mul]
  show (NormedSpace.exp Y)ᴴ * Hpk k r * NormedSpace.exp Y = Hpk k r
  rw [← Matrix.exp_conjTranspose, hY', Matrix.exp_conj _ _ hU, hpk_inv]
  have hE : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)),
      show -Y + Y = (0 : Mat k r) by abel, NormedSpace.exp_zero]
  calc Hpk k r * NormedSpace.exp (-Y) * Hpk k r * Hpk k r * NormedSpace.exp Y
      = Hpk k r * (NormedSpace.exp (-Y) * (Hpk k r * Hpk k r) * NormedSpace.exp Y) := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [hHH, Matrix.mul_one, hE, Matrix.mul_one]

def cv (b : Bool) (X : Mat k r) (t : ℝ) (g : Mat k r) : Mat k r :=
  match b with
  | true => NormedSpace.exp (-((t : ℂ) • X)) * g
  | false => g * NormedSpace.exp ((t : ℂ) • X)

def op (b : Bool) (X : Mat k r) (f : Mat k r → E) : Mat k r → E :=
  fun g => deriv (fun t : ℝ => f (cv b X t g)) 0

lemma op_true (X : Mat k r) (f : Mat k r → E) : op true X f = LdV X f := rfl

lemma op_false (X : Mat k r) (f : Mat k r → E) : op false X f = RdV X f := rfl

def mulL (X : Mat k r) : Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)

def mulR (X : Mat k r) : Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

lemma mulL_apply (X g : Mat k r) : mulL X g = X * g := rfl

lemma mulR_apply (X g : Mat k r) : mulR X g = g * X := rfl

def vf (b : Bool) (X : Mat k r) : Mat k r →L[ℝ] Mat k r :=
  match b with
  | true => -(mulL X)
  | false => mulR X

lemma vf_true (X g : Mat k r) : vf true X g = -(X * g) := rfl

lemma vf_false (X g : Mat k r) : vf false X g = g * X := rfl

lemma cv_zero (b : Bool) (X g : Mat k r) : cv b X 0 g = g := by
  cases b <;> simp [cv]

private lemma gv_mul_lemma {a c : Mat k r} (ha : a ∈ GV k r) (hc : c ∈ GV k r) : a * c ∈ GV k r := by
  show (a * c)ᴴ * Hpk k r * (a * c) = Hpk k r
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hc' : cᴴ * Hpk k r * c = Hpk k r := hc
  rw [Matrix.conjTranspose_mul,
    show cᴴ * aᴴ * Hpk k r * (a * c) = cᴴ * (aᴴ * Hpk k r * a) * c by simp only [Matrix.mul_assoc],
    ha', hc']

lemma cv_mem {b : Bool} {X g : Mat k r} (hX : inLie k r X) (hg : g ∈ GV k r) (t : ℝ) :
    cv b X t g ∈ GV k r := by
  cases b
  · simp only [cv]
    exact gv_mul_lemma hg (exp_mem (inLie_rsmul hX t))
  · simp only [cv]
    exact gv_mul_lemma (exp_mem (inLie_neg (inLie_rsmul hX t))) hg

lemma cv_hasDerivAt (b : Bool) (X g : Mat k r) :
    HasDerivAt (fun t : ℝ => cv b X t g) (vf b X g) 0 := by
  cases b
  · exact hasDerivAt_mul_exp_smul_zero g X
  · have h := hasDerivAt_mul_exp_smul_zero (1 : Mat k r) (-X)
    have h2 := (mulR g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    refine (h2.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    · show (1 * -X) * g = -(X * g)
      simp
    · show NormedSpace.exp (-((t : ℂ) • X)) * g = (1 * NormedSpace.exp ((t : ℂ) • -X)) * g
      simp

lemma cv_add (b : Bool) (X g : Mat k r) (s t : ℝ) : cv b X (s + t) g = cv b X t (cv b X s g) := by
  cases b
  · simp only [cv]
    rw [Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)]
    congr 2
    push_cast
    rw [add_smul]
  · simp only [cv]
    rw [← Matrix.mul_assoc,
      ← Matrix.exp_add_of_commute _ _ ((((Commute.refl X).smul_left _).smul_right _).neg_left.neg_right)]
    congr 2
    push_cast
    rw [add_smul, neg_add, add_comm]

lemma hasDerivAt_ext {f f' : Mat k r → E} {U : Set (Mat k r)} {g X : Mat k r} (b : Bool)
    (hU : IsOpen U) (hg : g ∈ U) (hgG : g ∈ GV k r) (hd : DifferentiableAt ℝ f' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → f h = f' h) (hX : inLie k r X) :
    HasDerivAt (fun t : ℝ => f (cv b X t g)) (fderiv ℝ f' g (vf b X g)) 0 := by
  have hc := cv_hasDerivAt b X g
  have h0 : cv b X 0 g = g := cv_zero b X g
  have hd' : HasFDerivAt f' (fderiv ℝ f' g) (cv b X 0 g) := by
    rw [h0]
    exact hd.hasFDerivAt
  have hcomp := hd'.comp_hasDerivAt 0 hc
  apply hcomp.congr_of_eventuallyEq
  have hcont : ContinuousAt (fun t => cv b X t g) 0 := hc.continuousAt
  have hUn : U ∈ nhds ((fun t => cv b X t g) 0) := by
    show U ∈ nhds (cv b X 0 g)
    rw [h0]
    exact hU.mem_nhds hg
  have hU' : ∀ᶠ t in nhds (0 : ℝ), cv b X t g ∈ U := hcont.preimage_mem_nhds hUn
  filter_upwards [hU'] with t ht
  exact hff _ ht (cv_mem hX hgG t)

lemma natCast_succ_le (m : ℕ) :
    (((m : ℕ) : ℕ∞) : WithTop ℕ∞) + 1 ≤ (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
  first
    | exact le_of_eq (by norm_cast)
    | exact le_of_eq (by simp)
    | simp

lemma one_le_cast (m : ℕ) : (1 : WithTop ℕ∞) ≤ (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
  first
    | exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    | simp

lemma cast_ne_zero (m : ℕ) : (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  first
    | exact_mod_cast Nat.succ_ne_zero m
    | simp

def op' (b : Bool) (X : Mat k r) (f' : Mat k r → E) : Mat k r → E :=
  fun g => fderiv ℝ f' g (vf b X g)

lemma op'_contDiffOn {f' : Mat k r → E} {U : Set (Mat k r)} (m : ℕ) (b : Bool) (X : Mat k r)
    (hU : IsOpen U) (hf : ContDiffOn ℝ (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) f' U) :
    ContDiffOn ℝ (((m : ℕ) : ℕ∞) : WithTop ℕ∞) (op' b X f') U := by
  exact (hf.fderiv_of_isOpen hU (natCast_succ_le m)).clm_apply (vf b X).contDiff.contDiffOn

lemma op_eq_op' {f f' : Mat k r → E} {U : Set (Mat k r)} {X : Mat k r} (m : ℕ) (b : Bool)
    (hU : IsOpen U) (hf : ContDiffOn ℝ (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) f' U)
    (hff : ∀ h ∈ U, h ∈ GV k r → f h = f' h) (hX : inLie k r X) :
    ∀ g ∈ U, g ∈ GV k r → op b X f g = op' b X f' g := by
  intro g hg hgG
  have hd : DifferentiableAt ℝ f' g :=
    (hf.contDiffAt (hU.mem_nhds hg)).differentiableAt (cast_ne_zero m)
  exact (hasDerivAt_ext b hU hg hgG hd hff hX).deriv

lemma ckOn_op {f : Mat k r → E} {X : Mat k r} (m : ℕ) (b : Bool)
    (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) (hX : inLie k r X) :
    CkOn ((m : ℕ) : ℕ∞) (GV k r) (op b X f) := by
  unfold CkOn at *
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g₀ hg₀
  exact ⟨U, op' b X f', hU, hgU, op'_contDiffOn m b X hU hc,
    fun g hg hgG => op_eq_op' m b hU hc hff hX g hg hgG⟩

lemma ckOn_diff {f : Mat k r → E} {X g : Mat k r} (m : ℕ) (b : Bool)
    (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) (hX : inLie k r X) (hg : g ∈ GV k r) :
    DifferentiableAt ℝ (fun t : ℝ => f (cv b X t g)) 0 := by
  unfold CkOn at hf
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g hg
  have hd : DifferentiableAt ℝ f' g :=
    (hc.contDiffAt (hU.mem_nhds hgU)).differentiableAt (cast_ne_zero m)
  exact (hasDerivAt_ext b hU hgU hg hd hff hX).differentiableAt

lemma ckOn_mono {f : Mat k r → E} {m n : ℕ} (h : m ≤ n) (hf : CkOn ((n : ℕ) : ℕ∞) (GV k r) f) :
    CkOn ((m : ℕ) : ℕ∞) (GV k r) f := by
  unfold CkOn at *
  intro g₀ hg
  obtain ⟨U, f', hU, hgU, hc, he⟩ := hf g₀ hg
  exact ⟨U, f', hU, hgU, hc.of_le (by exact_mod_cast h), he⟩

lemma ckOn_add {f f₂ : Mat k r → E} {m : ℕ∞} (hf : CkOn m (GV k r) f) (hf₂ : CkOn m (GV k r) f₂) :
    CkOn m (GV k r) (f + f₂) := by
  unfold CkOn at *
  intro g₀ hg
  obtain ⟨U₁, f₁', hU₁, hg₁, hc₁, he₁⟩ := hf g₀ hg
  obtain ⟨U₂, f₂', hU₂, hg₂, hc₂, he₂⟩ := hf₂ g₀ hg
  refine ⟨U₁ ∩ U₂, f₁' + f₂', hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
    (hc₁.mono Set.inter_subset_left).add (hc₂.mono Set.inter_subset_right), ?_⟩
  intro g hgU hgG
  simp only [Pi.add_apply]
  rw [he₁ g hgU.1 hgG, he₂ g hgU.2 hgG]

lemma ckOn_smul {f : Mat k r → E} {m : ℕ∞} (a : ℂ) (hf : CkOn m (GV k r) f) :
    CkOn m (GV k r) (a • f) := by
  unfold CkOn at *
  intro g₀ hg
  obtain ⟨U, f', hU, hgU, hc, he⟩ := hf g₀ hg
  refine ⟨U, a • f', hU, hgU, hc.const_smul a, ?_⟩
  intro g hgU' hgG
  simp only [Pi.smul_apply]
  rw [he g hgU' hgG]

lemma op_congr {f f₂ : Mat k r → E} {X : Mat k r} (b : Bool) (hX : inLie k r X)
    (h : ∀ g ∈ GV k r, f g = f₂ g) : ∀ g ∈ GV k r, op b X f g = op b X f₂ g := by
  intro g hg
  simp only [op]
  congr 1
  funext t
  exact h _ (cv_mem hX hg t)

lemma op_add {f f₂ : Mat k r → E} {X g : Mat k r} (b : Bool) (hX : inLie k r X)
    (hf : CkOn ((1 : ℕ) : ℕ∞) (GV k r) f) (hf₂ : CkOn ((1 : ℕ) : ℕ∞) (GV k r) f₂) (hg : g ∈ GV k r) :
    op b X (f + f₂) g = op b X f g + op b X f₂ g := by
  unfold CkOn at hf hf₂
  obtain ⟨U₁, f₁', hU₁, hg₁, hc₁, he₁⟩ := hf g hg
  obtain ⟨U₂, f₂', hU₂, hg₂, hc₂, he₂⟩ := hf₂ g hg
  have hU := hU₁.inter hU₂
  have hgU : g ∈ U₁ ∩ U₂ := ⟨hg₁, hg₂⟩
  have hc₁' := hc₁.mono (Set.inter_subset_left (s := U₁) (t := U₂))
  have hc₂' := hc₂.mono (Set.inter_subset_right (s := U₁) (t := U₂))
  have d1 : DifferentiableAt ℝ f₁' g :=
    (hc₁'.contDiffAt (hU.mem_nhds hgU)).differentiableAt (cast_ne_zero 0)
  have d2 : DifferentiableAt ℝ f₂' g :=
    (hc₂'.contDiffAt (hU.mem_nhds hgU)).differentiableAt (cast_ne_zero 0)
  rw [op_eq_op' (f := f + f₂) 0 b hU (hc₁'.add hc₂')
      (fun h hh hG => by
        simp only [Pi.add_apply]
        rw [he₁ h hh.1 hG, he₂ h hh.2 hG]) hX g hgU hg,
    op_eq_op' 0 b hU hc₁' (fun h hh hG => he₁ h hh.1 hG) hX g hgU hg,
    op_eq_op' 0 b hU hc₂' (fun h hh hG => he₂ h hh.2 hG) hX g hgU hg]
  simp only [op']
  exact congrArg (fun L => L (vf b X g)) (d1.hasFDerivAt.add d2.hasFDerivAt).fderiv

lemma op_smul (b : Bool) (X : Mat k r) (a : ℂ) (f : Mat k r → E) : op b X (a • f) = a • op b X f := by
  funext g
  simp only [op, Pi.smul_apply]
  first
    | exact deriv_const_smul' (f := fun t : ℝ => f (cv b X t g)) (x := 0) a
    | exact deriv_const_smul_field (f := fun t : ℝ => f (cv b X t g)) (x := 0) a

lemma op_rsmul (b : Bool) (X : Mat k r) (a : ℝ) (f : Mat k r → E) : op b X (a • f) = a • op b X f := by
  funext g
  simp only [op, Pi.smul_apply]
  first
    | exact deriv_const_smul' (f := fun t : ℝ => f (cv b X t g)) (x := 0) a
    | exact deriv_const_smul_field (f := fun t : ℝ => f (cv b X t g)) (x := 0) a

lemma cv_rsmul (b : Bool) (X g : Mat k r) (c t : ℝ) : cv b ((c : ℂ) • X) t g = cv b X (c * t) g := by
  cases b <;> simp only [cv, smul_smul, Complex.ofReal_mul, mul_comm]

lemma op_letter_smul (b : Bool) (X : Mat k r) (c : ℝ) (f : Mat k r → E) :
    op b ((c : ℂ) • X) f = c • op b X f := by
  funext g
  simp only [op, Pi.smul_apply]
  simp_rw [cv_rsmul]
  have := deriv_comp_mul_left c (fun s => f (cv b X s g)) 0
  simpa [mul_zero] using this

lemma op_letter_add {f : Mat k r → E} {X Y g : Mat k r} (b : Bool) (hX : inLie k r X)
    (hY : inLie k r Y) (hf : CkOn ((1 : ℕ) : ℕ∞) (GV k r) f) (hg : g ∈ GV k r) :
    op b (X + Y) f g = op b X f g + op b Y f g := by
  unfold CkOn at hf
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g hg
  rw [op_eq_op' 0 b hU hc hff (inLie_add hX hY) g hgU hg, op_eq_op' 0 b hU hc hff hX g hgU hg,
    op_eq_op' 0 b hU hc hff hY g hgU hg]
  simp only [op']
  have hv : vf b (X + Y) g = vf b X g + vf b Y g := by
    cases b
    · rw [vf_false, vf_false, vf_false, Matrix.mul_add]
    · rw [vf_true, vf_true, vf_true, Matrix.add_mul, neg_add]
  rw [hv, map_add]

def W (w : List (Bool × Mat k r)) (f : Mat k r → E) : Mat k r → E :=
  w.foldr (fun x h => op x.1 x.2 h) f

lemma W_nil (f : Mat k r → E) : W [] f = f := rfl

lemma W_cons (x : Bool × Mat k r) (w : List (Bool × Mat k r)) (f : Mat k r → E) :
    W (x :: w) f = op x.1 x.2 (W w f) := rfl

lemma W_append (p q : List (Bool × Mat k r)) (f : Mat k r → E) : W (p ++ q) f = W p (W q f) := by
  unfold W
  rw [List.foldr_append]

def lr (u v : List (Mat k r)) : List (Bool × Mat k r) :=
  u.map (fun X => (true, X)) ++ v.map (fun X => (false, X))

lemma dLR_eq (u v : List (Mat k r)) (f : Mat k r → E) : dLR u v f = W (lr u v) f := by
  have hv : ∀ v : List (Mat k r), Rw v f = W (v.map fun X => (false, X)) f := by
    intro v
    induction v with
    | nil => rfl
    | cons X v ih =>
      rw [List.map_cons, W_cons, ← ih, op_false]
      rfl
  have hu : ∀ (u : List (Mat k r)) (F : Mat k r → E), u.foldr LdV F = W (u.map fun X => (true, X)) F := by
    intro u F
    induction u with
    | nil => rfl
    | cons X u ih =>
      rw [List.map_cons, W_cons, ← ih, op_true]
      rfl
  unfold lr
  rw [W_append, ← hv, ← hu]
  rfl

def AllLie (w : List (Bool × Mat k r)) : Prop := ∀ x ∈ w, inLie k r x.2

lemma smooth_on_of_word_derivatives {f : Mat k r → E} (w : List (Bool × Mat k r)) (hw : AllLie w) :
    ∀ m : ℕ, CkOn ((m + w.length : ℕ) : ℕ∞) (GV k r) f → CkOn ((m : ℕ) : ℕ∞) (GV k r) (W w f) := by
  induction w with
  | nil =>
    intro m hm
    rw [W_nil]
    first
      | exact hm
      | simpa using hm
  | cons x w ih =>
    intro m hm
    rw [W_cons]
    have hx : inLie k r x.2 := hw x (by simp)
    have hw' : AllLie w := fun y hy => hw y (by simp [hy])
    have hm' : CkOn ((m + 1 + w.length : ℕ) : ℕ∞) (GV k r) f := by
      rw [show m + 1 + w.length = m + (x :: w).length by simp only [List.length_cons]; omega]
      exact hm
    exact ckOn_op m x.1 (ih hw' (m + 1) hm') hx

lemma W_congr {f f₂ : Mat k r → E} (w : List (Bool × Mat k r)) (hw : AllLie w)
    (h : ∀ g ∈ GV k r, f g = f₂ g) : ∀ g ∈ GV k r, W w f g = W w f₂ g := by
  induction w with
  | nil => exact h
  | cons x w ih =>
    intro g hg
    rw [W_cons, W_cons]
    exact op_congr x.1 (hw x (by simp)) (ih (fun y hy => hw y (by simp [hy]))) g hg

lemma W_add {f f₂ : Mat k r → E} (w : List (Bool × Mat k r)) (hw : AllLie w)
    (hf : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f) (hf₂ : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f₂) :
    ∀ g ∈ GV k r, W w (f + f₂) g = W w f g + W w f₂ g := by
  induction w with
  | nil => intro g _; rfl
  | cons x w ih =>
    intro g hg
    have hx : inLie k r x.2 := hw x (by simp)
    have hw' : AllLie w := fun y hy => hw y (by simp [hy])
    have hf' : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f :=
      ckOn_mono (by simp only [List.length_cons]; omega) hf
    have hf₂' : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f₂ :=
      ckOn_mono (by simp only [List.length_cons]; omega) hf₂
    have g1 : CkOn ((1 + w.length : ℕ) : ℕ∞) (GV k r) f :=
      ckOn_mono (by simp only [List.length_cons]; omega) hf
    have g2 : CkOn ((1 + w.length : ℕ) : ℕ∞) (GV k r) f₂ :=
      ckOn_mono (by simp only [List.length_cons]; omega) hf₂
    rw [W_cons, W_cons, W_cons]
    rw [op_congr (f₂ := W w f + W w f₂) x.1 hx (ih hw' hf' hf₂') g hg]
    exact op_add x.1 hx (smooth_on_of_word_derivatives w hw' 1 g1) (smooth_on_of_word_derivatives w hw' 1 g2) hg

lemma W_smul (w : List (Bool × Mat k r)) (a : ℂ) (f : Mat k r → E) : W w (a • f) = a • W w f := by
  induction w with
  | nil => rfl
  | cons x w ih => rw [W_cons, W_cons, ih, op_smul]

lemma W_rsmul (w : List (Bool × Mat k r)) (a : ℝ) (f : Mat k r → E) : W w (a • f) = a • W w f := by
  induction w with
  | nil => rfl
  | cons x w ih => rw [W_cons, W_cons, ih, op_rsmul]

lemma W_sub {f f₂ : Mat k r → E} (w : List (Bool × Mat k r)) (hw : AllLie w)
    (hf : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f) (hf₂ : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f₂) :
    ∀ g ∈ GV k r, W w (f - f₂) g = W w f g - W w f₂ g := by
  intro g hg
  have e : f - f₂ = f + ((-1 : ℂ) • f₂) := by
    funext x
    simp [sub_eq_add_neg]
  rw [e, W_add w hw hf (ckOn_smul (-1) hf₂) g hg, W_smul]
  simp [sub_eq_add_neg]

lemma allLie_lr {u v : List (Mat k r)} (hu : ∀ X ∈ u, unitLie k r X) (hv : ∀ X ∈ v, unitLie k r X) :
    AllLie (lr u v) := by
  unfold AllLie
  intro x hx
  simp only [lr, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
  · exact (hu X hX).1
  · exact (hv X hX).1

lemma length_lr (u v : List (Mat k r)) : (lr u v).length = u.length + v.length := by
  simp [lr]

lemma gN_rpow_nonneg (g : Mat k r) (A : ℝ) : 0 ≤ gN g ^ A := by
  exact Real.rpow_nonneg (Real.sqrt_nonneg _) A

lemma op_op_ext {f f' : Mat k r → E} {U : Set (Mat k r)} {X Y g : Mat k r} (b b' : Bool)
    (hU : IsOpen U) (hc : ContDiffOn ℝ (((1 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) f' U)
    (hff : ∀ h ∈ U, h ∈ GV k r → f h = f' h) (hX : inLie k r X) (hY : inLie k r Y)
    (hg : g ∈ U) (hgG : g ∈ GV k r) :
    op b X (op b' Y f) g =
      fderiv ℝ (fderiv ℝ f') g (vf b X g) (vf b' Y g) + fderiv ℝ f' g (vf b' Y (vf b X g)) := by
  rw [op_eq_op' 0 b hU (op'_contDiffOn 1 b' Y hU hc) (op_eq_op' 1 b' hU hc hff hY) hX g hg hgG]
  have hd : DifferentiableAt ℝ (fderiv ℝ f') g :=
    ((hc.fderiv_of_isOpen hU (natCast_succ_le 1)).differentiableOn (cast_ne_zero 0)).differentiableAt
      (hU.mem_nhds hg)
  have H := (hd.hasFDerivAt.clm_apply (vf b' Y).hasFDerivAt).fderiv
  unfold op'
  erw [H]
  exact add_comm _ _

lemma op_comm {f : Mat k r → E} {X Y g : Mat k r} (hf : CkOn ((2 : ℕ) : ℕ∞) (GV k r) f)
    (hX : inLie k r X) (hY : inLie k r Y) (hg : g ∈ GV k r) :
    op false Y (op true X f) g = op true X (op false Y f) g := by
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g hg
  rw [op_op_ext false true hU hc hff hY hX hgU hg, op_op_ext true false hU hc hff hX hY hgU hg]
  have hsym : IsSymmSndFDerivAt ℝ f' g :=
    (hc.contDiffAt (hU.mem_nhds hgU)).isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have h1 := hsym (vf false Y g) (vf true X g)
  have h2 : vf true X (vf false Y g) = vf false Y (vf true X g) := by
    simp [vf_true, vf_false, Matrix.mul_assoc]
  rw [h2]
  exact congrArg (· + fderiv ℝ f' g (vf false Y (vf true X g))) h1

lemma op_W_comm {Z : Mat k r} (hZ : inLie k r Z) (u : List (Mat k r)) (hu : ∀ X ∈ u, inLie k r X) :
    ∀ K : Mat k r → E, CkOn ((u.length + 1 : ℕ) : ℕ∞) (GV k r) K → ∀ g ∈ GV k r,
      op false Z (W (lr u []) K) g = W (lr u []) (op false Z K) g := by
  induction u with
  | nil => intro K _ g _; rfl
  | cons X u ih =>
    intro K hK g hg
    have hu' : ∀ X ∈ u, inLie k r X := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    have hl : AllLie (lr u ([] : List (Mat k r))) := by
      intro x hx
      simp only [lr, List.map_nil, List.append_nil, List.mem_map] at hx
      obtain ⟨Y, hY, rfl⟩ := hx
      exact hu' Y hY
    have e : ∀ K' : Mat k r → E, W (lr (X :: u) []) K' = op true X (W (lr u []) K') := fun _ => rfl
    rw [e, e, op_comm (smooth_on_of_word_derivatives _ hl 2 (ckOn_mono (by simp [lr]; omega) hK)) (hu X List.mem_cons_self) hZ hg]
    exact op_congr true (hu X List.mem_cons_self)
      (ih hu' K (ckOn_mono (by simp) hK)) g hg

def LRt (τ : List Bool) : Prop := ∃ a b, τ = List.replicate a true ++ List.replicate b false

private lemma tags_false_lemma : ∀ (w : List (Bool × Mat k r)) (b : ℕ),
    w.map Prod.fst = List.replicate b false → w = (w.map Prod.snd).map (fun X => (false, X)) := by
  intro w
  induction w with
  | nil => intro b _; rfl
  | cons x w ih =>
    intro b h
    cases b with
    | zero => simp at h
    | succ b =>
      simp only [List.map_cons, List.replicate_succ, List.cons.injEq] at h
      obtain ⟨hx, hw⟩ := h
      simp only [List.map_cons]
      rw [← ih b hw]
      congr 1
      exact Prod.ext hx rfl

lemma of_tags : ∀ (w : List (Bool × Mat k r)) (a b : ℕ),
    w.map Prod.fst = List.replicate a true ++ List.replicate b false →
    ∃ u v : List (Mat k r), u.length = a ∧ w = lr u v := by
  intro w a
  induction a generalizing w with
  | zero =>
    intro b h
    simp only [List.replicate_zero, List.nil_append] at h
    refine ⟨[], w.map Prod.snd, rfl, ?_⟩
    conv_lhs => rw [tags_false_lemma w b h]
    simp [lr]
  | succ a ih =>
    intro b h
    cases w with
    | nil => simp at h
    | cons x w =>
      simp only [List.map_cons, List.replicate_succ, List.cons_append, List.cons.injEq] at h
      obtain ⟨hx, hw⟩ := h
      obtain ⟨u, v, hu, rfl⟩ := ih w b hw
      refine ⟨x.2 :: u, v, by simp [hu], ?_⟩
      simp only [lr, List.map_cons, List.cons_append]
      congr 1
      exact Prod.ext hx rfl

lemma lrt_lr (u v : List (Mat k r)) : LRt ((lr u v).map Prod.fst) := by
  refine ⟨u.length, v.length, ?_⟩
  first
    | (simp [lr, Function.comp_def]; done)
    | (simp [lr, Function.comp_def, List.map_const']; done)
    | (simp [lr, List.map_map, Function.comp_def, List.eq_replicate_iff]; done)

lemma bound_tag {F : Mat k r → E} {A c : ℝ} {m : ℕ} (h : CCle A m F c) (w : List (Bool × Mat k r))
    (ht : LRt (w.map Prod.fst)) (hu : ∀ x ∈ w, unitLie k r x.2) (hl : w.length ≤ m) :
    ∀ g ∈ GV k r, gN g ^ A * ‖W w F g‖ ≤ c := by
  intro g hg
  obtain ⟨a, b, hab⟩ := ht
  obtain ⟨u, v, _, rfl⟩ := of_tags w a b hab
  rw [← dLR_eq]
  have hu' : ∀ X ∈ u, unitLie k r X := fun X hX => hu (true, X) (by simp [lr, hX])
  have hv' : ∀ X ∈ v, unitLie k r X := fun X hX => hu (false, X) (by simp [lr, hX])
  have hl' : u.length + v.length ≤ m := by
    rw [length_lr] at hl
    exact hl
  unfold CCle at h
  exact h.2 u v hu' hv' hl' g hg

def nrm (x : Bool × Mat k r) : Bool × Mat k r := (x.1, ((‖x.2‖⁻¹ : ℝ) : ℂ) • x.2)

lemma nrm_smul (X : Mat k r) : X = ((‖X‖ : ℝ) : ℂ) • (((‖X‖⁻¹ : ℝ) : ℂ) • X) := by
  by_cases hX : X = 0
  · simp [hX]
  · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hX),
      Complex.ofReal_one, one_smul]

private lemma entry_le_lemma (A : Mat k r) (i j : Fin (2 * r + k + 1)) : ‖A i j‖ ≤ ‖A‖ := by
  first
    | exact Matrix.norm_entry_le_entrywise_sup_norm A
    | exact (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)

private lemma norm_le_lemma_2 {A : Mat k r} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, ‖A i j‖ ≤ c) :
    ‖A‖ ≤ c := by
  first
    | exact (Matrix.norm_le_iff hc).mpr h
    | exact (pi_norm_le_iff_of_nonneg hc).mpr fun i => (pi_norm_le_iff_of_nonneg hc).mpr (h i)

lemma nrm_unit {x : Bool × Mat k r} (hx : inLie k r x.2) : unitLie k r (nrm x).2 := by
  refine ⟨inLie_rsmul hx _, fun i j => ?_⟩
  simp only [nrm, Matrix.smul_apply, smul_eq_mul, norm_mul]
  rw [show ‖((‖x.2‖⁻¹ : ℝ) : ℂ)‖ = ‖x.2‖⁻¹ by simp]
  by_cases h0 : ‖x.2‖ = 0
  · rw [h0, _root_.inv_zero, zero_mul]
    exact zero_le_one
  · calc ‖x.2‖⁻¹ * ‖x.2 i j‖ ≤ ‖x.2‖⁻¹ * ‖x.2‖ :=
        mul_le_mul_of_nonneg_left (entry_le_lemma x.2 i j) (inv_nonneg.mpr (norm_nonneg _))
      _ = 1 := inv_mul_cancel₀ h0

def pn (w : List (Bool × Mat k r)) : ℝ := (w.map fun x => ‖x.2‖).prod

lemma pn_nonneg (w : List (Bool × Mat k r)) : 0 ≤ pn w := by
  unfold pn
  apply List.prod_nonneg
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨x, _, rfl⟩ := ha
  exact norm_nonneg _

lemma pn_cons (x : Bool × Mat k r) (w : List (Bool × Mat k r)) : pn (x :: w) = ‖x.2‖ * pn w := by
  simp only [pn, List.map_cons, List.prod_cons]

lemma pn_append (p q : List (Bool × Mat k r)) : pn (p ++ q) = pn p * pn q := by
  simp only [pn, List.map_append, List.prod_append]

lemma pn_le_pow (w : List (Bool × Mat k r)) (K : ℝ) (h : ∀ x ∈ w, ‖x.2‖ ≤ K) :
    pn w ≤ K ^ w.length := by
  induction w with
  | nil => simp [pn]
  | cons x w ih =>
    rw [pn_cons, List.length_cons, pow_succ']
    have hx := h x (by simp)
    have ih' := ih (fun y hy => h y (by simp [hy]))
    exact mul_le_mul hx ih' (pn_nonneg w) (le_trans (norm_nonneg _) hx)

lemma W_nrm (w : List (Bool × Mat k r)) (F : Mat k r → E) : W w F = pn w • W (w.map nrm) F := by
  induction w with
  | nil => simp [pn, W]
  | cons x w ih =>
    rw [W_cons, ih, List.map_cons, W_cons, pn_cons, op_rsmul]
    conv_lhs => rw [nrm_smul x.2]
    rw [op_letter_smul, smul_smul, mul_comm (pn w)]
    rfl

lemma bound_scaled {F : Mat k r → E} {A c : ℝ} {m : ℕ} (h : CCle A m F c) (w : List (Bool × Mat k r))
    (ht : LRt (w.map Prod.fst)) (hw : AllLie w) (hl : w.length ≤ m) :
    ∀ g ∈ GV k r, gN g ^ A * ‖W w F g‖ ≤ pn w * c := by
  intro g hg
  have e : (w.map nrm).map Prod.fst = w.map Prod.fst := by
    rw [List.map_map]
    rfl
  have hb := bound_tag h (w.map nrm) (by rw [e]; exact ht)
    (fun x hx => by
      simp only [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact nrm_unit (hw y hy))
    (by rw [List.length_map]; exact hl) g hg
  rw [W_nrm, Pi.smul_apply, norm_smul, Real.norm_of_nonneg (pn_nonneg w)]
  calc gN g ^ A * (pn w * ‖W (w.map nrm) F g‖) = pn w * (gN g ^ A * ‖W (w.map nrm) F g‖) := by ring
    _ ≤ pn w * c := mul_le_mul_of_nonneg_left hb (pn_nonneg w)

lemma W_mid_add {F : Mat k r → E} (p q : List (Bool × Mat k r)) (b : Bool) {X Y : Mat k r}
    (hp : AllLie p) (hq : AllLie q) (hX : inLie k r X) (hY : inLie k r Y)
    (hF : CkOn ((p.length + 1 + q.length : ℕ) : ℕ∞) (GV k r) F) :
    ∀ g ∈ GV k r, W (p ++ (b, X + Y) :: q) F g = W (p ++ (b, X) :: q) F g + W (p ++ (b, Y) :: q) F g := by
  intro g hg
  simp only [W_append, W_cons]
  have hWq : CkOn ((p.length + 1 : ℕ) : ℕ∞) (GV k r) (W q F) := smooth_on_of_word_derivatives q hq (p.length + 1) hF
  have hWq1 : CkOn ((1 : ℕ) : ℕ∞) (GV k r) (W q F) := ckOn_mono (by omega) hWq
  have hinner : ∀ h ∈ GV k r, op b (X + Y) (W q F) h = (op b X (W q F) + op b Y (W q F)) h :=
    fun h hh => op_letter_add b hX hY hWq1 hh
  rw [W_congr p hp hinner g hg]
  exact W_add p hp (ckOn_op p.length b hWq hX) (ckOn_op p.length b hWq hY) g hg

lemma unit_norm_le {X : Mat k r} (h : unitLie k r X) : ‖X‖ ≤ 1 := by
  exact norm_le_lemma_2 zero_le_one h.2

lemma telescope {F : Mat k r → E} {A c K ε : ℝ} {m : ℕ} (h : CCle A m F c) (hc : 0 ≤ c) (hK : 1 ≤ K)
    (φ : Bool × Mat k r → Bool × Mat k r) (hφ1 : ∀ x, (φ x).1 = x.1)
    (hφL : ∀ x, unitLie k r x.2 → inLie k r (φ x).2)
    (hφK : ∀ x, unitLie k r x.2 → ‖(φ x).2‖ ≤ K)
    (hφε : ∀ x, unitLie k r x.2 → ‖(φ x).2 - x.2‖ ≤ ε) :
    ∀ (w p : List (Bool × Mat k r)), (∀ x ∈ p, unitLie k r x.2) → (∀ x ∈ w, unitLie k r x.2) →
      LRt ((p ++ w).map Prod.fst) → (p ++ w).length ≤ m → ∀ g ∈ GV k r,
      gN g ^ A * ‖W (p ++ w.map φ) F g - W (p ++ w) F g‖ ≤ w.length * (K ^ m * ε * c) := by
  intro w
  induction w with
  | nil => intro p _ _ _ _ g _; simp
  | cons x w ih =>
    intro p hp hw ht hl g hg
    have hx : unitLie k r x.2 := hw x List.mem_cons_self
    have hw' : ∀ y ∈ w, unitLie k r y.2 := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hε : 0 ≤ ε := le_trans (norm_nonneg _) (hφε x hx)
    have hpL : AllLie p := fun y hy => (hp y hy).1
    have hqL : AllLie (w.map φ) := by
      intro y hy
      obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
      exact hφL y' (hw' y' hy')
    have hlen : p.length + 1 + w.length ≤ m := by
      simp only [List.length_append, List.length_cons] at hl; omega
    have hδL : inLie k r ((φ x).2 - x.2) := inLie_sub (hφL x hx) hx.1

    have e1 : W (p ++ φ x :: w.map φ) F g =
        W (p ++ x :: w.map φ) F g + W (p ++ (x.1, (φ x).2 - x.2) :: w.map φ) F g := by
      have hφx : φ x = (x.1, x.2 + ((φ x).2 - x.2)) := by
        refine Prod.ext (hφ1 x) ?_
        simp
      have := W_mid_add p (w.map φ) x.1 hpL hqL hx.1 hδL
        (ckOn_mono (by simpa using hlen) h.1) g hg
      rw [← hφx] at this
      exact this
    have tags : ((p ++ (x.1, (φ x).2 - x.2) :: w.map φ).map Prod.fst) = (p ++ x :: w).map Prod.fst := by
      simp [List.map_append, List.map_map, Function.comp_def, hφ1]
    have b1 := bound_scaled h (p ++ (x.1, (φ x).2 - x.2) :: w.map φ) (by rw [tags]; exact ht)
      (by
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hpL y hy
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact hδL
          · exact hqL y hy)
      (by simp only [List.length_append, List.length_cons, List.length_map]; omega) g hg
    have hpn : pn (p ++ (x.1, (φ x).2 - x.2) :: w.map φ) ≤ K ^ m * ε := by
      rw [pn_append, pn_cons]
      have h1 : pn p ≤ 1 := by
        have := pn_le_pow p 1 (fun y hy => unit_norm_le (hp y hy))
        simpa using this
      have h2 : pn (w.map φ) ≤ K ^ m := by
        refine le_trans (pn_le_pow (w.map φ) K ?_) (pow_le_pow_right₀ hK (by simp; omega))
        intro y hy
        obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
        exact hφK y' (hw' y' hy')
      calc pn p * (‖(φ x).2 - x.2‖ * pn (w.map φ)) ≤ 1 * (ε * K ^ m) :=
            mul_le_mul h1 (mul_le_mul (hφε x hx) h2 (pn_nonneg _) hε)
              (mul_nonneg (norm_nonneg _) (pn_nonneg _)) zero_le_one
        _ = K ^ m * ε := by ring
    have b2 := ih (p ++ [x])
      (by
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hp y hy
        · rw [List.mem_singleton.mp hy]; exact hx)
      hw' (by simpa using ht) (by simpa using hl) g hg
    simp only [List.append_assoc, List.singleton_append] at b2
    rw [List.map_cons, e1]
    have hsplit : W (p ++ x :: w.map φ) F g + W (p ++ (x.1, (φ x).2 - x.2) :: w.map φ) F g -
        W (p ++ x :: w) F g = W (p ++ (x.1, (φ x).2 - x.2) :: w.map φ) F g +
          (W (p ++ x :: w.map φ) F g - W (p ++ x :: w) F g) := by abel
    rw [hsplit]
    calc gN g ^ A * ‖W (p ++ (x.1, (φ x).2 - x.2) :: w.map φ) F g +
          (W (p ++ x :: w.map φ) F g - W (p ++ x :: w) F g)‖
        ≤ gN g ^ A * (‖W (p ++ (x.1, (φ x).2 - x.2) :: w.map φ) F g‖ +
          ‖W (p ++ x :: w.map φ) F g - W (p ++ x :: w) F g‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (gN_rpow_nonneg g A)
      _ = gN g ^ A * ‖W (p ++ (x.1, (φ x).2 - x.2) :: w.map φ) F g‖ +
          gN g ^ A * ‖W (p ++ x :: w.map φ) F g - W (p ++ x :: w) F g‖ := by ring
      _ ≤ K ^ m * ε * c + w.length * (K ^ m * ε * c) :=
          add_le_add (le_trans b1 (mul_le_mul_of_nonneg_right hpn hc)) b2
      _ = ((x :: w).length : ℝ) * (K ^ m * ε * c) := by
          simp only [List.length_cons]; push_cast; ring

lemma inLie_conj {a X : Mat k r} (ha : a ∈ GV k r) (hX : inLie k r X) : inLie k r (a⁻¹ * X * a) := by
  have hH : IsUnit (Hpk k r).det := (Matrix.isUnit_iff_isUnit_det _).mp hpk_isUnit
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hdet : IsUnit a.det := by
    have hd := congrArg Matrix.det ha'
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at hd
    rw [isUnit_iff_ne_zero] at hH ⊢
    intro h0
    rw [h0, MulZeroClass.mul_zero] at hd
    exact hH hd.symm
  have e1 : aᴴ * Hpk k r = Hpk k r * a⁻¹ := by
    calc aᴴ * Hpk k r = aᴴ * Hpk k r * (a * a⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = Hpk k r * a⁻¹ := by rw [← Matrix.mul_assoc, ha']
  have e2 : (a⁻¹)ᴴ * Hpk k r = Hpk k r * a := by
    calc (a⁻¹)ᴴ * Hpk k r = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) := by rw [ha']
      _ = (a * a⁻¹)ᴴ * Hpk k r * a := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Hpk k r * a := by
          rw [Matrix.mul_nonsing_inv _ hdet, Matrix.conjTranspose_one, Matrix.one_mul]
  unfold inLie at *
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc _ = aᴴ * Xᴴ * ((a⁻¹)ᴴ * Hpk k r) + Hpk k r * a⁻¹ * X * a := by
        simp only [Matrix.mul_assoc]
    _ = aᴴ * (Xᴴ * Hpk k r + Hpk k r * X) * a := by
        rw [e2, ← e1]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX, Matrix.mul_zero, Matrix.zero_mul]

def sel (t : ℝ × ℝ) (b : Bool) : ℝ :=
  match b with
  | true => t.1
  | false => t.2

def adj (t : ℝ × ℝ) (x : Bool × Mat k r) : Bool × Mat k r :=
  (x.1, (aDil k r (sel t x.1))⁻¹ * x.2 * aDil k r (sel t x.1))

lemma aDil_isUnit_det (t : ℝ) (ht : t ≠ 0) : IsUnit (aDil k r t).det := by
  rw [aDil_eq, Matrix.det_diagonal]
  exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => left_ne_zero_of_mul_eq_one (dg_mul_inv k r t ht i))

private lemma exp_conj_lemma (a A : Mat k r) (ha : IsUnit a) :
    NormedSpace.exp (a⁻¹ * A * a) = a⁻¹ * NormedSpace.exp A * a := by
  first
    | exact Matrix.exp_conj' a A ha
    | (have h := Matrix.exp_conj a⁻¹ A ((Matrix.isUnit_nonsing_inv_iff).mpr ha)
       rwa [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp ha)] at h)

lemma cv_dil (t : ℝ × ℝ) (h1 : t.1 ≠ 0) (h2 : t.2 ≠ 0) (b : Bool) (X g : Mat k r) (s : ℝ) :
    (aDil k r t.1)⁻¹ * cv b X s g * aDil k r t.2 =
      cv b (adj t (b, X)).2 s ((aDil k r t.1)⁻¹ * g * aDil k r t.2) := by
  have hu1 : IsUnit (aDil k r t.1) := (Matrix.isUnit_iff_isUnit_det _).mpr (aDil_isUnit_det _ h1)
  have hu2 : IsUnit (aDil k r t.2) := (Matrix.isUnit_iff_isUnit_det _).mpr (aDil_isUnit_det _ h2)
  have hsm : ∀ (c : ℂ) (a : Mat k r), c • (a⁻¹ * X * a) = a⁻¹ * (c • X) * a := by
    intro c a
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hsm' : ∀ (c : ℂ) (a : Mat k r), -(c • (a⁻¹ * X * a)) = a⁻¹ * (-(c • X)) * a := by
    intro c a
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]
  cases b
  · simp only [cv, adj, sel]
    rw [hsm, exp_conj_lemma _ _ hu2]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (aDil_isUnit_det _ h2)]
  · simp only [cv, adj, sel]
    rw [hsm', exp_conj_lemma _ _ hu1]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (aDil_isUnit_det _ h1)]

def dl (t : ℝ × ℝ) (f : Mat k r → E) (g : Mat k r) : E := f ((aDil k r t.1)⁻¹ * g * aDil k r t.2)

lemma op_dl (t : ℝ × ℝ) (h1 : t.1 ≠ 0) (h2 : t.2 ≠ 0) (b : Bool) (X : Mat k r) (f : Mat k r → E) :
    op b X (dl t f) = dl t (op b (adj t (b, X)).2 f) := by
  funext g
  simp only [op, dl]
  congr 1
  funext s
  rw [cv_dil t h1 h2]

lemma W_dl (t : ℝ × ℝ) (h1 : t.1 ≠ 0) (h2 : t.2 ≠ 0) (w : List (Bool × Mat k r)) (f : Mat k r → E) :
    W w (dl t f) = dl t (W (w.map (adj t)) f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [W_cons, ih, op_dl t h1 h2, List.map_cons, W_cons]
    try rfl

lemma ckOn_dl {m : ℕ∞} (t : ℝ × ℝ) (h1 : t.1 ≠ 0) (h2 : t.2 ≠ 0) {f : Mat k r → E}
    (hf : CkOn m (GV k r) f) : CkOn m (GV k r) (dl t f) := by
  unfold CkOn at *
  have hin : ∀ g ∈ GV k r, (aDil k r t.1)⁻¹ * g * aDil k r t.2 ∈ GV k r := by
    intro g hg
    rw [aDil_inv k r t.1 h1]
    exact gv_mul_lemma (gv_mul_lemma (aDil_mem k r _ (inv_ne_zero h1)) hg) (aDil_mem k r _ h2)
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf _ (hin g₀ hg₀)
  let L : Mat k r →L[ℝ] Mat k r := (mulR (aDil k r t.2)).comp (mulL (aDil k r t.1)⁻¹)
  refine ⟨L ⁻¹' U, f' ∘ L, hU.preimage L.continuous, hgU, ?_, ?_⟩
  · exact hc.comp L.contDiff.contDiffOn (fun x hx => hx)
  · intro g hgU' hgG
    exact hff (L g) hgU' (hin g hgG)

lemma inv_mem_I {t : ℝ} (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : t⁻¹ ∈ Set.Icc (1 / 2 : ℝ) 2 := by
  obtain ⟨h1, h2⟩ := ht
  have hpos : 0 < t := by linarith
  have hs : t⁻¹ * t = 1 := inv_mul_cancel₀ hpos.ne'
  have hsp : 0 < t⁻¹ := inv_pos.mpr hpos
  rw [Set.mem_Icc]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h2 hsp.le]
  · nlinarith [mul_le_mul_of_nonneg_left h1 hsp.le]

lemma abs_inv_sub_one {t : ℝ} (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : |t⁻¹ - 1| ≤ 2 * |t - 1| := by
  have hpos : 0 < t := by linarith [ht.1]
  have e : t⁻¹ - 1 = -(t - 1) * t⁻¹ := by
    first
      | (field_simp; ring)
      | field_simp
  rw [e, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr hpos), mul_comm]
  exact mul_le_mul_of_nonneg_right (inv_mem_I ht).2 (abs_nonneg _)

lemma pow_sub_one_le {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2) (n : ℕ) : |t ^ n - 1| ≤ (2 ^ n - 1) * |t - 1| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : t ^ (n + 1) - 1 = t * (t ^ n - 1) + (t - 1) := by ring
    calc |t ^ (n + 1) - 1| ≤ |t * (t ^ n - 1)| + |t - 1| := by rw [e]; exact abs_add_le _ _
      _ = t * |t ^ n - 1| + |t - 1| := by rw [abs_mul, abs_of_nonneg h0]
      _ ≤ 2 * ((2 ^ n - 1) * |t - 1|) + |t - 1| := by
          have := mul_le_mul h2 ih (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
          linarith
      _ = (2 ^ (n + 1) - 1) * |t - 1| := by ring

lemma two_pow_le (n : ℕ) (h : n ≤ r) : (2 : ℝ) ^ n ≤ 2 ^ r := by
  exact pow_le_pow_right₀ (by norm_num) h

private lemma normc_lemma (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  rw [Complex.norm_real, Real.norm_eq_abs]

lemma dg_norm_le {t : ℝ} (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) (i : Fin (2 * r + k + 1)) :
    ‖dg k r t i‖ ≤ 2 ^ r := by
  obtain ⟨h1, h2⟩ := ht
  have hpos : 0 < t := by linarith
  have hi := i.isLt
  unfold dg
  split_ifs with ha hb
  · rw [normc_lemma, abs_of_pos (pow_pos hpos _)]
    exact le_trans (pow_le_pow_left₀ hpos.le h2 _) (two_pow_le _ (by omega))
  · rw [norm_one]
    exact one_le_pow₀ (by norm_num)
  · rw [normc_lemma, ← inv_pow, abs_of_pos (pow_pos (inv_pos.mpr hpos) _)]
    exact le_trans (pow_le_pow_left₀ (inv_pos.mpr hpos).le (inv_mem_I ⟨h1, h2⟩).2 _)
      (two_pow_le _ (by omega))

lemma dg_sub_one {t : ℝ} (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) (i : Fin (2 * r + k + 1)) :
    ‖dg k r t i - 1‖ ≤ 2 ^ (r + 1) * |t - 1| := by
  have ht' := ht
  obtain ⟨h1, h2⟩ := ht
  have hpos : 0 < t := by linarith
  have hi := i.isLt
  have hA : 0 ≤ |t - 1| := abs_nonneg _
  have h5 : (2 : ℝ) ^ (r + 1) = 2 ^ r * 2 := pow_succ 2 r
  have h6 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  rw [h5]
  unfold dg
  split_ifs with ha hb
  · rw [← Complex.ofReal_one, ← Complex.ofReal_sub, normc_lemma]
    have h3 := pow_sub_one_le hpos.le h2 (r - i.val)
    have h4 : (2 : ℝ) ^ (r - i.val) ≤ 2 ^ r := two_pow_le _ (by omega)
    have h7 := mul_le_mul_of_nonneg_right (show (2 : ℝ) ^ (r - i.val) - 1 ≤ 2 ^ r * 2 by linarith) hA
    linarith
  · rw [sub_self, norm_zero]
    positivity
  · rw [← Complex.ofReal_one, ← Complex.ofReal_sub, normc_lemma, ← inv_pow]
    have hinv := inv_mem_I ht'
    have h3 := pow_sub_one_le (inv_pos.mpr hpos).le hinv.2 (i.val - (r + k))
    have h4 : (2 : ℝ) ^ (i.val - (r + k)) ≤ 2 ^ r := two_pow_le _ (by omega)
    have h8 := abs_inv_sub_one ht'
    have h9 : (1 : ℝ) ≤ 2 ^ (i.val - (r + k)) := one_le_pow₀ (by norm_num)
    have h10 := mul_le_mul_of_nonneg_left h8 (show (0 : ℝ) ≤ 2 ^ (i.val - (r + k)) - 1 by linarith)
    have h11 := mul_le_mul_of_nonneg_right h4 hA
    nlinarith

lemma adj_apply {τ : ℝ} (hτ : τ ≠ 0) (X : Mat k r) (i j : Fin (2 * r + k + 1)) :
    ((aDil k r τ)⁻¹ * X * aDil k r τ) i j = dg k r τ⁻¹ i * X i j * dg k r τ j := by
  rw [aDil_inv k r τ hτ, aDil_eq, aDil_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]

lemma ne_zero_of_mem_I {t : ℝ} (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : t ≠ 0 := by
  have := ht.1
  exact ne_of_gt (by linarith)

lemma four_pow (r : ℕ) : (4 : ℝ) ^ r = 2 ^ r * 2 ^ r := by
  rw [← mul_pow]
  norm_num

lemma adj_norm {τ : ℝ} (hτ : τ ∈ Set.Icc (1 / 2 : ℝ) 2) (X : Mat k r) :
    ‖(aDil k r τ)⁻¹ * X * aDil k r τ‖ ≤ 4 ^ r * ‖X‖ := by
  have hτ0 := ne_zero_of_mem_I hτ
  apply norm_le_lemma_2 (by positivity)
  intro i j
  rw [adj_apply hτ0, norm_mul, norm_mul, four_pow]
  have a1 := dg_norm_le (k := k) (inv_mem_I hτ) i
  have a2 := dg_norm_le (k := k) hτ j
  have a3 : ‖X i j‖ ≤ ‖X‖ := entry_le_lemma X i j
  calc ‖dg k r τ⁻¹ i‖ * ‖X i j‖ * ‖dg k r τ j‖ ≤ 2 ^ r * ‖X‖ * 2 ^ r := by gcongr
    _ = 2 ^ r * 2 ^ r * ‖X‖ := by ring

lemma adj_sub_norm {τ : ℝ} (hτ : τ ∈ Set.Icc (1 / 2 : ℝ) 2) (X : Mat k r) :
    ‖(aDil k r τ)⁻¹ * X * aDil k r τ - X‖ ≤ 8 * 4 ^ r * |τ - 1| * ‖X‖ := by
  have hτ0 := ne_zero_of_mem_I hτ
  have hA : 0 ≤ |τ - 1| := abs_nonneg _
  apply norm_le_lemma_2 (by positivity)
  intro i j
  rw [Matrix.sub_apply, adj_apply hτ0]
  have e : dg k r τ⁻¹ i * X i j * dg k r τ j - X i j =
      X i j * (dg k r τ⁻¹ i * (dg k r τ j - 1) + (dg k r τ⁻¹ i - 1)) := by ring
  rw [e, norm_mul]
  have a1 := dg_norm_le (k := k) (inv_mem_I hτ) i
  have a2 := dg_sub_one (k := k) hτ j
  have a3 := dg_sub_one (k := k) (inv_mem_I hτ) i
  have a4 := abs_inv_sub_one hτ
  have a5 : ‖X i j‖ ≤ ‖X‖ := entry_le_lemma X i j
  have a6 : ‖dg k r τ⁻¹ i - 1‖ ≤ 2 ^ (r + 1) * (2 * |τ - 1|) :=
    a3.trans (mul_le_mul_of_nonneg_left a4 (by positivity))
  have b : ‖dg k r τ⁻¹ i * (dg k r τ j - 1) + (dg k r τ⁻¹ i - 1)‖ ≤ 8 * 4 ^ r * |τ - 1| := by
    calc _ ≤ ‖dg k r τ⁻¹ i * (dg k r τ j - 1)‖ + ‖dg k r τ⁻¹ i - 1‖ := norm_add_le _ _
      _ = ‖dg k r τ⁻¹ i‖ * ‖dg k r τ j - 1‖ + ‖dg k r τ⁻¹ i - 1‖ := by rw [norm_mul]
      _ ≤ 2 ^ r * (2 ^ (r + 1) * |τ - 1|) + 2 ^ (r + 1) * (2 * |τ - 1|) := by gcongr
      _ ≤ 8 * 4 ^ r * |τ - 1| := by
          rw [four_pow, pow_succ]
          have h2r : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
          have h3 := mul_le_mul_of_nonneg_right (show (2 : ℝ) ^ r ≤ 2 ^ r * 2 ^ r by nlinarith) hA
          have h4 : 0 ≤ 2 ^ r * 2 ^ r * |τ - 1| := by positivity
          nlinarith
  calc ‖X i j‖ * _ ≤ ‖X‖ * (8 * 4 ^ r * |τ - 1|) := by gcongr
    _ = 8 * 4 ^ r * |τ - 1| * ‖X‖ := by ring

lemma gN_diag (d₁ d₂ : Fin (2 * r + k + 1) → ℂ) (κ : ℝ) (h₁ : ∀ i, ‖d₁ i‖ ≤ κ)
    (h₂ : ∀ i, ‖d₂ i‖ ≤ κ) (g : Mat k r) :
    gN (Matrix.diagonal d₁ * g * Matrix.diagonal d₂) ≤ κ ^ 2 * gN g := by
  unfold gN
  have hκ : 0 ≤ κ := le_trans (norm_nonneg _) (h₁ ⟨0, by omega⟩)
  rw [show κ ^ 2 = Real.sqrt ((κ ^ 2) ^ 2) by rw [Real.sqrt_sq (by positivity)],
    ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Complex.normSq_mul, Complex.normSq_mul]
  have a1 : Complex.normSq (d₁ i) ≤ κ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (h₁ i) 2
  have a2 : Complex.normSq (d₂ j) ≤ κ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (h₂ j) 2
  have a3 := Complex.normSq_nonneg (g i j)
  have a4 := Complex.normSq_nonneg (d₁ i)
  have a5 := Complex.normSq_nonneg (d₂ j)
  calc Complex.normSq (d₁ i) * Complex.normSq (g i j) * Complex.normSq (d₂ j)
      ≤ κ ^ 2 * Complex.normSq (g i j) * κ ^ 2 := by gcongr
    _ = (κ ^ 2) ^ 2 * Complex.normSq (g i j) := by ring

lemma gN_dil {τ₁ τ₂ A : ℝ} (h₁ : τ₁ ∈ Set.Icc (1 / 2 : ℝ) 2) (h₂ : τ₂ ∈ Set.Icc (1 / 2 : ℝ) 2)
    (hA : 0 ≤ A) (g : Mat k r) :
    gN g ^ A ≤ ((4 : ℝ) ^ r) ^ A * gN (aDil k r τ₁ * g * aDil k r τ₂) ^ A := by
  have h10 := ne_zero_of_mem_I h₁
  have h20 := ne_zero_of_mem_I h₂
  have hg : g = Matrix.diagonal (dg k r τ₁⁻¹) * (aDil k r τ₁ * g * aDil k r τ₂) *
      Matrix.diagonal (dg k r τ₂⁻¹) := by
    rw [← aDil_eq, ← aDil_eq, ← aDil_inv k r τ₁ h10, ← aDil_inv k r τ₂ h20]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ (aDil_isUnit_det _ h10), Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (aDil_isUnit_det _ h20), Matrix.mul_one]
  have hle : gN g ≤ (2 ^ r) ^ 2 * gN (aDil k r τ₁ * g * aDil k r τ₂) := by
    conv_lhs => rw [hg]
    exact gN_diag _ _ _ (dg_norm_le (inv_mem_I h₁)) (dg_norm_le (inv_mem_I h₂)) _
  have h0 : 0 ≤ gN g := Real.sqrt_nonneg _
  calc gN g ^ A ≤ ((2 ^ r) ^ 2 * gN (aDil k r τ₁ * g * aDil k r τ₂)) ^ A :=
      Real.rpow_le_rpow h0 hle hA
    _ = ((4 : ℝ) ^ r) ^ A * gN (aDil k r τ₁ * g * aDil k r τ₂) ^ A := by
      rw [Real.mul_rpow (by positivity)
        (show (0 : ℝ) ≤ gN (aDil k r τ₁ * g * aDil k r τ₂) from Real.sqrt_nonneg _), four_pow, sq]

def zd (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℝ :=
  if i.val < r then ((r - i.val : ℕ) : ℝ) else if i.val ≤ r + k then 0 else -((i.val - (r + k) : ℕ) : ℝ)

def Zm (k r : ℕ) : Mat k r := Matrix.diagonal fun i => ((zd k r i : ℝ) : ℂ)

lemma exp_Zm (s : ℝ) : NormedSpace.exp ((s : ℂ) • Zm k r) = aDil k r (Real.exp s) := by
  unfold Zm
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, aDil_eq]
  congr 1
  funext i
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  unfold zd dg
  by_cases c1 : i.val < r
  · simp only [c1, if_true, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  · by_cases c2 : i.val ≤ r + k
    · simp [c1, c2]
    · simp only [c1, c2, if_false, Pi.smul_apply, smul_eq_mul]
      push_cast
      rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
      congr 1
      ring

private lemma zd_pair_lemma (i j : Fin (2 * r + k + 1)) (hi : i.val < r)
    (hij : i.val + j.val = 2 * r + k) : zd k r i + zd k r j = 0 := by
  have hj1 : ¬ j.val < r := by omega
  have hj2 : ¬ j.val ≤ r + k := by omega
  have e : j.val - (r + k) = r - i.val := by omega
  unfold zd
  rw [if_pos hi, if_neg hj1, if_neg hj2, e]
  ring

private lemma zd_mid_lemma_2 (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) :
    zd k r i = 0 := by
  unfold zd
  rw [if_neg (by omega), if_pos h2]

lemma Zm_lie : inLie k r (Zm k r) := by
  unfold inLie
  have hD : (Zm k r)ᴴ = Zm k r := by
    unfold Zm
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      simp
    · rw [if_neg (Ne.symm h), if_neg h, star_zero]
  rw [hD]
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply]
  unfold Zm
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk
  split_ifs with h1 h2 h3 h4
  · rw [mul_one, one_mul, ← Complex.ofReal_add, zd_pair_lemma i j h1.1 h1.2, Complex.ofReal_zero]
  · rw [mul_one, one_mul, ← Complex.ofReal_add, add_comm, zd_pair_lemma j i h2.1 (by omega),
      Complex.ofReal_zero]
  · obtain ⟨ha, hb, rfl⟩ := h3
    rw [zd_mid_lemma_2 i ha hb]
    simp
  · obtain ⟨ha, hb, rfl⟩ := h3
    rw [zd_mid_lemma_2 i ha hb]
    simp
  · simp

lemma Zm_norm : ‖Zm k r‖ ≤ r := by
  apply norm_le_lemma_2 (Nat.cast_nonneg r)
  intro i j
  have hi := i.isLt
  unfold Zm
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · rw [normc_lemma]
    unfold zd
    split_ifs with ha hb
    · rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (by omega : r - i.val ≤ r)
    · simp
    · rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (by omega : i.val - (r + k) ≤ r)
  · simp

lemma cv_Zm_true (s : ℝ) (g : Mat k r) : cv true (Zm k r) s g = aDil k r (Real.exp (-s)) * g := by
  simp only [cv]
  rw [← exp_Zm (-s)]
  congr 2
  push_cast
  rw [neg_smul]

lemma cv_Zm_false (s : ℝ) (g : Mat k r) : cv false (Zm k r) s g = g * aDil k r (Real.exp s) := by
  simp only [cv]
  rw [exp_Zm]

lemma hasDerivAt_cv {H : Mat k r → E} (hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H) {Z g : Mat k r}
    (hZ : inLie k r Z) (hg : g ∈ GV k r) (b : Bool) (σ : ℝ) :
    HasDerivAt (fun x : ℝ => H (cv b Z x g)) (op b Z H (cv b Z σ g)) σ := by
  have hg' : cv b Z σ g ∈ GV k r := cv_mem hZ hg σ
  have hd := ckOn_diff 0 b hH hZ hg'
  have h1 : HasDerivAt (fun s => H (cv b Z s (cv b Z σ g))) (op b Z H (cv b Z σ g)) 0 :=
    hd.hasDerivAt
  have h2 := HasDerivAt.comp_sub_const σ σ (by rw [sub_self]; exact h1)
  convert h2 using 1
  funext x
  rw [← cv_add]
  congr 2
  ring

lemma mean_value {H : Mat k r → E} (hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H) {Z g : Mat k r}
    (hZ : inLie k r Z) (hg : g ∈ GV k r) (b : Bool) {lm B L : ℝ} (hlm : 0 ≤ lm)
    (hB : ∀ σ : ℝ, |σ| ≤ L → lm * ‖op b Z H (cv b Z σ g)‖ ≤ B) {s : ℝ} (hs : |s| ≤ L) :
    lm * ‖H (cv b Z s g) - H g‖ ≤ B * |s| := by
  have hL : 0 ≤ L := le_trans (abs_nonneg s) hs
  have hB0 : 0 ≤ B :=
    le_trans (mul_nonneg hlm (norm_nonneg _)) (hB 0 (by rw [abs_zero]; exact hL))
  rcases eq_or_lt_of_le hlm with h0 | hpos
  · rw [← h0, zero_mul]
    exact mul_nonneg hB0 (abs_nonneg s)
  · have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun σ => H (cv b Z σ g)) (f' := fun σ => op b Z H (cv b Z σ g)) (C := B / lm)
      (s := Set.Icc (-L) L)
      (fun x _ => (hasDerivAt_cv hH hZ hg b x).hasDerivWithinAt)
      (fun x hx => by
        rw [le_div_iff₀ hpos, mul_comm]
        exact hB x (abs_le.mpr hx))
      (convex_Icc _ _) (show (0 : ℝ) ∈ Set.Icc (-L) L from ⟨by linarith, hL⟩)
      (show s ∈ Set.Icc (-L) L from abs_le.mp hs)
    simp only [sub_zero, Real.norm_eq_abs] at hmv
    rw [cv_zero] at hmv
    have hne : lm ≠ 0 := hpos.ne'
    calc lm * ‖H (cv b Z s g) - H g‖ ≤ lm * (B / lm * |s|) := mul_le_mul_of_nonneg_left hmv hlm
      _ = B * |s| := by
        first
          | (field_simp; done)
          | (field_simp; ring)

lemma abs_log_le {t : ℝ} (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : |Real.log t| ≤ 2 * |t - 1| := by
  have hpos : 0 < t := by linarith [ht.1]
  have h2 := abs_inv_sub_one ht
  rw [abs_le]
  constructor
  · have h1 := Real.one_sub_inv_le_log_of_pos hpos
    linarith [le_abs_self (t⁻¹ - 1)]
  · have := Real.log_le_sub_one_of_pos hpos
    linarith [le_abs_self (t - 1), abs_nonneg (t - 1)]

lemma abs_log_le_log_two {t : ℝ} (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : |Real.log t| ≤ Real.log 2 := by
  obtain ⟨h1, h2⟩ := ht
  have hpos : 0 < t := by linarith
  rw [abs_le]
  constructor
  · have := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) h1
    rw [one_div, Real.log_inv] at this
    linarith
  · exact Real.log_le_log hpos h2

lemma exp_mem_I {σ : ℝ} (h : |σ| ≤ Real.log 2) : Real.exp σ ∈ Set.Icc (1 / 2 : ℝ) 2 := by
  rw [abs_le] at h
  rw [Set.mem_Icc]
  constructor
  · have := Real.exp_le_exp.mpr h.1
    rwa [Real.exp_neg, Real.exp_log (by norm_num), ← one_div] at this
  · have := Real.exp_le_exp.mpr h.2
    rwa [Real.exp_log (by norm_num)] at this

lemma cc_nonneg {F : Mat k r → E} {A c : ℝ} {m : ℕ} (h : CCle A m F c) : 0 ≤ c := by
  unfold CCle at h
  have h1 : (1 : Mat k r) ∈ GV k r := by
    show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  have := h.2 [] [] (by simp) (by simp) (by simp) 1 h1
  exact le_trans (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) A) (norm_nonneg _)) this

lemma cc_mono {F : Mat k r → E} {A c c' : ℝ} {m : ℕ} (h : CCle A m F c) (hc : c ≤ c') : CCle A m F c' := by
  unfold CCle at *
  exact ⟨h.1, fun u v hu hv hl g hg => (h.2 u v hu hv hl g hg).trans hc⟩

lemma aDil_one : aDil k r 1 = 1 := by
  rw [aDil_eq, ← Matrix.diagonal_one]
  congr 1
  funext i
  unfold dg
  split_ifs <;> simp

lemma sel_mem {t : ℝ × ℝ} (h1 : t.1 ∈ Set.Icc (1 / 2 : ℝ) 2) (h2 : t.2 ∈ Set.Icc (1 / 2 : ℝ) 2) (b : Bool) :
    sel t b ∈ Set.Icc (1 / 2 : ℝ) 2 := by
  cases b
  · exact h2
  · exact h1

lemma sel_sub_le (t : ℝ × ℝ) (b : Bool) : |sel t b - 1| ≤ |t.1 - 1| + |t.2 - 1| := by
  cases b <;> simp only [sel] <;> linarith [abs_nonneg (t.1 - 1), abs_nonneg (t.2 - 1)]

lemma one_le_K (r : ℕ) : (1 : ℝ) ≤ 4 ^ r := by
  exact one_le_pow₀ (by norm_num)

section

variable {t : ℝ × ℝ} (h1 : t.1 ∈ Set.Icc (1 / 2 : ℝ) 2) (h2 : t.2 ∈ Set.Icc (1 / 2 : ℝ) 2)

include h1 h2

lemma adj_lie (x : Bool × Mat k r) (hx : unitLie k r x.2) : inLie k r (adj t x).2 := by
  exact inLie_conj (aDil_mem k r _ (ne_zero_of_mem_I (sel_mem h1 h2 x.1))) hx.1

lemma adj_le (x : Bool × Mat k r) (hx : unitLie k r x.2) : ‖(adj t x).2‖ ≤ 4 ^ r := by
  have a1 := adj_norm (k := k) (sel_mem h1 h2 x.1) x.2
  have a2 := unit_norm_le hx
  calc ‖(adj t x).2‖ ≤ 4 ^ r * ‖x.2‖ := a1
    _ ≤ 4 ^ r * 1 := by gcongr
    _ = 4 ^ r := mul_one _

lemma adj_sub_le (x : Bool × Mat k r) (hx : unitLie k r x.2) :
    ‖(adj t x).2 - x.2‖ ≤ 8 * 4 ^ r * (|t.1 - 1| + |t.2 - 1|) := by
  have a1 := adj_sub_norm (k := k) (sel_mem h1 h2 x.1) x.2
  have a2 := unit_norm_le hx
  have a3 := sel_sub_le t x.1
  calc ‖(adj t x).2 - x.2‖ ≤ 8 * 4 ^ r * |sel t x.1 - 1| * ‖x.2‖ := a1
    _ ≤ 8 * 4 ^ r * (|t.1 - 1| + |t.2 - 1|) * 1 := by gcongr
    _ = 8 * 4 ^ r * (|t.1 - 1| + |t.2 - 1|) := mul_one _

lemma dl_mem {g : Mat k r} (hg : g ∈ GV k r) : (aDil k r t.1)⁻¹ * g * aDil k r t.2 ∈ GV k r := by
  rw [aDil_inv k r t.1 (ne_zero_of_mem_I h1)]
  exact gv_mul_lemma (gv_mul_lemma (aDil_mem k r _ (inv_ne_zero (ne_zero_of_mem_I h1))) hg)
    (aDil_mem k r _ (ne_zero_of_mem_I h2))

lemma unit_lr {u v : List (Mat k r)} (hu : ∀ X ∈ u, unitLie k r X) (hv : ∀ X ∈ v, unitLie k r X) :
    ∀ x ∈ lr u v, unitLie k r x.2 := by
  intro x hx
  simp only [lr, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
  · exact hu X hX
  · exact hv X hX

lemma dil_bound1 {F : Mat k r → E} {A c : ℝ} {m : ℕ} (hA : 0 ≤ A) (hF : CCle A m F c) :
    CCle A m (dl t F) (((4 : ℝ) ^ r) ^ A * ((4 ^ r) ^ m * c)) := by
  have ht1 := ne_zero_of_mem_I h1
  have ht2 := ne_zero_of_mem_I h2
  have hc0 : 0 ≤ c := cc_nonneg hF
  unfold CCle at *
  refine ⟨ckOn_dl t ht1 ht2 hF.1, ?_⟩
  intro u v hu hv hl g hg
  have hunit := unit_lr h1 h2 hu hv
  set w' := (lr u v).map (adj t) with hw'
  set g' := (aDil k r t.1)⁻¹ * g * aDil k r t.2 with hg'
  have hgd : g' ∈ GV k r := dl_mem h1 h2 hg
  have hlen : w'.length ≤ m := by
    rw [hw', List.length_map, length_lr]
    exact hl
  have hb := bound_scaled (A := A) hF w' (by rw [hw', List.map_map]; exact lrt_lr u v)
    (fun x hx => by
      rw [hw', List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact adj_lie h1 h2 y (hunit y hy))
    hlen g' hgd
  have hpn : pn w' ≤ (4 ^ r) ^ m := by
    calc pn w' ≤ (4 ^ r) ^ w'.length := pn_le_pow w' (4 ^ r) (fun x hx => by
          rw [hw', List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          exact adj_le h1 h2 y (hunit y hy))
      _ ≤ (4 ^ r) ^ m := pow_le_pow_right₀ (one_le_K r) hlen
  have hW : dLR u v (dl t F) g = W w' F g' := by
    rw [dLR_eq, W_dl t ht1 ht2]
    rfl
  have hgn : gN g ^ A ≤ ((4 : ℝ) ^ r) ^ A * gN g' ^ A := by
    have := gN_dil (k := k) (inv_mem_I h1) h2 hA g
    rw [← aDil_inv k r t.1 ht1] at this
    exact this
  rw [hW]
  have hWn := norm_nonneg (W w' F g')
  calc gN g ^ A * ‖W w' F g'‖ ≤ ((4 : ℝ) ^ r) ^ A * gN g' ^ A * ‖W w' F g'‖ :=
      mul_le_mul_of_nonneg_right hgn hWn
    _ = ((4 : ℝ) ^ r) ^ A * (gN g' ^ A * ‖W w' F g'‖) := by ring
    _ ≤ ((4 : ℝ) ^ r) ^ A * (pn w' * c) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ ((4 : ℝ) ^ r) ^ A * ((4 ^ r) ^ m * c) := by gcongr

lemma dil_bound2 {F : Mat k r → E} {A c : ℝ} {m : ℕ} (hA : 0 ≤ A) (hF : CCle A (m + 1) F c) :
    CCle A m (dl t F - F)
      (((4 : ℝ) ^ r) ^ A * (m * ((4 ^ r) ^ (m + 1) * (8 * 4 ^ r)) + 2 * r) * (|t.1 - 1| + |t.2 - 1|) * c) := by
  have n1 := ne_zero_of_mem_I h1
  have n2 := ne_zero_of_mem_I h2
  have p1 : 0 < t.1 := by linarith [h1.1]
  have p2 : 0 < t.2 := by linarith [h2.1]
  have hc := cc_nonneg hF
  have hFm : CkOn ((m : ℕ) : ℕ∞) (GV k r) F := ckOn_mono (Nat.le_succ m) hF.1
  have hsub : dl t F - F = dl t F + (-1 : ℂ) • F := by simp [sub_eq_add_neg]
  refine ⟨by rw [hsub]; exact ckOn_add (ckOn_dl t n1 n2 hFm) (ckOn_smul _ hFm), ?_⟩
  intro u v hu hv hlen g hg
  have hun := unit_lr h1 h2 hu hv
  have hL : AllLie (lr u v) := allLie_lr hu hv
  have hl : (lr u v).length ≤ m := by rw [length_lr]; exact hlen
  rw [dLR_eq, W_sub _ hL (ckOn_mono hl (ckOn_dl t n1 n2 hFm)) (ckOn_mono hl hFm) g hg, W_dl t n1 n2]
  show gN g ^ A * ‖W ((lr u v).map (adj t)) F ((aDil k r t.1)⁻¹ * g * aDil k r t.2) - W (lr u v) F g‖ ≤ _
  set κ : ℝ := ((4 : ℝ) ^ r) ^ A with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set δ : ℝ := |t.1 - 1| + |t.2 - 1| with hδ
  have hδ0 : 0 ≤ δ := by positivity
  set g' : Mat k r := (aDil k r t.1)⁻¹ * g * aDil k r t.2 with hg'
  have hg'G : g' ∈ GV k r := dl_mem h1 h2 hg
  set g₂ : Mat k r := g * aDil k r t.2 with hg₂
  have hg₂G : g₂ ∈ GV k r := WeylGroupFacts.uh_mul hg (aDil_mem k r t.2 n2)
  set H : Mat k r → E := W (lr u v) F with hH
  have hH1 : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H :=
    smooth_on_of_word_derivatives _ hL 1 (ckOn_mono (by omega) hF.1)
  have hpw : pn (lr u v) ≤ 1 := by
    have := pn_le_pow (lr u v) 1 (fun y hy => unit_norm_le (hun y hy))
    simpa using this

  have T1 : gN g ^ A * ‖W ((lr u v).map (adj t)) F g' - H g'‖ ≤
      κ * (m * ((4 ^ r) ^ (m + 1) * (8 * 4 ^ r * δ) * c)) := by
    have hN : gN g ^ A ≤ κ * gN g' ^ A := by
      have := gN_dil (k := k) (r := r) (inv_mem_I h1) h2 hA g
      rwa [← aDil_inv k r t.1 n1] at this
    have ht := telescope hF hc (one_le_K r) (adj t) (fun _ => rfl) (adj_lie h1 h2) (adj_le h1 h2)
      (adj_sub_le h1 h2) (lr u v) [] (by simp) hun (lrt_lr u v) (by simpa using le_trans hl (Nat.le_succ m))
      g' hg'G
    simp only [List.nil_append] at ht
    have hm : ((lr u v).length : ℝ) ≤ m := by exact_mod_cast hl
    calc gN g ^ A * ‖W ((lr u v).map (adj t)) F g' - H g'‖
        ≤ (κ * gN g' ^ A) * ‖W ((lr u v).map (adj t)) F g' - H g'‖ :=
          mul_le_mul_of_nonneg_right hN (norm_nonneg _)
      _ = κ * (gN g' ^ A * ‖W ((lr u v).map (adj t)) F g' - H g'‖) := by ring
      _ ≤ κ * (m * ((4 ^ r) ^ (m + 1) * (8 * 4 ^ r * δ) * c)) :=
          mul_le_mul_of_nonneg_left (le_trans ht (mul_le_mul_of_nonneg_right hm (by positivity))) hκ0

  have T2 : gN g ^ A * ‖H g' - H g₂‖ ≤ κ * (r * c) * |Real.log t.1| := by
    have hB : ∀ σ : ℝ, |σ| ≤ Real.log 2 →
        gN g ^ A * ‖op true (Zm k r) H (cv true (Zm k r) σ g₂)‖ ≤ κ * (r * c) := by
      intro σ hσ
      have hpt : cv true (Zm k r) σ g₂ ∈ GV k r := cv_mem Zm_lie hg₂G σ
      have hN : gN g ^ A ≤ κ * gN (cv true (Zm k r) σ g₂) ^ A := by
        have := gN_dil (k := k) (r := r) (exp_mem_I (by rwa [abs_neg] : |-σ| ≤ Real.log 2)) h2 hA g
        rwa [cv_Zm_true, hg₂, ← Matrix.mul_assoc]
      have hb := bound_scaled hF (lr (Zm k r :: u) v) (lrt_lr _ _)
        (by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Zm_lie
          · exact hL x hx)
        (by rw [length_lr, List.length_cons]; omega) _ hpt
      have hpn : pn (lr (Zm k r :: u) v) ≤ r := by
        have e : pn (lr (Zm k r :: u) v) = ‖Zm k r‖ * pn (lr u v) := pn_cons _ _
        rw [e]
        calc ‖Zm k r‖ * pn (lr u v) ≤ r * 1 := mul_le_mul Zm_norm hpw (pn_nonneg _) (by positivity)
          _ = r := by ring
      calc gN g ^ A * ‖op true (Zm k r) H (cv true (Zm k r) σ g₂)‖
          ≤ (κ * gN (cv true (Zm k r) σ g₂) ^ A) * ‖op true (Zm k r) H (cv true (Zm k r) σ g₂)‖ :=
            mul_le_mul_of_nonneg_right hN (norm_nonneg _)
        _ = κ * (gN (cv true (Zm k r) σ g₂) ^ A * ‖W (lr (Zm k r :: u) v) F (cv true (Zm k r) σ g₂)‖) := by
            rw [mul_assoc]; rfl
        _ ≤ κ * (r * c) :=
            mul_le_mul_of_nonneg_left (le_trans hb (mul_le_mul_of_nonneg_right hpn hc)) hκ0
    have h := mean_value hH1 Zm_lie hg₂G true (gN_rpow_nonneg g A) hB (abs_log_le_log_two h1)
    rwa [cv_Zm_true, Real.exp_neg, Real.exp_log p1, ← aDil_inv k r t.1 n1, hg₂, ← Matrix.mul_assoc] at h

  have T3 : gN g ^ A * ‖H g₂ - H g‖ ≤ κ * (r * c) * |Real.log t.2| := by
    have hB : ∀ σ : ℝ, |σ| ≤ Real.log 2 →
        gN g ^ A * ‖op false (Zm k r) H (cv false (Zm k r) σ g)‖ ≤ κ * (r * c) := by
      intro σ hσ
      have hpt : cv false (Zm k r) σ g ∈ GV k r := cv_mem Zm_lie hg σ
      have hN : gN g ^ A ≤ κ * gN (cv false (Zm k r) σ g) ^ A := by
        have := gN_dil (k := k) (r := r) (τ₁ := 1) (by norm_num) (exp_mem_I hσ) hA g
        rwa [aDil_one, Matrix.one_mul, ← cv_Zm_false] at this
      have hsp : lr u v = lr u [] ++ lr [] v := by simp [lr]
      have hsp2 : lr u (Zm k r :: v) = lr u [] ++ (false, Zm k r) :: lr [] v := by simp [lr]
      have hLv : AllLie (lr ([] : List (Mat k r)) v) := allLie_lr (by simp) hv
      have hcomm : op false (Zm k r) H (cv false (Zm k r) σ g) =
          W (lr u (Zm k r :: v)) F (cv false (Zm k r) σ g) := by
        rw [hH, hsp, W_append, op_W_comm Zm_lie u (fun X hX => (hu X hX).1) _
          (smooth_on_of_word_derivatives _ hLv _ (ckOn_mono (by rw [length_lr]; simp; omega) hF.1)) _ hpt, hsp2, W_append, W_cons]
      have hb := bound_scaled hF (lr u (Zm k r :: v)) (lrt_lr _ _)
        (by
          intro x hx
          rw [hsp2] at hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hL x (by rw [hsp]; exact List.mem_append_left _ hx)
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact Zm_lie
            · exact hL x (by rw [hsp]; exact List.mem_append_right _ hx))
        (by rw [length_lr, List.length_cons]; omega) _ hpt
      have hpn : pn (lr u (Zm k r :: v)) ≤ r := by
        have e : pn (lr u (Zm k r :: v)) = ‖Zm k r‖ * pn (lr u v) := by
          rw [hsp2, hsp, pn_append, pn_append, pn_cons]; ring
        rw [e]
        calc ‖Zm k r‖ * pn (lr u v) ≤ r * 1 := mul_le_mul Zm_norm hpw (pn_nonneg _) (by positivity)
          _ = r := by ring
      rw [hcomm]
      calc gN g ^ A * ‖W (lr u (Zm k r :: v)) F (cv false (Zm k r) σ g)‖
          ≤ (κ * gN (cv false (Zm k r) σ g) ^ A) * ‖W (lr u (Zm k r :: v)) F (cv false (Zm k r) σ g)‖ :=
            mul_le_mul_of_nonneg_right hN (norm_nonneg _)
        _ = κ * (gN (cv false (Zm k r) σ g) ^ A * ‖W (lr u (Zm k r :: v)) F (cv false (Zm k r) σ g)‖) := by
            ring
        _ ≤ κ * (r * c) :=
            mul_le_mul_of_nonneg_left (le_trans hb (mul_le_mul_of_nonneg_right hpn hc)) hκ0
    have h := mean_value hH1 Zm_lie hg false (gN_rpow_nonneg g A) hB (abs_log_le_log_two h2)
    rwa [cv_Zm_false, Real.exp_log p2] at h
  have l1 := abs_log_le h1
  have l2 := abs_log_le h2
  have hrc : 0 ≤ κ * (r * c) := by positivity
  have tri : ‖W ((lr u v).map (adj t)) F g' - H g‖ ≤
      ‖W ((lr u v).map (adj t)) F g' - H g'‖ + ‖H g' - H g₂‖ + ‖H g₂ - H g‖ := by
    have e : W ((lr u v).map (adj t)) F g' - H g =
        (W ((lr u v).map (adj t)) F g' - H g') + (H g' - H g₂) + (H g₂ - H g) := by abel
    rw [e]
    exact norm_add₃_le
  calc gN g ^ A * ‖W ((lr u v).map (adj t)) F g' - H g‖
      ≤ gN g ^ A * (‖W ((lr u v).map (adj t)) F g' - H g'‖ + ‖H g' - H g₂‖ + ‖H g₂ - H g‖) :=
        mul_le_mul_of_nonneg_left tri (gN_rpow_nonneg g A)
    _ = gN g ^ A * ‖W ((lr u v).map (adj t)) F g' - H g'‖ + gN g ^ A * ‖H g' - H g₂‖ +
          gN g ^ A * ‖H g₂ - H g‖ := by ring
    _ ≤ κ * (m * ((4 ^ r) ^ (m + 1) * (8 * 4 ^ r * δ) * c)) + κ * (r * c) * (2 * |t.1 - 1|) +
          κ * (r * c) * (2 * |t.2 - 1|) :=
        add_le_add (add_le_add T1 (le_trans T2 (mul_le_mul_of_nonneg_left l1 hrc)))
          (le_trans T3 (mul_le_mul_of_nonneg_left l2 hrc))
    _ = κ * (m * ((4 ^ r) ^ (m + 1) * (8 * 4 ^ r)) + 2 * r) * δ * c := by rw [hδ]; ring

end

end Formalism.FourierDecayAlt.P.B4

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4

theorem dilation_unipotent_measure : Formalism.FourierDecayAlt.B.DilN := by
  intro k r z t ht hz n hn
  have hn' := (WeylGroupFacts.nset_iff n).1 hn
  have hell : ell k r z (aDil k r t * n * (aDil k r t)⁻¹) = (t : ℂ) * ell k r z n := by
    unfold ell
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : a.val + 1 < r
    · simp only [h, dif_pos]
      rw [conj_apply k r t ht, mul_right_comm, dg_step k r t ht a h]
    · simp only [h, dif_neg, not_false_eq_true]
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [conj_apply k r t ht, dg_last k r t a h]
      by_cases hj : j.val < r ∨ r + k < j.val
      · rw [hz j hj]; simp
      · rw [dg_mid k r t⁻¹ j (by omega) (by omega)]; ring
  refine ⟨?_, hell, ?_⟩
  · rw [WeylGroupFacts.nset_iff]
    refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (aDil_mem k r t ht) hn'.1) (WeylGroupFacts.uh_inv (aDil_mem k r t ht)), ?_⟩
    intro i j hj hi
    rw [conj_apply k r t ht, hn'.2 i j hj hi]
    by_cases hij : i = j
    · subst hij
      simp [dg_mul_inv k r t ht i]
    · simp [hij]
  · unfold lam
    rw [hell, mul_left_comm, Complex.re_ofReal_mul]

theorem dilation_unipotent_weyl_measure : Formalism.FourierDecayAlt.B.DilUW := by
  intro k r z t h hh
  obtain ⟨hc, hr⟩ := WeylGroupFacts.uw_block hh
  ext i j
  rw [aDil_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hj : j.val < r ∨ r + k < j.val
  · rw [hc i j hj]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · by_cases hi : i.val < r ∨ r + k < i.val
    · rw [hr i j hi]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    · rw [dg_mid k r t i (by omega) (by omega), dg_mid k r t j (by omega) (by omega)]; ring

theorem matrix_coefficient_linear : Formalism.FourierDecayAlt.B.CCLin := by
  intro k r E _ _ A m F F' c c' a hF hF'
  obtain ⟨hF, hb⟩ := hF
  obtain ⟨hF', hb'⟩ := hF'
  refine ⟨⟨ckOn_add hF hF', ?_⟩, ⟨ckOn_smul a hF, ?_⟩⟩
  · intro u v hu hv hlen g hg
    have hl : (lr u v).length ≤ m := by rw [length_lr]; exact hlen
    rw [dLR_eq, W_add _ (allLie_lr hu hv) (ckOn_mono hl hF) (ckOn_mono hl hF') g hg, ← dLR_eq, ← dLR_eq]
    calc gN g ^ A * ‖dLR u v F g + dLR u v F' g‖
        ≤ gN g ^ A * (‖dLR u v F g‖ + ‖dLR u v F' g‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (gN_rpow_nonneg g A)
      _ = gN g ^ A * ‖dLR u v F g‖ + gN g ^ A * ‖dLR u v F' g‖ := by ring
      _ ≤ c + c' := add_le_add (hb u v hu hv hlen g hg) (hb' u v hu hv hlen g hg)
  · intro u v hu hv hlen g hg
    rw [dLR_eq, W_smul, ← dLR_eq, Pi.smul_apply, norm_smul]
    calc gN g ^ A * (‖a‖ * ‖dLR u v F g‖) = ‖a‖ * (gN g ^ A * ‖dLR u v F g‖) := by ring
      _ ≤ ‖a‖ * c := mul_le_mul_of_nonneg_left (hb u v hu hv hlen g hg) (norm_nonneg _)

theorem dilation_matrix_coefficient : Formalism.FourierDecayAlt.B.DilCC := by
  intro k r Wp Wq _ _ _ _ A hA
  refine ⟨((4 : ℝ) ^ r) ^ A * (4 ^ r) ^ 5 +
    ((4 : ℝ) ^ r) ^ A * (((4 : ℕ) : ℝ) * ((4 ^ r) ^ (4 + 1) * (8 * 4 ^ r)) + 2 * r), ?_⟩
  intro t ht F c hF
  obtain ⟨h1, h2⟩ := Set.mem_prod.mp ht
  have hc := cc_nonneg hF
  have hδ : 0 ≤ |t.1 - 1| + |t.2 - 1| := by positivity
  have a1 : (0 : ℝ) ≤ ((4 : ℝ) ^ r) ^ A * (4 ^ r) ^ 5 := by positivity
  have a2 : (0 : ℝ) ≤ ((4 : ℝ) ^ r) ^ A * (((4 : ℕ) : ℝ) * ((4 ^ r) ^ (4 + 1) * (8 * 4 ^ r)) + 2 * r) := by
    positivity
  constructor
  · refine cc_mono (dil_bound1 h1 h2 hA hF) ?_
    have := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right a2 :
      ((4 : ℝ) ^ r) ^ A * (4 ^ r) ^ 5 ≤ _) hc
    linarith
  · refine cc_mono (dil_bound2 h1 h2 hA hF) ?_
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left a1 :
      ((4 : ℝ) ^ r) ^ A * (((4 : ℕ) : ℝ) * ((4 ^ r) ^ (4 + 1) * (8 * 4 ^ r)) + 2 * r) ≤ _) hδ) hc
    exact this

end Formalism.FourierDecayAlt.P

import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentLeviRadicalCoordsHomeomorph
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselUnitaryHaarUniqueStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DensityInChartStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOnStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PowApplyEqZeroOfStrictUpper

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.NCoord
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.NLie

variable {k r : ℕ}

def TN (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | Xᴴ * Hpk k r + Hpk k r * X = 0 ∧
    (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → X i (eI k r a) = 0) ∧
    ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val → X i j = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro X Y ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
    refine ⟨?_, fun a i h => by simp [h2 a i h, g2 a i h], fun i j a b c => by simp [h3 i j a b c, g3 i j a b c]⟩
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, h1, g1, add_zero]
  smul_mem' := by
    rintro c X ⟨h1, h2, h3⟩
    refine ⟨?_, fun a i h => by simp [h2 a i h], fun i j a b c => by simp [h3 i j a b c]⟩
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, star_trivial, ← smul_add, h1, smul_zero]

theorem tangent_mem {γ : ℝ → Mat k r} {X : Mat k r} (h : ∀ t, γ t ∈ Nset k r) (h0 : γ 0 = 1)
    (hd : ∀ i j, HasDerivAt (fun t => γ t i j) (X i j) 0) : X ∈ TN k r := by
  have hc : ∀ i j c, (∀ t, γ t i j = c) → X i j = 0 := fun i j c hc =>
    (hd i j).unique (by simp only [hc]; exact hasDerivAt_const _ _)
  refine ⟨?_, fun a i hi => hc _ _ _ fun t => (h t).2.1 a i hi, fun i j a b c => hc _ _ _ fun t => (h t).2.2 i j a b c⟩
  ext i j
  have h1 : HasDerivAt (fun t => ∑ l, (∑ m, star (γ t m i) * Hpk k r m l) * γ t l j)
      (∑ l, ((∑ m, star (X m i) * Hpk k r m l) * γ 0 l j + (∑ m, star (γ 0 m i) * Hpk k r m l) * X l j)) 0 :=
    HasDerivAt.fun_sum fun l _ => (HasDerivAt.fun_sum fun m _ => ((hd m i).star).mul_const _).fun_mul (hd l j)
  have h2 : (fun t => ∑ l, (∑ m, star (γ t m i) * Hpk k r m l) * γ t l j) = fun _ => Hpk k r i j := by
    funext t
    have : (γ t)ᴴ * Hpk k r * γ t = Hpk k r := (h t).1
    simpa [Matrix.mul_apply] using congrFun (congrFun this i) j
  rw [h2] at h1
  have h3 := h1.unique (hasDerivAt_const _ _)
  rw [h0] at h3
  simpa [Matrix.mul_apply, Matrix.one_apply, Finset.sum_add_distrib, apply_ite star] using h3

theorem TN_rel {X : Mat k r} (hX : X ∈ TN k r) (i j : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ fun l => X l j) i = -star ((Hpk k r *ᵥ fun l => X l i) j) := by
  have h := congrFun (congrFun hX.1 i) j
  have hH : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  have : Xᴴ * Hpk k r = (Hpk k r * X)ᴴ := by rw [conjTranspose_mul, hH]
  rw [this] at h
  simp only [Matrix.add_apply, conjTranspose_apply, Matrix.mul_apply, Matrix.zero_apply] at h
  simp only [Matrix.mulVec, dotProduct]
  linear_combination h

theorem TN_ss {X : Mat k r} (hX : X ∈ TN k r) (a b : Fin r) :
    X (esI k r a) (esI k r b) = -star (X (eI k r b) (eI k r a)) := by
  simpa only [H_e, H_es] using TN_rel hX (eI k r a) (esI k r b)

theorem TN_es {X : Mat k r} (hX : X ∈ TN k r) (a b : Fin r) :
    X (eI k r a) (esI k r b) = -star (X (eI k r b) (esI k r a)) := by
  simpa only [H_e, H_es] using TN_rel hX (esI k r a) (esI k r b)

theorem TN_ew {X : Mat k r} (hX : X ∈ TN k r) (a : Fin r) (j : Fin (k + 1)) :
    ‖X (eI k r a) (wI k r j)‖ = ‖X (wI k r j) (esI k r a)‖ := by
  have h := TN_rel hX (esI k r a) (wI k r j)
  rw [H_es, H_w, Hb, Matrix.mulVec_diagonal] at h
  rw [h]
  split_ifs <;> simp

theorem TN_upper {X : Mat k r} (hX : X ∈ TN k r) (i j : Fin (2 * r + k + 1)) (h : j.val ≤ i.val) : X i j = 0 := by
  rcases idx_cases j with ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩
  · exact hX.2.1 b i h
  · have := b.isLt
    have h1 : (wI k r b).val = r + b.val := rfl
    exact hX.2.2 _ _ (by omega) (by omega) (by omega)
  · have := b.isLt
    have h1 : (esI k r b).val = 2 * r + k - b.val := rfl
    have := i.isLt
    obtain ⟨a, rfl⟩ : ∃ a, i = esI k r a := ⟨⟨2 * r + k - i.val, by omega⟩, Fin.ext (by simp [esI]; omega)⟩
    have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
    have := a.isLt
    rw [TN_ss hX, hX.2.1 a (eI k r b) (by show a.val ≤ b.val; omega)]
    simp

theorem pow_upper {m : ℕ} {X : Matrix (Fin m) (Fin m) ℂ} (hX : ∀ i j : Fin m, j.val ≤ i.val → X i j = 0) (n : ℕ) :
    ∀ i j : Fin m, j.val < i.val + n → (X ^ n) i j = 0 := by
  first
  | exact @_root_.GlobalTheory.StrictUpperNilpotentFlagMeasures.pow_apply_eq_zero_of_strictUpper
  | exact _root_.GlobalTheory.StrictUpperNilpotentFlagMeasures.pow_apply_eq_zero_of_strictUpper
  | (apply _root_.GlobalTheory.StrictUpperNilpotentFlagMeasures.pow_apply_eq_zero_of_strictUpper <;> assumption)
  | (intros; apply _root_.GlobalTheory.StrictUpperNilpotentFlagMeasures.pow_apply_eq_zero_of_strictUpper <;> assumption)
  | (intros; apply @_root_.GlobalTheory.StrictUpperNilpotentFlagMeasures.pow_apply_eq_zero_of_strictUpper <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.StrictUpperNilpotentFlagMeasures.pow_apply_eq_zero_of_strictUpper ..)

theorem exp_upper {m : ℕ} {X : Matrix (Fin m) (Fin m) ℂ} (hX : ∀ i j : Fin m, j.val ≤ i.val → X i j = 0) :
    NormedSpace.exp X = ∑ n ∈ Finset.range (m + 2), ((n.factorial : ℂ)⁻¹) • X ^ n := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  refine tsum_eq_sum fun n hn => ?_
  have : X ^ n = 0 := by
    ext i j
    rw [Finset.mem_range] at hn
    exact pow_upper hX n i j (by omega)
  rw [this, smul_zero]

theorem exp_inj_upper {m : ℕ} {X Y : Matrix (Fin m) (Fin m) ℂ} (hX : ∀ i j : Fin m, j.val ≤ i.val → X i j = 0)
    (hY : ∀ i j : Fin m, j.val ≤ i.val → Y i j = 0) (h : NormedSpace.exp X = NormedSpace.exp Y) : X = Y := by
  ext i j
  let P : Matrix (Fin m) (Fin m) ℂ → Polynomial ℂ := fun Z =>
    ∑ n ∈ Finset.range (m + 2), Polynomial.monomial n ((n.factorial : ℂ)⁻¹ * (Z ^ n) i j)
  have hP : ∀ Z : Matrix (Fin m) (Fin m) ℂ, (∀ i j : Fin m, j.val ≤ i.val → Z i j = 0) → ∀ t : ℕ,
      (P Z).eval (t : ℂ) = (NormedSpace.exp Z ^ t) i j := by
    intro Z hZ t
    rw [← Matrix.exp_nsmul, exp_upper (X := t • Z) (fun i j h => by simp [hZ i j h]), Matrix.sum_apply,
      Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_pow]
    simp only [Polynomial.eval_monomial, Matrix.smul_apply, smul_eq_mul]
    ring
  have hc : ∀ Z : Matrix (Fin m) (Fin m) ℂ, (P Z).coeff 1 = Z i j := by
    intro Z
    simp [P, Polynomial.coeff_monomial]
  have : P X = P Y := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ (Set.infinite_of_injective_forall_mem
      (f := fun t : ℕ => (t : ℂ)) Nat.cast_injective fun t => ?_)
    show (P X).eval (t : ℂ) = (P Y).eval (t : ℂ)
    rw [hP X hX, hP Y hY, h]
  rw [← hc X, this, hc]

theorem exp_mem {X : Mat k r} (hX : X ∈ TN k r) : NormedSpace.exp X ∈ Nset k r := by
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have key : ∀ i j : Fin (2 * r + k + 1), (∀ l : Fin (2 * r + k + 1), i.val ≤ l.val → X l j = 0) →
      NormedSpace.exp X i j = if i = j then 1 else 0 := by
    intro i j h
    rw [exp_upper (TN_upper hX), Finset.sum_range_succ', Matrix.add_apply, Matrix.sum_apply, Finset.sum_eq_zero]
    · simp [Matrix.one_apply]
    · intro n _
      rw [Matrix.smul_apply, pow_succ, Matrix.mul_apply, Finset.sum_eq_zero, smul_zero]
      intro l _
      by_cases hl : l.val < i.val
      · rw [pow_upper (TN_upper hX) n i l (by omega), zero_mul]
      · rw [h l (by omega), mul_zero]
  refine ⟨?_, fun a i hi => key _ _ fun l hl => hX.2.1 a l (by omega),
    fun i j a b c => key _ _ fun l hl => hX.2.2 l j a b (by omega)⟩
  show (NormedSpace.exp X)ᴴ * Hpk k r * NormedSpace.exp X = Hpk k r
  have hi : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hH
  have h1 : Xᴴ = Hpk k r * (-X) * (Hpk k r)⁻¹ := by
    have h2 : Xᴴ * Hpk k r = Hpk k r * (-X) := by rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hX.1
    rw [hi, ← h2, Matrix.mul_assoc, hH, Matrix.mul_one]
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det _).2
    (Matrix.isUnit_det_of_left_inverse hH)), hi, Matrix.mul_assoc _ (Hpk k r) (Hpk k r), hH, Matrix.mul_one, Matrix.mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left, neg_add_cancel, NormedSpace.exp_zero, Matrix.mul_one]

open scoped Matrix.Norms.Operator in
theorem deriv_exp {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let e : Matrix (Fin m) (Fin m) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact e.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem lieOf_eq : lieOf (Nset k r) = TN k r := by
  ext X
  constructor
  · intro h
    exact tangent_mem (γ := fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) h (by simp) (deriv_exp X)
  · intro h t
    exact exp_mem ((TN k r).smul_mem t h)

def rl (m : ℕ) : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun X := WithLp.toLp 2 (realifyFun X)
  map_add' X Y := by ext p; simp only [realifyFun, PiLp.add_apply]; split_ifs <;> simp
  map_smul' c X := by ext p; simp only [realifyFun, PiLp.smul_apply]; split_ifs <;> simp

theorem unrealify_rl {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : unrealify (rl m X) = X := by
  ext i j; apply Complex.ext <;> simp [unrealify, rl, realifyFun]

theorem norm_rl {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : ‖rl m X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, rl, realifyFun, LinearMap.coe_mk, AddHom.coe_mk,
    Real.norm_eq_abs, sq_abs, Complex.sq_norm, Complex.normSq_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp; ring

theorem lieE_eq : lieE (Nset k r) = (TN k r).map (rl _) := by
  rw [lieE, lieOf_eq, ← Submodule.span_eq ((TN k r).map (rl _))]
  rfl

theorem mem_lieE {x : EuclideanSpace ℝ _} (hx : x ∈ lieE (Nset k r)) : unrealify x ∈ TN k r := by
  rw [lieE_eq] at hx
  obtain ⟨X, hX, rfl⟩ := hx
  rwa [unrealify_rl]

theorem rl_unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : rl m (unrealify x) = x := by
  ext ⟨i, j, b⟩; cases b <;> simp [unrealify, rl, realifyFun]

theorem sum_three' (f : Fin (2 * r + k + 1) → ℝ) :
    ∑ i, f i = ∑ a, f (eI k r a) + ∑ j, f (wI k r j) + ∑ a, f (esI k r a) := by
  exact_mod_cast sum_three fun i => (f i : ℂ)

theorem sum_UT (f : Fin r → Fin r → ℝ) :
    ∑ a, ∑ b, f a b = ∑ p : UT r, f p.1.1 p.1.2 + ∑ p : UT r, f p.1.2 p.1.1 + ∑ a, f a a := by
  have h : ∀ g : Fin r → Fin r → ℝ, ∑ p : UT r, g p.1.1 p.1.2 = ∑ a, ∑ b, if a < b then g a b else 0 := by
    intro g
    rw [← Fintype.sum_prod_type' (fun a b => if a < b then g a b else 0), ← Finset.sum_filter]
    exact (Finset.sum_subtype (p := fun p : Fin r × Fin r => p.1 < p.2) _ (by simp) fun p => g p.1 p.2).symm
  rw [h f, h fun a b => f b a, Finset.sum_comm (f := fun a b => if a < b then f b a else 0),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show f a a = ∑ b, if a = b then f a b else 0 by simp, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.not_gt, h.ne]
  · simp [h]
  · simp [h, h.not_gt, h.ne']

theorem card_UT : 2 * Fintype.card (UT r) = r * (r - 1) := by
  have h := sum_UT (r := r) fun _ _ => 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  have h' : r * r = Fintype.card (UT r) + Fintype.card (UT r) + r := by exact_mod_cast h
  rw [Nat.mul_sub_one]; omega

theorem norm_TN {X : Mat k r} (hX : X ∈ TN k r) : ‖rl _ X‖ ^ 2 =
    2 * ∑ p : UT r, ‖X (eI k r p.1.1) (eI k r p.1.2)‖ ^ 2 + (2 * ∑ b, ∑ j, ‖X (wI k r j) (esI k r b)‖ ^ 2 +
      (2 * ∑ p : UT r, ‖X (eI k r p.1.1) (esI k r p.1.2)‖ ^ 2 + ∑ a, (X (eI k r a) (esI k r a)).im ^ 2)) := by
  have hwe : ∀ j a, X (wI k r j) (eI k r a) = 0 := fun j a => hX.2.1 a _ (by simp [wI]; omega)
  have hse : ∀ b a, X (esI k r b) (eI k r a) = 0 := fun j a => hX.2.1 a _ (by simp [esI]; omega)
  have hww : ∀ j l, X (wI k r j) (wI k r l) = 0 := fun j l =>
    hX.2.2 _ _ (by simp [wI]) (by simp [wI]; omega) (by simp [wI])
  have hsw : ∀ b l, X (esI k r b) (wI k r l) = 0 := fun j l =>
    hX.2.2 _ _ (by simp [wI]) (by simp [wI]; omega) (by simp [esI]; omega)
  have hee : ∑ a, ∑ b, ‖X (eI k r a) (eI k r b)‖ ^ 2 = ∑ p : UT r, ‖X (eI k r p.1.1) (eI k r p.1.2)‖ ^ 2 := by
    rw [sum_UT, Finset.sum_eq_zero (s := Finset.univ) (f := fun a => ‖X (eI k r a) (eI k r a)‖ ^ 2)
      fun a _ => by simp [hX.2.1 a (eI k r a) le_rfl],
      Finset.sum_eq_zero (s := Finset.univ) (f := fun p : UT r => ‖X (eI k r p.1.2) (eI k r p.1.1)‖ ^ 2)
      fun p _ => by simp [hX.2.1 p.1.1 (eI k r p.1.2) p.2.le], add_zero, add_zero]
  have hes : ∑ a, ∑ b, ‖X (eI k r a) (esI k r b)‖ ^ 2 =
      2 * ∑ p : UT r, ‖X (eI k r p.1.1) (esI k r p.1.2)‖ ^ 2 + ∑ a, (X (eI k r a) (esI k r a)).im ^ 2 := by
    rw [sum_UT, two_mul]
    congr 2
    · exact Finset.sum_congr rfl fun p _ => by rw [TN_es hX]; simp
    · funext a
      have := congrArg Complex.re (TN_es hX a a)
      simp at this
      rw [Complex.sq_norm, Complex.normSq_apply, show (X (eI k r a) (esI k r a)).re = 0 by linarith]
      ring
  rw [norm_rl]
  simp only [sum_three' (k := k) (r := r), Finset.sum_add_distrib, hwe, hse, hww, hsw, TN_ew hX, TN_ss hX,
    norm_neg, norm_star]
  rw [hes, Finset.sum_comm (f := fun a b => ‖X (eI k r b) (eI k r a)‖ ^ 2), hee,
    Finset.sum_comm (f := fun j b => ‖X (wI k r j) (esI k r b)‖ ^ 2)]
  simp; ring

abbrev EE (k r : ℕ) := (UT r → ℂ) × PPar k r

def Phi (q : EE k r) : Mat k r := uEmb k r (upper q.1) * pOf k r q.2

theorem Phi_mem (q : EE k r) : Phi q ∈ Nset k r := (coord_homeo k r).1.mapsTo trivial

theorem upper_zero : upper (0 : UT r → ℂ) = 1 := by
  ext a b
  by_cases h : a < b <;> simp [upper, h, Matrix.one_apply]
  exact h.ne

theorem Phi_zero : Phi (0 : EE k r) = 1 := by
  rw [Phi, Prod.fst_zero, upper_zero, GlobalTheory.Amp.UEmb.uEmb_one, Matrix.one_mul]
  ext i j
  simp [pOf, pEl, skewM, herm, Matrix.one_apply]

theorem smooth_upper (a b : Fin r) : ContDiff ℝ 1 fun x : UT r → ℂ => upper x a b := by
  unfold upper
  split_ifs <;> fun_prop

theorem smooth_upper_inv (a b : Fin r) : ContDiff ℝ 1 fun x : UT r → ℂ => (upper x)⁻¹ a b := by
  have : (fun x : UT r → ℂ => (upper x)⁻¹ a b) = fun x => (upper x).adjugate a b := by
    funext x; rw [Matrix.inv_def, det_upper]; simp
  rw [this]
  simp only [Matrix.adjugate_apply, Matrix.det_apply', Matrix.updateRow_apply]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  split_ifs
  · exact contDiff_const
  · exact smooth_upper _ _

theorem smooth_star {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℂ} (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 fun x => star (f x) := Complex.conjCLE.contDiff.comp hf

theorem smooth_Phi (i j : Fin (2 * r + k + 1)) : ContDiff ℝ 1 fun q : EE k r => Phi q i j := by
  simp only [Phi, Matrix.mul_apply]
  refine ContDiff.sum fun l _ => ContDiff.mul ?_ ?_
  · refine ContDiff.comp (g := fun x => uEmb k r (upper x) i l) ?_ contDiff_fst
    unfold uEmb
    split_ifs
    · exact smooth_upper _ _
    · exact smooth_star (smooth_upper_inv _ _)
    all_goals exact contDiff_const
  · refine ContDiff.comp (g := fun x => pOf k r x l j) ?_ contDiff_snd
    have hB : ∀ a b, ContDiff ℝ 1 fun x : PPar k r => x.1 a b := fun a b => by fun_prop
    have hS : ∀ a b, ContDiff ℝ 1 fun x : PPar k r => skewM x.2.1 x.2.2 a b := fun a b => by
      unfold skewM
      split_ifs
      · fun_prop
      · exact (smooth_star (by fun_prop)).neg
      · exact (Complex.ofRealCLM.contDiff.comp (by fun_prop)).mul contDiff_const
    unfold pOf pEl herm Matrix.mulVec dotProduct
    simp only [Pi.star_apply]
    split_ifs
    · exact contDiff_const
    · exact (ContDiff.sum fun _ _ => (smooth_star (hB _ _)).mul contDiff_const).neg
    · exact hB _ _
    · exact (hS _ _).sub ((ContDiff.sum fun _ _ => (smooth_star (hB _ _)).mul
        (ContDiff.sum fun _ _ => contDiff_const.mul (hB _ _))).div_const _)
    · exact contDiff_const

def Dm (k r : ℕ) : EE k r →ₗ[ℝ] Mat k r where
  toFun v := Matrix.of fun i j => fderiv ℝ (fun q : EE k r => Phi q i j) 0 v
  map_add' v w := by ext i j; simp
  map_smul' c v := by ext i j; simp

theorem deriv_Phi (v : EE k r) (i j : Fin (2 * r + k + 1)) :
    HasDerivAt (fun t : ℝ => Phi (t • v) i j) (Dm k r v i j) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t • v) v 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have h2 := ((smooth_Phi (k := k) (r := r) i j).differentiable (by simp) 0).hasFDerivAt
  exact h2.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)

theorem Dm_mem (v : EE k r) : Dm k r v ∈ TN k r :=
  tangent_mem (γ := fun t : ℝ => Phi (t • v)) (fun _ => Phi_mem _) (by simp [Phi_zero]) (deriv_Phi v)

theorem deriv_lin (c : ℂ) : HasDerivAt (fun t : ℝ => t • c) c 0 := by
  simpa using (hasDerivAt_id (0 : ℝ)).smul_const c

theorem Dm_ee (v : EE k r) (p : UT r) : Dm k r v (eI k r p.1.1) (eI k r p.1.2) = v.1 p := by
  refine (deriv_Phi v _ _).unique ?_
  have : ∀ q : EE k r, Phi q (eI k r p.1.1) (eI k r p.1.2) = q.1 p := fun q =>
    congrFun (congrArg Prod.fst (cOf_coord q)) p
  simp only [this]
  exact deriv_lin _

theorem Dm_ws (v : EE k r) (j : Fin (k + 1)) (b : Fin r) : Dm k r v (wI k r j) (esI k r b) = v.2.1 b j := by
  refine (deriv_Phi v _ _).unique ?_
  have : ∀ q : EE k r, Phi q (wI k r j) (esI k r b) = q.2.1 b j := fun q => by
    rw [Phi, Matrix.mul_apply, GlobalTheory.Amp.UEmb.sum_idx]
    have h := congrFun (congrFun (Bof_pEl q.2.1 (skewM q.2.2.1 q.2.2.2)) b) j
    change ∑ a, uEmb k r _ (GlobalTheory.Amp.UEmb.mI k r j) _ * _ + (∑ a, uEmb k r _ (GlobalTheory.Amp.UEmb.mI k r j) _ * _ +
      ∑ a, uEmb k r _ (GlobalTheory.Amp.UEmb.mI k r j) _ * _) = _
    simp [GlobalTheory.Amp.UEmb.u_me, GlobalTheory.Amp.UEmb.u_mm, GlobalTheory.Amp.UEmb.u_ms]
    exact h
  simp only [this]
  exact deriv_lin _

theorem Dm_es (v : EE k r) (a b : Fin r) : Dm k r v (eI k r a) (esI k r b) = skewM v.2.2.1 v.2.2.2 a b := by
  refine (deriv_Phi v _ _).unique ?_
  have h1 : ∀ q : EE k r, Phi q (eI k r a) (esI k r b) =
      ∑ c, upper q.1 a c * (skewM q.2.2.1 q.2.2.2 c b - herm (Hb k) (q.2.1 b) (q.2.1 c) / 2) := fun q => by
    rw [Phi, Matrix.mul_apply, GlobalTheory.Amp.UEmb.sum_idx]
    simp only [GlobalTheory.Amp.UEmb.u_ee, GlobalTheory.Amp.UEmb.u_em, GlobalTheory.Amp.UEmb.u_es, zero_mul, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h := congrFun (congrFun (Sof_pEl q.2.1 (skewM q.2.2.1 q.2.2.2)) c) b
    rw [Sof, Bof_pEl] at h
    rw [← h, pOf]; ring
  have h2 : ∀ t : ℝ, Phi (t • v) (eI k r a) (esI k r b) =
      ∑ c, ((1 : Matrix (Fin r) (Fin r) ℂ) a c + t • (upper v.1 a c - (1 : Matrix (Fin r) (Fin r) ℂ) a c)) *
        (t • skewM v.2.2.1 v.2.2.2 c b - (t • (1 : ℂ)) * (t • (herm (Hb k) (v.2.1 b) (v.2.1 c) / 2))) := fun t => by
    rw [h1]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    · by_cases h : a < c
      · simp [upper, h, Matrix.one_apply, h.ne]
      · simp [upper, h, Matrix.one_apply]
    · congr 1
      · unfold skewM
        split_ifs <;> simp [mul_assoc]
      · simp [herm, Matrix.mulVec_smul, mul_div_assoc]
  simp only [h2]
  have h3 := HasDerivAt.fun_sum (u := Finset.univ) fun (c : Fin r) _ =>
    ((deriv_lin (upper v.1 a c - (1 : Matrix (Fin r) (Fin r) ℂ) a c)).const_add
      ((1 : Matrix (Fin r) (Fin r) ℂ) a c)).fun_mul ((deriv_lin (skewM v.2.2.1 v.2.2.2 c b)).fun_sub
        ((deriv_lin 1).fun_mul (deriv_lin (herm (Hb k) (v.2.1 b) (v.2.1 c) / 2))))
  convert h3 using 1
  simp [Matrix.one_apply]

theorem norm_Dm (v : EE k r) : ‖rl _ (Dm k r v)‖ ^ 2 =
    2 * ∑ p, ‖v.1 p‖ ^ 2 + (2 * ∑ b, ∑ j, ‖v.2.1 b j‖ ^ 2 + (2 * ∑ p, ‖v.2.2.1 p‖ ^ 2 + ∑ a, v.2.2.2 a ^ 2)) := by
  rw [norm_TN (Dm_mem v)]
  simp only [Dm_ee, Dm_ws, Dm_es]
  congr 5
  · funext p; simp [skewM, p.2]
  · funext a; simp [skewM]

theorem Dm_surj {X : Mat k r} (hX : X ∈ TN k r) : ∃ v, Dm k r v = X := by
  let v : EE k r := (fun p => X (eI k r p.1.1) (eI k r p.1.2), fun b j => X (wI k r j) (esI k r b),
    fun p => X (eI k r p.1.1) (esI k r p.1.2), fun a => (X (eI k r a) (esI k r a)).im)
  refine ⟨v, ?_⟩
  have h := norm_TN ((TN k r).sub_mem (Dm_mem v) hX)
  simp only [Matrix.sub_apply, Dm_ee, Dm_ws, Dm_es] at h
  have h1 : ∀ p : UT r, skewM v.2.2.1 v.2.2.2 p.1.1 p.1.2 = X (eI k r p.1.1) (esI k r p.1.2) := fun p => by
    simp [skewM, p.2, v]
  have h2 : ∀ a, (skewM v.2.2.1 v.2.2.2 a a).im = (X (eI k r a) (esI k r a)).im := fun p => by
    simp [skewM, v]
  simp only [h1, h2, Complex.sub_im, v, sub_self] at h
  have h3 : rl _ (Dm k r v - X) = 0 := by simpa using h
  rw [← sub_eq_zero, ← unrealify_rl (Dm k r v - X), h3, ← map_zero (rl _), unrealify_rl]

theorem Dm_inj : Function.Injective fun v : EE k r => rl _ (Dm k r v) := by
  refine (injective_iff_map_eq_zero ((rl _).comp (Dm k r))).2 fun v hv => ?_
  have hv' : Dm k r v = 0 := by
    rw [← unrealify_rl (Dm k r v), show rl _ (Dm k r v) = 0 from hv, ← map_zero (rl _), unrealify_rl]
  obtain ⟨x, B, s, t⟩ := v
  simp only [Prod.mk_eq_zero]
  refine ⟨funext fun p => ?_, funext fun b => funext fun j => ?_, funext fun p => ?_, funext fun a => ?_⟩
  · simpa [hv'] using (Dm_ee (x, B, s, t) p).symm
  · simpa [hv'] using (Dm_ws (x, B, s, t) j b).symm
  · simpa [hv', skewM, p.2] using (Dm_es (x, B, s, t) p.1.1 p.1.2).symm
  · simpa [hv', skewM] using (Dm_es (x, B, s, t) a a).symm

def LL (k r : ℕ) : EE k r ≃L[ℝ] lieE (Nset k r) :=
  (LinearEquiv.ofBijective (((rl _).comp (Dm k r)).codRestrict (lieE (Nset k r))
    fun v => by rw [lieE_eq]; exact ⟨_, Dm_mem v, rfl⟩)
    ⟨fun v w h => Dm_inj (congrArg Subtype.val h), fun x => by
      obtain ⟨v, hv⟩ := Dm_surj (mem_lieE x.2)
      exact ⟨v, Subtype.ext (by show rl _ (Dm k r v) = _; rw [hv, rl_unrealify])⟩⟩).toContinuousLinearEquiv

theorem LL_val (v : EE k r) : (LL k r v : EuclideanSpace ℝ _) = rl _ (Dm k r v) := rfl

theorem gauss_pi (ι : Type) [Fintype ι] :
    ∫ x : ι → ℂ, Real.exp (-(2 * ∑ p, ‖x p‖ ^ 2)) = (Real.pi / 2) ^ Fintype.card ι := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) (b := 2) two_pos
  have h2 := integral_fintype_prod_volume_eq_pow (ι := ι) fun z : ℂ => Real.exp (-2 * ‖z‖ ^ 2)
  rw [h] at h2
  simp only [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.mul_sum, neg_mul] at h2
  simpa [← Finset.mul_sum] using h2

theorem gaussian_integral_complex_matrix (ι κ : Type) [Fintype ι] [Fintype κ] :
    ∫ x : ι → κ → ℂ, Real.exp (-(2 * ∑ p, ∑ j, ‖x p j‖ ^ 2)) = (Real.pi / 2) ^ (Fintype.card ι * Fintype.card κ) := by
  have h2 := integral_fintype_prod_volume_eq_pow (ι := ι) fun z : κ → ℂ => Real.exp (-(2 * ∑ j, ‖z j‖ ^ 2))
  rw [gauss_pi, ← pow_mul, mul_comm] at h2
  simpa only [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.mul_sum] using h2

theorem gauss_re (ι : Type) [Fintype ι] :
    ∫ x : ι → ℝ, Real.exp (-(∑ p, x p ^ 2)) = √Real.pi ^ Fintype.card ι := by
  have h2 := integral_fintype_prod_volume_eq_pow (ι := ι) fun z : ℝ => Real.exp (-1 * z ^ 2)
  rw [integral_gaussian] at h2
  simpa [← Real.exp_sum] using h2

theorem gauss_EE : ∫ v : EE k r, Real.exp (-1 * ‖LL k r v‖ ^ 2) =
    (Real.pi / 2) ^ (r * (k + 1) + r * (r - 1)) * √Real.pi ^ r := by
  have : ∀ v : EE k r, Real.exp (-1 * ‖LL k r v‖ ^ 2) = Real.exp (-(2 * ∑ p, ‖v.1 p‖ ^ 2)) *
      (fun q : PPar k r => Real.exp (-(2 * ∑ b, ∑ j, ‖q.1 b j‖ ^ 2)) *
        (fun w : (UT r → ℂ) × (Fin r → ℝ) => Real.exp (-(2 * ∑ p, ‖w.1 p‖ ^ 2)) * Real.exp (-(∑ a, w.2 a ^ 2))) q.2)
          v.2 := fun v => by
    rw [Submodule.coe_norm, LL_val, norm_Dm]
    simp only [← Real.exp_add]
    congr 1; ring
  simp only [this]
  rw [Measure.volume_eq_prod, integral_prod_mul (fun x : UT r → ℂ => Real.exp (-(2 * ∑ p, ‖x p‖ ^ 2)))
      (fun q : PPar k r => Real.exp (-(2 * ∑ b, ∑ j, ‖q.1 b j‖ ^ 2)) *
        (Real.exp (-(2 * ∑ p, ‖q.2.1 p‖ ^ 2)) * Real.exp (-(∑ a, q.2.2 a ^ 2)))),
    Measure.volume_eq_prod, integral_prod_mul (fun x : Fin r → Fin (k + 1) → ℂ => Real.exp (-(2 * ∑ b, ∑ j, ‖x b j‖ ^ 2)))
      (fun w : (UT r → ℂ) × (Fin r → ℝ) => Real.exp (-(2 * ∑ p, ‖w.1 p‖ ^ 2)) * Real.exp (-(∑ a, w.2 a ^ 2))),
    Measure.volume_eq_prod, integral_prod_mul (fun x : UT r → ℂ => Real.exp (-(2 * ∑ p, ‖x p‖ ^ 2)))
      (fun x : Fin r → ℝ => Real.exp (-(∑ a, x a ^ 2))), gauss_pi, gaussian_integral_complex_matrix, gauss_re, ← card_UT]
  simp only [Fintype.card_fin]
  ring

theorem finrank_lieE : Module.finrank ℝ (lieE (Nset k r)) = 2 * (r * (k + 1) + r * (r - 1)) + r := by
  rw [← (LL k r).toLinearEquiv.finrank_eq, ← card_UT]
  simp [Module.finrank_prod, Module.finrank_pi_fintype]
  ring

instance haarP : (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

instance haarB : (volume : Measure (Fin r → Fin (k + 1) → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

instance haarPPar : (volume : Measure (PPar k r)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _

instance haarEE : (volume : Measure (EE k r)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _

theorem vol_LL {A : Set (EE k r)} :
    volume (LL k r '' A) = (2 ^ (r * (k + 1) + r * (r - 1)) : ℝ≥0∞) * volume A := by
  have hm : MeasurableEmbedding (LL k r) := (LL k r).toHomeomorph.measurableEmbedding
  have h := Measure.isAddLeftInvariant_eq_smul ((volume : Measure (EE k r)).map (LL k r)) volume
  set c := Measure.addHaarScalarFactor ((volume : Measure (EE k r)).map (LL k r)) volume
  have h1 := gauss_EE (k := k) (r := r)
  rw [← hm.integral_map (fun y => Real.exp (-1 * ‖y‖ ^ 2)), h, integral_smul_nnreal_measure,
    GaussianFourier.integral_rexp_neg_mul_sq_norm one_pos, finrank_lieE] at h1
  set N := r * (k + 1) + r * (r - 1)
  have h2 : (Real.pi / 1) ^ (((2 * N + r : ℕ) : ℝ) / 2) = Real.pi ^ N * √Real.pi ^ r := by
    rw [div_one, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le,
      ← Real.rpow_add Real.pi_pos]
    congr 1; push_cast; ring
  rw [h2, NNReal.smul_def, smul_eq_mul, div_pow] at h1
  have h3 : (2 : NNReal) ^ N * c = 1 := by
    have := Real.pi_pos
    apply NNReal.coe_injective
    push_cast
    field_simp at h1
    linarith
  have h4 : volume A = c * volume (LL k r '' A) := by
    have := congrArg (fun μ : Measure _ => μ (LL k r '' A)) h
    simpa [hm.map_apply, Set.preimage_image_eq _ (LL k r).injective] using this
  rw [h4, ← mul_assoc]
  have h5 : (2 : ℝ≥0∞) ^ N * c = 1 := by exact_mod_cast h3
  rw [h5, one_mul]

theorem closed_N : IsClosed (Nset k r) := by
  have he : ∀ i j c, IsClosed {g : Mat k r | g i j = c} := fun i j c =>
    isClosed_eq (continuous_id.matrix_elem i j) continuous_const
  refine IsClosed.and (isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const) (IsClosed.and ?_ ?_)
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => he _ _ _
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => he _ _ _

theorem matGroup_N : PI.IsMatGroup (Nset k r) :=
  ⟨closed_N, (nSubgroup k r).1, (nSubgroup k r).2.1, fun a ha => ⟨(nSubgroup k r).2.2 a ha,
    Matrix.mul_nonsing_inv _ ((uHGroup _ _ (Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1)).2.2 a ha.1).1⟩⟩

open scoped Matrix.Norms.Operator in
theorem cont_exp {m : ℕ} : Continuous (NormedSpace.exp : Matrix (Fin m) (Fin m) ℂ → _) :=
  NormedSpace.exp_continuous

theorem dens_one : HasDens (Nset k r) (haarLie (Nset k r) 1) 1 := by
  let f : lieE (Nset k r) → Mt k r := fun x i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j
  have hu : Continuous fun x : lieE (Nset k r) => unrealify (m := 2 * r + k + 1) x.1 := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [unrealify, Complex.mk_eq_add_mul_I]
    fun_prop
  have hf : Continuous f := cont_exp.comp hu
  have hi : Function.Injective f := fun x y h => by
    have := exp_inj_upper (TN_upper (mem_lieE x.2)) (TN_upper (mem_lieE y.2)) h
    apply Subtype.ext
    rw [← rl_unrealify x.1, this, rl_unrealify]
  have hm : MeasurableEmbedding f := hf.measurableEmbedding hi
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  have : haarLie (Nset k r) 1 (expSet (Nset k r) (Metric.ball 0 ρ)) = volume (Metric.ball (0 : lieE (Nset k r)) ρ) := by
    rw [haarLie, one_smul]
    exact (hm.map_apply _ _).trans (congrArg _ (Set.preimage_image_eq _ hi))
  rw [this, ENNReal.div_self (Metric.measure_ball_pos _ _ hρ).ne' measure_ball_lt_top.ne]

theorem haarLie_eq_lebN : ∀ k r : ℕ,
    haarLie (Nset k r) 1 = (2 ^ (r * (k + 1) + r * (r - 1)) : ℝ≥0∞) • lebN k r := by
  intro k r
  have hH := GlobalTheory.T.haarLie_isHaarOn_unipotentRadical k r 1 one_pos ENNReal.one_lt_top
  obtain ⟨c, -, -, hc⟩ := GlobalTheory.T.closedSubgroupBesselUnitary_haar_unique k r (Nset k r) _ _
    ⟨fun _ h => h.1, closed_N, (nSubgroup k r).1, (nSubgroup k r).2.1, (nSubgroup k r).2.2⟩ (GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn k r) hH
  have hT := GlobalTheory.T.tendsto_measure_image_ball_div_volume _ (Nset k r) _ 1 matGroup_N hH dens_one (EE k r) Phi (LL k r) Phi_zero
    (Eventually.of_forall Phi_mem) fun i j => ⟨_, (smooth_Phi i j).contDiffAt.hasStrictFDerivAt (by simp),
      fun v => by rw [LL_val, unrealify_rl]; rfl⟩
  have hi : Function.Injective fun q : EE k r => (Matrix.of.symm (Phi q) : Mt k r) := fun q q' h =>
    (coord_homeo k r).1.injOn trivial trivial h
  haveI : PolishSpace (EE k r) := by
    haveI : SecondCountableTopology (EE k r) := inferInstance
    haveI : TopologicalSpace.IsCompletelyMetrizableSpace (EE k r) := MetricSpace.toIsCompletelyMetrizableSpace
    exact {}
  have hm : MeasurableEmbedding fun q : EE k r => (Matrix.of.symm (Phi q) : Mt k r) :=
    Continuous.measurableEmbedding (f := fun q : EE k r => (Matrix.of.symm (Phi q) : Mt k r))
      (continuous_pi fun i => continuous_pi fun j => (smooth_Phi i j).continuous) hi
  set N : ℝ≥0∞ := 2 ^ (r * (k + 1) + r * (r - 1)) with hN
  have hN0 : N ≠ 0 := by simp [hN]
  have hN1 : N ≠ ⊤ := by simp [hN]
  have h1 : c / N = 1 := by
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hT
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    have : lebN k r ((fun q : EE k r => Matrix.of.symm (Phi q)) '' Metric.ball 0 ρ) =
        volume (Metric.ball (0 : EE k r) ρ) :=
      (hm.map_apply _ _).trans (congrArg _ (Set.preimage_image_eq _ hi))
    rw [vol_LL, hc, Measure.smul_apply, this, smul_eq_mul,
      ENNReal.mul_div_mul_right _ _ (Metric.measure_ball_pos _ _ hρ).ne' measure_ball_lt_top.ne]
  rw [hc, (ENNReal.div_eq_one_iff hN0 hN1).1 h1]

end GlobalTheory.Amp.NLie

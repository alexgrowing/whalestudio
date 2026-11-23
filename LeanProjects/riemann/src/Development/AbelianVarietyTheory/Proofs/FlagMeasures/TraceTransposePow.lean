import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarOfMultOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothAddSmul
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec.FormF

private lemma matrix_of_pow_apply_eq_epow {n : ℕ} {A : Type} [Ring A] (E : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) :
    (Matrix.of E ^ k) a b = Formalism.REAL.epow E k a b := by
  induction k generalizing b with
  | zero => simp [Formalism.REAL.epow, Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp only [ih, Matrix.of_apply, Formalism.REAL.epow]

private lemma matrix_of_pow_succ_apply_sub_nsmul_add_trace {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : Formalism.REAL.GlRel E) (j : ℕ) (a b : Fin n) :
    ∑ c, E c a * (Matrix.of E ^ j) b c =
      (Matrix.of E ^ (j + 1)) b a - n • (Matrix.of E ^ j) b a +
        if a = b then ∑ c, (Matrix.of E ^ j) c c else 0 := by
  simp only [matrix_of_pow_apply_eq_epow]
  have h1 : ∀ c, E c a * Formalism.REAL.epow E j b c = Formalism.REAL.epow E j b c * E c a +
      ((if a = b then Formalism.REAL.epow E j c c else 0) - Formalism.REAL.epow E j b a) := by
    intro c
    have := Formalism.REAL.epowCov (Module.End ℂ V) n E hE j b c c a
    rw [if_pos rfl] at this
    rw [← this]
    abel
  rw [Finset.sum_congr rfl fun c _ => h1 c]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [show Formalism.REAL.epow E (j + 1) b a = ∑ c, Formalism.REAL.epow E j b c * E c a from rfl]
  by_cases hab : a = b
  · simp only [hab, if_true]
    abel
  · simp only [hab, if_false, Finset.sum_const_zero]
    abel

private lemma ite_eq_trace_matrix_of_pow_apply {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : Formalism.REAL.GlRel E) (j : ℕ) (a b : Fin n) (w : V) :
    ∑ c, E c a ((Matrix.of E ^ j) b c w) = (Matrix.of E ^ (j + 1)) b a w - n • (Matrix.of E ^ j) b a w +
      if a = b then (∑ c, (Matrix.of E ^ j) c c) w else 0 := by
  have := congrArg (fun T : Module.End ℂ V => T w) (matrix_of_pow_succ_apply_sub_nsmul_add_trace E hE j a b)
  simp only [LinearMap.sum_apply, Module.End.mul_apply] at this
  rw [this]
  split_ifs <;> simp

private lemma sum_range_shift_smul_eq_sub_add {Y : Type} [AddCommGroup Y] [Module ℂ Y] (α : ℕ → ℂ) (m : ℕ) (N φ : ℂ)
    (y : ℕ → Y) :
    ∑ j ∈ Finset.range (m + 2), ((if 1 ≤ j then α (j - 1) else 0) - N * (if j ≤ m then α j else 0) +
        (if j = 0 then φ else 0)) • y j =
      ∑ j ∈ Finset.range (m + 1), α j • y (j + 1) - N • ∑ j ∈ Finset.range (m + 1), α j • y j + φ • y 0 := by
  simp only [add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum]
  have h1 : ∑ j ∈ Finset.range (m + 2), (if 1 ≤ j then α (j - 1) else 0) • y j =
      ∑ j ∈ Finset.range (m + 1), α j • y (j + 1) := by
    rw [Finset.sum_range_succ']
    simp
  have h2 : ∑ j ∈ Finset.range (m + 2), (if j ≤ m then α j else 0) • y j =
      ∑ j ∈ Finset.range (m + 1), α j • y j := by
    rw [Finset.sum_range_succ]
    simp only [show ¬ (m + 1 ≤ m) from by omega, if_false, zero_smul, add_zero]
    exact Finset.sum_congr rfl fun j hj => by
      rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
  have h3 : ∑ j ∈ Finset.range (m + 2), (if j = 0 then φ else 0) • y j = φ • y 0 := by
    rw [Finset.sum_range_succ']
    simp
  rw [h1, h2, h3]

private lemma sum_mulVec_one_eq_sum_entries {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, (P *ᵥ fun _ => (1 : ℂ)) i = ∑ a, ∑ b, P a b := by
  simp [Matrix.mulVec, dotProduct]

open Polynomial in

theorem trace_transpose_pow {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (χ : Fin n → ℂ) (v : V)
    (hv : ∀ k : ℕ, (∑ c, (Matrix.of E ^ k) c c) v = gelfVal χ k • v) (m : ℕ) :
    (∑ c, (Matrix.of (fun a b => E b a) ^ m) c c) v = ((-1) ^ m * gelfVal (fun a => -χ a) m) • v := by
  set Am := Formalism.REAL.Amat (fun c => χ c + ((n : ℂ) - 1) / 2) with hAm
  set M : Matrix (Fin n) (Fin n) ℂ := Am - (n : ℂ) • 1 + Matrix.of (fun _ _ => (1 : ℂ)) with hM
  have hgv : ∀ k, gelfVal χ k = ∑ a, ∑ b, (Am ^ k) a b := fun k => rfl
  have hsumvec : ∀ (m : ℕ) (α : ℕ → ℂ), ∑ i, ((∑ j ∈ Finset.range (m + 1), α j • Am ^ j) *ᵥ fun _ => (1 : ℂ)) i =
      ∑ j ∈ Finset.range (m + 1), α j * gelfVal χ j := by
    intro m α
    rw [sum_mulVec_one_eq_sum_entries]
    have hab : ∀ a b, (∑ j ∈ Finset.range (m + 1), α j • Am ^ j) a b =
        ∑ j ∈ Finset.range (m + 1), α j * (Am ^ j) a b := by
      intro a b
      simp [Matrix.sum_apply]
    simp only [hab, hgv, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  have key : ∀ m : ℕ, ∃ α : ℕ → ℂ,
      (∀ a b, (Matrix.of (fun a b => E b a) ^ m) a b v =
        ∑ j ∈ Finset.range (m + 1), α j • (Matrix.of E ^ j) b a v) ∧
      (∑ j ∈ Finset.range (m + 1), α j • Am ^ j) *ᵥ (fun _ => (1 : ℂ)) = M ^ m *ᵥ (fun _ => 1) := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun _ => 1, fun a b => ?_, ?_⟩
      · by_cases hab : a = b
        · subst hab
          simp
        · simp [Matrix.one_apply, hab, Ne.symm hab]
      · simp
    | succ m ih =>
      obtain ⟨α, h1, h2⟩ := ih
      set φ : ℂ := ∑ j ∈ Finset.range (m + 1), α j * gelfVal χ j with hφ
      refine ⟨fun j => (if 1 ≤ j then α (j - 1) else 0) - (n : ℂ) * (if j ≤ m then α j else 0) +
        (if j = 0 then φ else 0), fun a b => ?_, ?_⟩
      · rw [sum_range_shift_smul_eq_sub_add α m (n : ℂ) φ (fun j => (Matrix.of E ^ j) b a v)]
        rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply]
        simp only [Module.End.mul_apply, Matrix.of_apply, h1, map_sum, map_smul]
        rw [Finset.sum_comm]
        simp only [← Finset.smul_sum]
        simp only [ite_eq_trace_matrix_of_pow_apply E hE, hv]
        simp only [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        congr 1
        · congr 1
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_comm, Nat.cast_smul_eq_nsmul]
        · by_cases hab : a = b
          · subst hab
            simp [hφ, Finset.sum_smul, smul_smul]
          · simp [hab, Ne.symm hab, Matrix.one_apply_ne (Ne.symm hab)]
      · rw [sum_range_shift_smul_eq_sub_add α m (n : ℂ) φ (fun j => Am ^ j), pow_succ', ← Matrix.mulVec_mulVec, ← h2,
          Matrix.mulVec_mulVec]
        have hP : ∑ j ∈ Finset.range (m + 1), α j • Am ^ (j + 1) = Am * ∑ j ∈ Finset.range (m + 1), α j • Am ^ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [Matrix.mul_smul, pow_succ']
        rw [hP, pow_zero, hM, Matrix.add_mul, Matrix.sub_mul, Matrix.add_mulVec, Matrix.sub_mulVec,
          Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mul, Matrix.one_mul]
        congr 1
        rw [← Matrix.mulVec_mulVec]
        ext i
        have := hsumvec m α
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, one_mul, Matrix.smul_apply, Matrix.one_apply,
          smul_eq_mul, mul_one] at this ⊢
        rw [this, hφ]
        simp
  obtain ⟨α, h1, h2⟩ := key m
  have hM' : M = (-Formalism.REAL.Amat (fun c => -χ c + ((n : ℂ) - 1) / 2))ᵀ := by
    ext a b
    simp only [hM, hAm, Formalism.REAL.Amat, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.of_apply, Matrix.transpose_apply, Matrix.neg_apply, smul_eq_mul]
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h, h.ne, h.ne', not_lt.2 h.le]
    · simp
      ring
    · simp [h, h.ne, h.ne', not_lt.2 h.le]
  have hval : ∑ j ∈ Finset.range (m + 1), α j * gelfVal χ j = (-1) ^ m * gelfVal (fun a => -χ a) m := by
    rw [← hsumvec m α, h2, sum_mulVec_one_eq_sum_entries, hM', ← Matrix.transpose_pow]
    have hneg : (-Formalism.REAL.Amat (fun c => -χ c + ((n : ℂ) - 1) / 2)) ^ m =
        ((-1 : ℂ) ^ m) • Formalism.REAL.Amat (fun c => -χ c + ((n : ℂ) - 1) / 2) ^ m := by
      rw [← _root_.smul_pow, neg_one_smul]
    rw [hneg]
    simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, gelfVal, Finset.mul_sum]
    exact Finset.sum_comm
  rw [LinearMap.sum_apply]
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum, ← LinearMap.sum_apply, hv, smul_smul, ← Finset.sum_smul]
  rw [hval]

variable {n : ℕ}

open GlobalTheory.CapelliCentral in

lemma word_apply {ε : Fin n → Bool} (w : List (Fin n × Fin n)) (F : smoothSpace ε ℂ) {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g, inUJ ε g → F.1 g = f g) :
    ∀ g, inUJ ε g → ((w.map fun p => eabEnd ε ℂ p.1 p.2).prod F).1 g = Eword ε w f g := by
  induction w with
  | nil =>
    intro g hg
    simpa [Formalism.REAL.Eword] using h g hg
  | cons p w ih =>
    intro g hg
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, Formalism.REAL.Eword]
    rw [eabEnd_apply p.1 p.2 _ ih hg, Formalism.REAL.eabV_eq]

private lemma matrix_of_pow_succ_apply_eq_sum_prod {A : Type} [Ring A] (E : Fin n → Fin n → A) (k : ℕ) :
    ∀ i j : Fin n, (Matrix.of E ^ (k + 1)) i j = ∑ a : Fin (k + 1) → Fin n, if a 0 = i then
      (List.ofFn fun t : Fin (k + 1) =>
        E ((Fin.snoc a j : Fin (k + 2) → Fin n) t.castSucc) ((Fin.snoc a j : Fin (k + 2) → Fin n) t.succ)).prod
      else 0 := by
  induction k with
  | zero =>
    intro i j
    rw [pow_succ, pow_zero, Matrix.one_mul, Matrix.of_apply]
    rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)) _ (fun c => if c = i then E c j else 0)
      (fun a => by simp [Fin.snoc, Equiv.funUnique, Fin.default_eq_zero])]
    simp
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih, Finset.sum_mul, ite_mul, zero_mul]
    rw [← (Fin.snocEquiv (fun _ => Fin n)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
    have h0 : (Fin.snoc a c : Fin (k + 2) → Fin n) 0 = a 0 := by
      simpa only [Fin.castSucc_zero] using Fin.snoc_castSucc (α := fun _ => Fin n) c a 0
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, h0]
    split_ifs with hi
    · conv_rhs => rw [List.ofFn_succ', List.prod_concat]
      simp only [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_last, Fin.succ_last, Matrix.of_apply]
    · rfl

lemma sum_cycWord {A : Type} [Ring A] (E : Fin n → Fin n → A) (m : ℕ) :
    ∑ a : Fin (m + 1) → Fin n, ((cycWord a).map fun p => E p.1 p.2).prod = ∑ c, (Matrix.of E ^ (m + 1)) c c := by
  simp_rw [matrix_of_pow_succ_apply_eq_sum_prod E m]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true, cycWord, List.map_ofFn]
  congr 1
  refine List.ofFn_inj.mpr ?_
  funext t
  simp only [Function.comp_apply]
  by_cases ht : t = Fin.last m
  · subst ht
    simp [Fin.snoc_last]
  · have hs : t.succ = (finRotate (m + 1) t).castSucc := by
      ext
      simp [Fin.val_add_one_of_lt (Fin.lt_last_iff_ne_last.2 ht)]
    rw [hs, Fin.snoc_castSucc, Fin.snoc_castSucc]

open GlobalTheory.CapelliCentral in

lemma gelf_apply {ε : Fin n → Bool} (m : ℕ) (F : smoothSpace ε ℂ) {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g, inUJ ε g → F.1 g = f g) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ((∑ c, (Matrix.of (eabEnd ε ℂ) ^ (m + 1)) c c) F).1 g = gelf ε m f g := by
  rw [← sum_cycWord, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  unfold gelf
  exact Finset.sum_congr rfl fun a _ => word_apply (cycWord a) F h g hg

open GlobalTheory.CapelliCentral in
lemma gelf_mk {ε : Fin n → Bool} {χ : Fin n → ℂ} {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : IsZEigen ε χ f) (k : ℕ) :
    (∑ c, (Matrix.of (eabEnd ε ℂ) ^ k) c c) (mk f h.1) = gelfVal χ k • mk f h.1 := by
  cases k with
  | zero =>
    apply ext_on
    intro g hg
    simp [gelfVal, Matrix.one_apply, mk_apply f h.1 hg]
  | succ m =>
    apply ext_on
    intro g hg
    rw [gelf_apply m _ (fun g' hg' => mk_apply f h.1 hg') hg, h.2 m g hg]
    simp [mk_apply f h.1 hg]

lemma Rd_neg (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Rd (-X) f g = -Rd X f g := by
  unfold Formalism.REAL.Rd
  have h : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • -X))) =
      fun t : ℝ => (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (-t) := by
    funext t
    simp only [Complex.ofReal_neg, neg_smul, smul_neg]
  rw [h]
  exact (deriv_comp_neg (f := fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (x := (0 : ℝ))).trans
    (by rw [neg_zero])

lemma Rd_conj (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (c : ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Rd X (fun x => c * f (x.map star)) g = c * Rd (X.map star) f (g.map star) := by
  unfold Formalism.REAL.Rd
  have h : (fun t : ℝ => c * f ((g * NormedSpace.exp ((t : ℂ) • X)).map star)) =
      fun t : ℝ => c * f (g.map star * NormedSpace.exp ((t : ℂ) • X.map star)) := by
    funext t
    rw [map_star_mul, exp_star]
    congr 4
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, Complex.conj_ofReal]
  simp only [h]
  exact deriv_const_mul_field c

lemma Jm_single (ε : Fin n → Bool) (a b : Fin n) :
    Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Jm ε = ((Formalism.REAL.sgn ε a b : ℝ) : ℂ) • Matrix.single b a (1 : ℂ) := by
  ext i j
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    Matrix.smul_apply, Matrix.single_apply, Formalism.REAL.sgn, smul_eq_mul]
  by_cases h : b = i ∧ a = j
  · obtain ⟨rfl, rfl⟩ := h
    by_cases ha : ε a <;> by_cases hb : ε b <;> simp [ha, hb]
  · have h' : ¬ (a = j ∧ b = i) := fun h'' => h ⟨h''.2, h''.1⟩
    simp [h, h']

private lemma rd_smul_sign_eq_mul (Y : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) (hr : r = 1 ∨ r = -1) :
    Rd ((r : ℂ) • Y) f g = r * Rd Y f g := by
  rcases hr with rfl | rfl
  · simp
  · simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul, Rd_neg]
    ring

private lemma map_star_cpart_single_eq_neg_sgn_smul_swap (ε : Fin n → Bool) (a b : Fin n) :
    (Formalism.REAL.cpart1 ε (Matrix.single a b 1)).map star =
              ((-Formalism.REAL.sgn ε a b : ℝ) : ℂ) • Formalism.REAL.cpart1 ε (Matrix.single b a 1) ∧
      (Formalism.REAL.cpart2 ε (Matrix.single a b 1)).map star =
        ((-Formalism.REAL.sgn ε a b : ℝ) : ℂ) • Formalism.REAL.cpart2 ε (Matrix.single b a 1) := by
  simp only [Formalism.REAL.cpart1, Formalism.REAL.cpart2, Jm_single]
  have hs : Formalism.REAL.sgn ε b a = Formalism.REAL.sgn ε a b := by
    simp only [Formalism.REAL.sgn, eq_comm]
  rw [hs]
  by_cases hab : ε a = ε b
  · have h1 : Formalism.REAL.sgn ε a b = 1 := by simp [Formalism.REAL.sgn, hab]
    rw [h1]
    constructor <;> ext i j <;>
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply,
        smul_eq_mul] <;> split_ifs <;> simp
  · have h1 : Formalism.REAL.sgn ε a b = -1 := by simp [Formalism.REAL.sgn, hab]
    rw [h1]
    constructor <;> ext i j <;>
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply,
        smul_eq_mul] <;> split_ifs <;> simp

lemma Eab_conj (ε : Fin n → Bool) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (c : ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Eab ε a b (fun x => c * f (x.map star)) g =
      -((Formalism.REAL.sgn ε a b : ℝ) : ℂ) * c * Eab ε b a f (g.map star) := by
  obtain ⟨h1, h2⟩ := map_star_cpart_single_eq_neg_sgn_smul_swap ε a b
  have hr : (-Formalism.REAL.sgn ε a b) = 1 ∨ (-Formalism.REAL.sgn ε a b) = -1 := by
    unfold Formalism.REAL.sgn
    split_ifs <;> norm_num
  simp only [Formalism.REAL.Eab, Formalism.REAL.Ec, Rd_conj, h1, h2, rd_smul_sign_eq_mul _ _ _ _ hr]
  push_cast
  ring

lemma sgn_cycWord (ε : Fin n → Bool) {m : ℕ} (a : Fin (m + 1) → Fin n) :
    ((cycWord a).map fun p => -((Formalism.REAL.sgn ε p.1 p.2 : ℝ) : ℂ)).prod = (-1) ^ (m + 1) := by
  set e : Fin n → ℂ := fun x => if ε x then 1 else -1 with he
  have hs : ∀ x y, -((Formalism.REAL.sgn ε x y : ℝ) : ℂ) = -1 * (e x * e y) := by
    intro x y
    simp only [he, Formalism.REAL.sgn]
    by_cases hx : ε x <;> by_cases hy : ε y <;> simp [hx, hy]
  have hr : ∏ i, e (a (finRotate (m + 1) i)) = ∏ i, e (a i) :=
    Fintype.prod_equiv (finRotate (m + 1)) _ _ (fun _ => rfl)
  have h1 : (∏ i, e (a i)) * ∏ i, e (a i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    simp only [he]
    split_ifs <;> norm_num
  simp only [cycWord, List.map_ofFn, List.prod_ofFn, Function.comp_def, hs]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_mul_distrib, hr, h1, mul_one]

lemma Jm_perm (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) : Jm (ε ∘ s) = (Jm ε).submatrix s s := by
  unfold Formalism.REAL.Jm
  rw [Matrix.submatrix_diagonal_equiv]
  rfl

lemma UJ_perm {ε : Fin n → Bool} (s : Equiv.Perm (Fin n)) {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ UJset ε) :
    g.submatrix s s ∈ UJset (ε ∘ s) := by
  have h' : Formalism.REAL.inUJ ε g := h
  show Formalism.REAL.inUJ (ε ∘ s) (g.submatrix s s)
  unfold Formalism.REAL.inUJ at h' ⊢
  rw [Jm_perm, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h']

lemma K_perm {ε : Fin n → Bool} (s : Equiv.Perm (Fin n)) {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ Kset ε) :
    g.submatrix s s ∈ Kset (ε ∘ s) := by
  obtain ⟨hu, hc⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff] at hu ⊢
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      ← Matrix.star_eq_conjTranspose, hu, Matrix.submatrix_one_equiv]
  · rw [Jm_perm, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hc]

lemma exp_perm (s : Equiv.Perm (Fin n)) (X : Matrix (Fin n) (Fin n) ℂ) :
    (NormedSpace.exp X).submatrix s s = NormedSpace.exp (X.submatrix s s) := by
  have hconj : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Y.submatrix s s =
      (1 : Matrix (Fin n) (Fin n) ℂ).submatrix s id * Y * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id s := by
    intro Y
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply]
  have hPQ : (1 : Matrix (Fin n) (Fin n) ℂ).submatrix s id * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id s = 1 := by
    have := hconj 1
    rw [Matrix.mul_one] at this
    rw [← this, Matrix.submatrix_one_equiv]
  have hQP : (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id s * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix s id = 1 :=
    mul_eq_one_comm.mp hPQ
  have hinv : ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix s id)⁻¹ = (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id s :=
    Matrix.inv_eq_right_inv hPQ
  have hU : IsUnit ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix s id) := ⟨⟨_, _, hPQ, hQP⟩, rfl⟩
  rw [hconj, hconj, ← hinv, Matrix.exp_conj _ _ hU]

private lemma rd_submatrix_perm (s : Equiv.Perm (Fin n)) (X : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Rd X (fun x => f (x.submatrix s s)) g = Rd (X.submatrix s s) f (g.submatrix s s) := by
  unfold Formalism.REAL.Rd
  congr 1
  funext t
  beta_reduce
  rw [← Matrix.submatrix_mul_equiv (e₂ := s), exp_perm]
  rfl

private lemma cpart1_submatrix_perm (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (Formalism.REAL.cpart1 ε Z).submatrix s s = Formalism.REAL.cpart1 (ε ∘ s) (Z.submatrix s s) := by
  have hsub : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (A - B).submatrix s s = A.submatrix s s - B.submatrix s s :=
    fun _ _ => rfl
  have hsm : ∀ (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ), (c • A).submatrix s s = c • A.submatrix s s :=
    fun _ _ => rfl
  simp only [Formalism.REAL.cpart1, hsm, hsub, Jm_perm,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

private lemma cpart2_submatrix_perm (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (Formalism.REAL.cpart2 ε Z).submatrix s s = Formalism.REAL.cpart2 (ε ∘ s) (Z.submatrix s s) := by
  have hadd : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (A + B).submatrix s s = A.submatrix s s + B.submatrix s s :=
    fun _ _ => rfl
  have hsm : ∀ (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ), (c • A).submatrix s s = c • A.submatrix s s :=
    fun _ _ => rfl
  simp only [Formalism.REAL.cpart2, hsm, hadd, Jm_perm,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

lemma Eab_perm (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Eab ε (s a) (s b) (fun x => f (x.submatrix s s)) g = Eab (ε ∘ s) a b f (g.submatrix s s) := by
  have hsg : (Matrix.single (s a) (s b) (1 : ℂ)).submatrix s s = Matrix.single a b 1 := by
    ext i j
    simp [Matrix.single_apply, s.injective.eq_iff]
  simp only [Formalism.REAL.Eab, Formalism.REAL.Ec, rd_submatrix_perm, cpart1_submatrix_perm, cpart2_submatrix_perm, hsg]

lemma Eword_perm (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : List (Fin n × Fin n)) :
    Eword ε (w.map fun p => (s p.1, s p.2)) (fun x => f (x.submatrix s s)) =
      fun g => Eword (ε ∘ s) w f (g.submatrix s s) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    funext g
    simp only [List.map_cons, Formalism.REAL.Eword]
    rw [ih]
    exact Eab_perm ε s p.1 p.2 _ g

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
lemma isZEigen_perm {ε : Fin n → Bool} (s : Equiv.Perm (Fin n)) {χ : Fin n → ℂ} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : IsZEigen (ε ∘ s) χ f) : IsZEigen ε χ (fun x => f (x.submatrix s s)) := by
  obtain ⟨hsm, hev⟩ := h
  have hc : ∀ {k : WithTop ℕ∞}, ContDiff ℝ k (fun x : Matrix (Fin n) (Fin n) ℂ => x.submatrix s s) :=
    contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_apply_apply ℝ ℂ (s i) (s j)
  refine ⟨?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hsm (g₀.submatrix s s) (UJ_perm s hg₀)
    exact ⟨(fun x : Matrix (Fin n) (Fin n) ℂ => x.submatrix s s) ⁻¹' U, fun x => F (x.submatrix s s),
      hU.preimage (hc (k := 0)).continuous, hgU, hF.comp hc.contDiffOn (fun x hx => hx),
      fun g hg hgu => hfF _ hg (UJ_perm s hgu)⟩
  · intro m g hg
    have hg' : g.submatrix s s ∈ UJset (ε ∘ s) := UJ_perm s hg
    have key : gelf ε m (fun x => f (x.submatrix s s)) g = gelf (ε ∘ s) m f (g.submatrix s s) := by
      unfold gelf
      symm
      refine Fintype.sum_equiv (Equiv.piCongrRight fun _ => s) _ _ (fun a => ?_)
      have hw : cycWord ((Equiv.piCongrRight fun _ => s) a) = (cycWord a).map fun p => (s p.1, s p.2) := by
        simp [cycWord, List.map_ofFn, Function.comp_def]
      rw [hw, Eword_perm]
    rw [key, hev m _ hg']

theorem trWord : ∀ (n : ℕ) (ε : Fin n → Bool) (χ : Fin n → ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ), SmoothOnG ε f → IsZEigen ε χ f → ∀ m : ℕ, ∀ g ∈ UJset ε, ∑ a : Fin (m + 1) → Fin n, Eword ε ((cycWord a).map Prod.swap) f g = (-1) ^ (m + 1) * gelfVal (fun a => -χ a) (m + 1) * f g := by
  intro n ε χ f hf hz m g hg
  have hT := trace_transpose_pow (GlobalTheory.CapelliCentral.eabEnd ε ℂ) GlobalTheory.CapelliCentral.eabEnd_glRel χ (GlobalTheory.CapelliCentral.mk f hz.1) (fun k => gelf_mk hz k) (m + 1)
  have h2 := congrArg (fun F : GlobalTheory.CapelliCentral.smoothSpace ε ℂ => F.1 g) hT
  rw [← sum_cycWord (fun a b => GlobalTheory.CapelliCentral.eabEnd ε ℂ b a), LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply] at h2
  rw [Submodule.coe_smul, Pi.smul_apply, GlobalTheory.CapelliCentral.mk_apply f hz.1 hg, smul_eq_mul] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hw : ((cycWord a).map fun p => GlobalTheory.CapelliCentral.eabEnd ε ℂ p.2 p.1) =
      (((cycWord a).map Prod.swap).map fun p => GlobalTheory.CapelliCentral.eabEnd ε ℂ p.1 p.2) := by
    simp [List.map_map, Function.comp_def]
  rw [hw, word_apply ((cycWord a).map Prod.swap) (GlobalTheory.CapelliCentral.mk f hz.1) (fun g' hg' => GlobalTheory.CapelliCentral.mk_apply f hz.1 hg') g hg]

private lemma eword_map_star_eq_prod_neg_sgn_mul_swap (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : List (Fin n × Fin n)) :
    Formalism.REAL.Eword ε w (fun x => f (x.map star)) = fun g =>
      (w.map fun p => -((Formalism.REAL.sgn ε p.1 p.2 : ℝ) : ℂ)).prod *
        Formalism.REAL.Eword ε (w.map Prod.swap) f (g.map star) := by
  induction w with
  | nil =>
    funext g
    simp [Formalism.REAL.Eword]
  | cons p w ih =>
    funext g
    simp only [List.map_cons, List.prod_cons, Formalism.REAL.Eword]
    rw [ih, Eab_conj]
    simp only [Prod.fst_swap, Prod.snd_swap]

theorem wordConj : ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : List (Fin n × Fin n)) (g : Matrix (Fin n) (Fin n) ℂ), Eword ε w (fun x => f (x.map star)) g = (w.map fun p => -((Formalism.REAL.sgn ε p.1 p.2 : ℝ) : ℂ)).prod * Eword ε (w.map Prod.swap) f (g.map star) := by
  intro n ε f w g
  exact congrFun (eword_map_star_eq_prod_neg_sgn_mul_swap ε f w) g

theorem eigConj : ∀ (n : ℕ) (ε : Fin n → Bool) (χ : Fin n → ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ), SmoothOnG ε f → IsZEigen ε χ f → SmoothOnG ε (fun x => f (x.map star)) ∧ IsZEigen ε (fun a => -χ a) (fun x => f (x.map star)) := by
  intro n ε χ f hf hz
  have hsm : SmoothOnG ε (fun x => f (x.map star)) := by
    letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
    letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
    intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (g₀.map star) (UJ_star hg₀)
    have hc : ∀ {k : WithTop ℕ∞}, ContDiff ℝ k (fun x : Matrix (Fin n) (Fin n) ℂ => x.map star) :=
      contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
        (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (contDiff_apply_apply ℝ ℂ i j)
    refine ⟨(fun x : Matrix (Fin n) (Fin n) ℂ => x.map star) ⁻¹' U, fun x => F (x.map star),
      hU.preimage (hc (k := 0)).continuous, by simpa using hgU, hF.comp hc.contDiffOn (fun x hx => hx), ?_⟩
    intro g hg hgu
    exact hfF _ hg (UJ_star hgu)
  refine ⟨hsm, hsm, ?_⟩
  intro m g hg
  have hg' : g.map star ∈ UJset ε := UJ_star hg
  unfold gelf
  simp only [wordConj, sgn_cycWord]
  rw [← Finset.mul_sum, trWord n ε χ f hf hz m _ hg']
  have h1 : ((-1 : ℂ) ^ (m + 1)) * (-1) ^ (m + 1) = 1 := by
    rw [← mul_pow]
    simp
  linear_combination (gelfVal (fun a => -χ a) (m + 1) * f (g.map star)) * h1

end GlobalTheory.Dec.FormF

import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExponentWordRecursion

open Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.ListSumSplittings

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def splits {α : Type*} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: w => (splits w).flatMap fun p => [(x :: p.1, p.2), (p.1, x :: p.2)]

lemma splits_mem {α : Type*} : ∀ (w : List α), ∀ p ∈ splits w, p.1.Sublist w ∧ p.2.Sublist w := by
  intro w
  induction w with
  | nil => intro p hp; simp only [splits, List.mem_singleton] at hp; subst hp; simp
  | cons x w ih =>
    intro p hp
    rw [splits, List.mem_flatMap] at hp
    obtain ⟨q, hq, hp⟩ := hp
    rcases List.mem_cons.1 hp with h | h
    · subst h; exact ⟨(ih q hq).1.cons_cons x, (ih q hq).2.cons x⟩
    · rw [List.mem_singleton.1 h]; exact ⟨(ih q hq).1.cons x, (ih q hq).2.cons_cons x⟩

lemma list_sum_mul_right {α : Type*} (L : List α) (f : α → ℝ) (c : ℝ) :
    (L.map fun a => f a * c).sum = (L.map f).sum * c := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.sum_cons, ih, add_mul]

lemma ckOn_const' {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {m : ℕ∞} (c : F) :
    CkOn m (GV k r) (fun _ : Mat k r => c) := by
  intro g₀ _
  exact ⟨Set.univ, fun _ => c, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

lemma ckOn_mulF {f : Mat k r → ℂ} {H : Mat k r → E} {m : ℕ∞} (hf : CkOn m (GV k r) f)
    (hH : CkOn m (GV k r) H) : CkOn m (GV k r) (fun g => f g • H g) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g₀ hg₀
  obtain ⟨U₂, H', hU₂, hgU₂, hc₂, hff₂⟩ := hH g₀ hg₀
  refine ⟨U ∩ U₂, fun g => f' g • H' g, hU.inter hU₂, ⟨hgU, hgU₂⟩,
    (hc.mono Set.inter_subset_left).smul (hc₂.mono Set.inter_subset_right), ?_⟩
  intro g hg hgG
  show f g • H g = f' g • H' g
  rw [hff g hg.1 hgG, hff₂ g hg.2 hgG]

lemma op_smulF {f : Mat k r → ℂ} {H : Mat k r → E} {X g : Mat k r} (b : Bool) (hX : inLie k r X)
    (hf : CkOn ((1 : ℕ) : ℕ∞) (GV k r) f) (hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H) (hg : g ∈ GV k r) :
    op b X (fun g => f g • H g) g = op b X f g • H g + f g • op b X H g := by
  have h1 := (ckOn_diff 0 b hf hX hg).hasDerivAt
  have h2 := (ckOn_diff 0 b hH hX hg).hasDerivAt
  have h3 := h1.smul h2
  simp only [cv_zero] at h3
  show deriv (fun t : ℝ => f (cv b X t g) • H (cv b X t g)) 0 = _
  rw [show (fun t : ℝ => f (cv b X t g) • H (cv b X t g)) =
    ((fun t => f (cv b X t g)) • fun t => H (cv b X t g)) from rfl, h3.deriv]
  exact add_comm _ _

lemma ckOn_listSumF {α : Type*} (φ : α → Mat k r → E) {m : ℕ∞} :
    ∀ (L : List α), (∀ a ∈ L, CkOn m (GV k r) (φ a)) →
      CkOn m (GV k r) (fun g => (L.map fun a => φ a g).sum) := by
  intro L
  induction L with
  | nil => intro _; simpa using (ckOn_const' (k := k) (r := r) (m := m) (0 : E))
  | cons a L ih =>
    intro hL
    have e : (fun g => ((a :: L).map fun a => φ a g).sum) = φ a + (fun g => (L.map fun a => φ a g).sum) := by
      funext g; simp
    rw [e]
    exact ckOn_add (hL a List.mem_cons_self) (ih fun b hb => hL b (List.mem_cons_of_mem _ hb))

lemma op_listSumF {α : Type*} {b : Bool} {X : Mat k r} (hX : inLie k r X) (φ : α → Mat k r → E) :
    ∀ (L : List α), (∀ a ∈ L, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (φ a)) →
      ∀ g ∈ GV k r, op b X (fun g' => (L.map fun a => φ a g').sum) g = (L.map fun a => op b X (φ a) g).sum := by
  intro L
  induction L with
  | nil => intro _ g _; simp [op]
  | cons a L ih =>
    intro hL g hg
    have hL' : ∀ c ∈ L, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (φ c) := fun c hc => hL c (List.mem_cons_of_mem _ hc)
    have e : (fun g' => ((a :: L).map fun a => φ a g').sum) = φ a + (fun g' => (L.map fun a => φ a g').sum) := by
      funext g'; simp
    rw [e, op_add b hX (hL a List.mem_cons_self) (ckOn_listSumF φ L hL') hg, ih hL' g hg]
    simp

theorem W_smulF : ∀ (w : List (Bool × Mat k r)), AllLie w → ∀ (f : Mat k r → ℂ) (H : Mat k r → E),
    CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f → CkOn ((w.length : ℕ) : ℕ∞) (GV k r) H → ∀ g ∈ GV k r,
      W w (fun g => f g • H g) g = ((splits w).map fun p => W p.1 f g • W p.2 H g).sum := by
  intro w
  induction w with
  | nil => intro _ f H _ _ g _; simp [splits, W_nil]
  | cons x w ih =>
    intro hw f H hf hH g hg
    have hw' : AllLie w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hx : inLie k r x.2 := hw x List.mem_cons_self
    have hf' : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f := ckOn_mono (by simp) hf
    have hH' : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) H := ckOn_mono (by simp) hH
    rw [W_cons, op_congr x.1 hx (ih hw' f H hf' hH') g hg]
    have hCf : ∀ l : List (Bool × Mat k r), l.Sublist w → CkOn ((1 : ℕ) : ℕ∞) (GV k r) (W l f) :=
      fun l hl => smooth_on_of_word_derivatives l (fun y hy => hw' y (hl.subset hy)) 1
        (ckOn_mono (by have := hl.length_le; simp; omega) hf)
    have hCH : ∀ l : List (Bool × Mat k r), l.Sublist w → CkOn ((1 : ℕ) : ℕ∞) (GV k r) (W l H) :=
      fun l hl => smooth_on_of_word_derivatives l (fun y hy => hw' y (hl.subset hy)) 1
        (ckOn_mono (by have := hl.length_le; simp; omega) hH)
    rw [op_listSumF hx (fun p g' => W p.1 f g' • W p.2 H g') (splits w)
      (fun p hp => ckOn_mulF (hCf p.1 (splits_mem w p hp).1) (hCH p.2 (splits_mem w p hp).2)) g hg]
    rw [splits, list_sum_flatMap]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    rw [op_smulF x.1 hx (hCf p.1 (splits_mem w p hp).1) (hCH p.2 (splits_mem w p hp).2) hg]
    simp [W_cons]

def PolyClass (D : ℕ) (P : Mat k r → ℂ) : Prop :=
  CkOn (⊤ : ℕ∞) (GV k r) P ∧ ∀ a : List (Bool × Mat k r), AllLie a →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ GV k r, ‖W a P g‖ ≤ C * gN g ^ D

lemma polyClass_mono {D D' : ℕ} {P : Mat k r → ℂ} (h : D ≤ D') (hP : PolyClass D P) : PolyClass D' P := by
  refine ⟨hP.1, fun a ha => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hP.2 a ha
  exact ⟨C, hC0, fun g hg => (hC g hg).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_gN hg) h) hC0)⟩

lemma polyClass_op {D : ℕ} {P : Mat k r → ℂ} (hP : PolyClass D P) (b : Bool) {X : Mat k r}
    (hX : inLie k r X) : PolyClass D (op b X P) := by
  refine ⟨ckOn_op_top b hP.1 hX, fun a ha => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hP.2 (a ++ [(b, X)]) (by
    intro y hy; rcases List.mem_append.1 hy with h | h
    · exact ha y h
    · rw [List.mem_singleton.1 h]; exact hX)
  exact ⟨C, hC0, fun g hg => by have := hC g hg; rwa [W_append] at this⟩

lemma W_const (c : ℂ) : ∀ a : List (Bool × Mat k r), ∃ c' : ℂ, ‖c'‖ ≤ ‖c‖ ∧ W a (fun _ => c) = fun _ => c' := by
  intro a
  induction a with
  | nil => exact ⟨c, le_rfl, rfl⟩
  | cons x a ih =>
    obtain ⟨c', -, he⟩ := ih
    refine ⟨0, by simp, ?_⟩
    rw [W_cons, he]
    funext g; simp [op]

lemma polyClass_const (c : ℂ) : PolyClass 0 (fun _ : Mat k r => c) := by
  refine ⟨ckOn_const' c, fun a _ => ?_⟩
  obtain ⟨c', hc', he⟩ := W_const c a
  exact ⟨‖c‖, norm_nonneg _, fun g _ => by rw [he]; simpa using hc'⟩

lemma polyClass_add {D : ℕ} {P Q : Mat k r → ℂ} (hP : PolyClass D P) (hQ : PolyClass D Q) :
    PolyClass D (fun g => P g + Q g) := by
  refine ⟨ckOn_add hP.1 hQ.1, fun a ha => ?_⟩
  obtain ⟨C1, h10, h1⟩ := hP.2 a ha
  obtain ⟨C2, h20, h2⟩ := hQ.2 a ha
  refine ⟨C1 + C2, add_nonneg h10 h20, fun g hg => ?_⟩
  have e := W_add a ha (ckOn_top_nat hP.1 _) (ckOn_top_nat hQ.1 _) g hg
  rw [show (fun g => P g + Q g) = P + Q from rfl, e]
  calc ‖W a P g + W a Q g‖ ≤ ‖W a P g‖ + ‖W a Q g‖ := norm_add_le _ _
    _ ≤ C1 * gN g ^ D + C2 * gN g ^ D := add_le_add (h1 g hg) (h2 g hg)
    _ = (C1 + C2) * gN g ^ D := by ring

lemma polyClass_mul {D1 D2 : ℕ} {P Q : Mat k r → ℂ} (hP : PolyClass D1 P) (hQ : PolyClass D2 Q) :
    PolyClass (D1 + D2) (fun g => P g * Q g) := by
  have hfun : (fun g => P g * Q g) = (fun g => P g • Q g) := by funext g; rw [smul_eq_mul]
  rw [hfun]
  refine ⟨ckOn_mulF hP.1 hQ.1, fun a ha => ?_⟩
  have hexP : ∀ l : List (Bool × Mat k r), ∃ C : ℝ, 0 ≤ C ∧
      (AllLie l → ∀ g ∈ GV k r, ‖W l P g‖ ≤ C * gN g ^ D1) := by
    intro l; by_cases hl : AllLie l
    · obtain ⟨C, h0, h⟩ := hP.2 l hl; exact ⟨C, h0, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => absurd h hl⟩
  have hexQ : ∀ l : List (Bool × Mat k r), ∃ C : ℝ, 0 ≤ C ∧
      (AllLie l → ∀ g ∈ GV k r, ‖W l Q g‖ ≤ C * gN g ^ D2) := by
    intro l; by_cases hl : AllLie l
    · obtain ⟨C, h0, h⟩ := hQ.2 l hl; exact ⟨C, h0, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => absurd h hl⟩
  choose CP hCP0 hCP using hexP
  choose CQ hCQ0 hCQ using hexQ
  refine ⟨((splits a).map fun p => CP p.1 * CQ p.2).sum,
    list_sum_nonneg _ _ fun p _ => mul_nonneg (hCP0 _) (hCQ0 _), fun g hg => ?_⟩
  rw [W_smulF a ha P Q (ckOn_top_nat hP.1 _) (ckOn_top_nat hQ.1 _) g hg]
  refine (norm_list_sum_le _ _).trans ?_
  rw [← list_sum_mul_right]
  refine list_sum_le _ _ _ fun p hp => ?_
  obtain ⟨h1, h2⟩ := splits_mem a p hp
  have hl1 : AllLie p.1 := fun y hy => ha y (h1.subset hy)
  have hl2 : AllLie p.2 := fun y hy => ha y (h2.subset hy)
  rw [norm_smul, pow_add]
  calc ‖W p.1 P g‖ * ‖W p.2 Q g‖ ≤ (CP p.1 * gN g ^ D1) * (CQ p.2 * gN g ^ D2) :=
        mul_le_mul (hCP p.1 hl1 g hg) (hCQ p.2 hl2 g hg) (norm_nonneg _)
          (mul_nonneg (hCP0 _) (pow_nonneg (gN_pos hg).le _))
    _ = CP p.1 * CQ p.2 * (gN g ^ D1 * gN g ^ D2) := by ring

lemma polyClass_cmul {D : ℕ} {P : Mat k r → ℂ} (c : ℂ) (hP : PolyClass D P) :
    PolyClass D (fun g => c * P g) := by
  have := polyClass_mul (polyClass_const c) hP
  rwa [zero_add] at this

lemma polyClass_pow {D : ℕ} {P : Mat k r → ℂ} (hP : PolyClass D P) :
    ∀ n : ℕ, PolyClass (n * D) (fun g => P g ^ n) := by
  intro n
  induction n with
  | zero => simpa using polyClass_const (k := k) (r := r) 1
  | succ n ih =>
    have := polyClass_mul ih hP
    have e : (fun g => P g ^ (n + 1)) = fun g => P g ^ n * P g := by funext g; rw [pow_succ]
    rw [e, Nat.succ_mul]
    exact this

lemma polyClass_prod {ι : Type*} (s : Finset ι) (D : ι → ℕ) (P : ι → Mat k r → ℂ)
    (h : ∀ i ∈ s, PolyClass (D i) (P i)) : PolyClass (∑ i ∈ s, D i) (fun g => ∏ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polyClass_const (k := k) (r := r) 1
  | insert a s ha ih =>
    have := polyClass_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    have e : (fun g => ∏ i ∈ insert a s, P i g) = fun g => P a g * ∏ i ∈ s, P i g := by
      funext g; rw [Finset.prod_insert ha]
    rw [Finset.sum_insert ha, e]
    exact this

lemma polyClass_sum {ι : Type*} (s : Finset ι) (D : ℕ) (P : ι → Mat k r → ℂ)
    (h : ∀ i ∈ s, PolyClass D (P i)) : PolyClass D (fun g => ∑ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polyClass_mono (Nat.zero_le D) (polyClass_const (k := k) (r := r) 0)
  | insert a s ha ih =>
    have := polyClass_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    have e : (fun g => ∑ i ∈ insert a s, P i g) = fun g => P a g + ∑ i ∈ s, P i g := by
      funext g; rw [Finset.sum_insert ha]
    rw [e]
    exact this

lemma op_lin (ℓ : Mat k r →ₗ[ℝ] ℂ) (b : Bool) (X : Mat k r) :
    op b X (fun g => ℓ g) = fun g => (ℓ.comp (vf b X).toLinearMap) g := by
  funext g
  have hd : HasDerivAt (fun t : ℝ => ℓ (cv b X t g)) (ℓ (vf b X g)) 0 := by
    have h := (LinearMap.toContinuousLinearMap ℓ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (cv_hasDerivAt b X g)
    exact h
  show deriv (fun t : ℝ => ℓ (cv b X t g)) 0 = _
  rw [hd.deriv]; rfl

lemma W_lin (ℓ : Mat k r →ₗ[ℝ] ℂ) :
    ∀ a : List (Bool × Mat k r), ∃ ℓ' : Mat k r →ₗ[ℝ] ℂ, W a (fun g => ℓ g) = fun g => ℓ' g := by
  intro a
  induction a with
  | nil => exact ⟨ℓ, rfl⟩
  | cons x a ih =>
    obtain ⟨ℓ', he⟩ := ih
    exact ⟨ℓ'.comp (vf x.1 x.2).toLinearMap, by rw [W_cons, he, op_lin]⟩

lemma entry_le_gN (g : Mat k r) (i j : Fin (2 * r + k + 1)) : ‖g i j‖ ≤ gN g := by
  have h : ‖g i j‖ ^ 2 ≤ ∑ i, ∑ j, Complex.normSq (g i j) := by
    rw [Complex.sq_norm]
    exact (Finset.single_le_sum (f := fun j => Complex.normSq (g i j)) (fun _ _ => Complex.normSq_nonneg _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (g i j))
        (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i))
  have := Real.abs_le_sqrt h
  rwa [abs_of_nonneg (norm_nonneg _)] at this

lemma polyClass_lin (ℓ : Mat k r →ₗ[ℝ] ℂ) : PolyClass 1 (fun g => ℓ g) := by
  refine ⟨?_, fun a _ => ?_⟩
  · intro g₀ _
    refine ⟨Set.univ, fun g => ℓ g, isOpen_univ, trivial, ?_, fun _ _ _ => rfl⟩
    have h := ((LinearMap.toContinuousLinearMap ℓ).contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffOn
      (s := Set.univ)
    exact h
  · obtain ⟨ℓ', he⟩ := W_lin ℓ a
    refine ⟨∑ j : J k r, ‖ℓ' (Eb j)‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun g _ => ?_⟩
    rw [he, pow_one]
    have eg : ℓ' g = ∑ j : J k r, co g j • ℓ' (Eb j) := by
      conv_lhs => rw [← Mv_co g, Mv_sum]
      rw [map_sum]; simp only [map_smul]
    show ‖ℓ' g‖ ≤ _
    rw [eg, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hco : |co g j| ≤ ‖g j.1 j.2.1‖ := by
      unfold co; split_ifs
      · exact Complex.abs_im_le_norm _
      · exact Complex.abs_re_le_norm _
    exact hco.trans (entry_le_gN g _ _)

def varIn (p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) : Mat k r →ₗ[ℝ] ℂ where
  toFun g := g p.1 p.2
  map_add' _ _ := rfl
  map_smul' c g := by simp

def varCj (p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) : Mat k r →ₗ[ℝ] ℂ where
  toFun g := conj (g p.1 p.2)
  map_add' x y := by simp
  map_smul' c g := by simp [Complex.real_smul]

def varL : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) →
    (Mat k r →ₗ[ℝ] ℂ) := Sum.elim varIn varCj

theorem polyClass_of_isPolyDeg {D : ℕ} {P : Mat k r → ℂ} (hP : C2.IsPolyDeg D P) : PolyClass D P := by
  obtain ⟨q, hq, hPq⟩ := hP
  have e : P = fun g => ∑ d ∈ q.support, q.coeff d * ∏ v, (varL v g) ^ d v := by
    funext g
    rw [hPq g, MvPolynomial.eval_eq']
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    cases v <;> rfl
  rw [e]
  refine polyClass_sum _ _ _ fun d hd => ?_
  have hdeg : ∑ v, d v * 1 ≤ D := by
    have h1 := MvPolynomial.le_totalDegree hd
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1
    simpa using h1.trans hq
  refine polyClass_mono hdeg (polyClass_cmul _ ?_)
  exact polyClass_prod Finset.univ (fun v => d v * 1) (fun v g => (varL v g) ^ d v)
    fun v _ => polyClass_pow (polyClass_lin (varL v)) (d v)

end Formalism.FourierDecayAlt.P.ListSumSplittings

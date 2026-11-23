import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeRulesA1

open Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.ListSumInequalities

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma list_sum_flatMap {α β M : Type*} [AddCommMonoid M] (L : List α) (f : α → List β) (h : β → M) :
    ((L.flatMap f).map h).sum = (L.map fun a => ((f a).map h).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

lemma norm_list_sum_le {α : Type*} (L : List α) (f : α → E) :
    ‖(L.map f).sum‖ ≤ (L.map fun a => ‖f a‖).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

lemma list_sum_le {α : Type*} (L : List α) (f f' : α → ℝ) (h : ∀ a ∈ L, f a ≤ f' a) :
    (L.map f).sum ≤ (L.map f').sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

lemma list_sum_nonneg {α : Type*} (L : List α) (f : α → ℝ) (h : ∀ a ∈ L, 0 ≤ f a) : 0 ≤ (L.map f).sum := by
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact h a ha)

lemma list_sum_mul_left {α : Type*} (L : List α) (f : α → ℝ) (c : ℝ) :
    (L.map fun a => c * f a).sum = c * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [mul_add, ih]

lemma ckOn_rsmul {f : Mat k r → E} {m : ℕ∞} (a : ℝ) (hf : CkOn m (GV k r) f) :
    CkOn m (GV k r) (fun g => a • f g) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', heq⟩ := hf g₀ hg₀
  exact ⟨U, fun g => a • f' g, hU, hgU, hf'.const_smul a, fun g hg hgv => by
    show a • f g = a • f' g
    rw [heq g hg hgv]⟩

lemma ckOn_zero {m : ℕ∞} : CkOn m (GV k r) (fun _ : Mat k r => (0 : E)) := by
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

lemma op_listSum {b : Bool} {X : Mat k r} (hX : inLie k r X) :
    ∀ (L : List (ℝ × (Mat k r → E))), (∀ p ∈ L, CkOn ((1 : ℕ) : ℕ∞) (GV k r) p.2) →
      ∀ g ∈ GV k r, op b X (fun g' => (L.map fun p => p.1 • p.2 g').sum) g =
        (L.map fun p => p.1 • op b X p.2 g).sum := by
  intro L hL g hg
  have key : ∀ L' : List (ℝ × (Mat k r → E)), (∀ p ∈ L', CkOn ((1 : ℕ) : ℕ∞) (GV k r) p.2) →
      HasDerivAt (fun t : ℝ => (L'.map fun p => p.1 • p.2 (cv b X t g)).sum)
        ((L'.map fun p => p.1 • op b X p.2 g).sum) 0 := by
    intro L'
    induction L' with
    | nil =>
      intro _
      simpa using hasDerivAt_const (0 : ℝ) (0 : E)
    | cons p L' ih =>
      intro h
      have h1 := hasDerivAt_cv (h p (by simp)) hX hg b 0
      rw [cv_zero] at h1
      simp only [List.map_cons, List.sum_cons]
      exact (h1.const_smul p.1).add (ih fun q hq => h q (by simp [hq]))
  exact (key L hL).deriv

lemma vf_sum (b : Bool) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Y : ι → Mat k r) (g : Mat k r) :
    vf b (∑ i ∈ s, c i • Y i) g = ∑ i ∈ s, c i • vf b (Y i) g := by
  cases b <;> simp [vf, mulL, mulR, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]

lemma op_expand {H : Mat k r → E} {X g : Mat k r} (b : Bool) (hX : inLie k r X)
    (hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H) (hg : g ∈ GV k r) :
    op b X H g = ∑ i, kc i X • op b (Lt i) H g := by
  obtain ⟨U, f', hU, hgU, hf', heq⟩ := hH g hg
  have hd : DifferentiableAt ℝ f' g := (hf'.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hop : ∀ Z, inLie k r Z → op b Z H g = fderiv ℝ f' g (vf b Z g) := fun Z hZ =>
    (hasDerivAt_ext (f := H) b hU hgU hg hd heq hZ).deriv
  rw [hop X hX]
  conv_lhs => rw [expandL hX]
  rw [vf_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hop _ (Lt_unit i).1]

def expW : List (Bool × Mat k r) → List (ℝ × List (Bool × Mat k r))
  | [] => [(1, [])]
  | x :: w => (expW w).flatMap fun p =>
      (Finset.univ.toList : List (J k r)).map fun i => (kc i x.2 * p.1, (x.1, Lt i) :: p.2)

def bw : List Bool → List (List (Bool × Mat k r))
  | [] => [[]]
  | b :: τ => (bw τ).flatMap fun w => (Finset.univ.toList : List (J k r)).map fun i => (b, Lt i) :: w

lemma bw_tags : ∀ (τ : List Bool), ∀ w' ∈ bw (k := k) (r := r) τ, w'.map Prod.fst = τ := by
  intro τ
  induction τ with
  | nil =>
    intro w' hw
    simp only [bw, List.mem_singleton] at hw
    subst hw
    rfl
  | cons b τ ih =>
    intro w' hw
    simp only [bw, List.mem_flatMap, List.mem_map] at hw
    obtain ⟨w, hw, i, -, rfl⟩ := hw
    simp [ih w hw]

lemma expW_snd (w : List (Bool × Mat k r)) : (expW w).map Prod.snd = bw (w.map Prod.fst) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [expW, List.map_cons, bw, ← ih, List.map_flatMap, List.flatMap_map, List.map_map,
      Function.comp_def]

lemma expW_mem (w : List (Bool × Mat k r)) :
    ∀ p ∈ expW w, p.2.length = w.length ∧ ∀ y ∈ p.2, unitLie k r y.2 := by
  induction w with
  | nil =>
    intro p hp
    simp only [expW, List.mem_singleton] at hp
    subst hp
    simp
  | cons x w ih =>
    intro p hp
    simp only [expW, List.mem_flatMap, List.mem_map] at hp
    obtain ⟨q, hq, i, -, rfl⟩ := hp
    obtain ⟨h1, h2⟩ := ih q hq
    refine ⟨by simp [h1], ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Lt_unit i
    · exact h2 y hy

def Kc (k r : ℕ) : ℝ := 1 + ∑ i : J k r, ‖prj (Eb i)‖

lemma one_le_Kc : 1 ≤ Kc k r := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)

lemma kc_le {X : Mat k r} (hX : unitLie k r X) (i : J k r) : |kc i X| ≤ Kc k r := by
  have hco : |co X i| ≤ 1 := by
    unfold co
    split_ifs
    · exact (Complex.abs_im_le_norm _).trans (hX.2 _ _)
    · exact (Complex.abs_re_le_norm _).trans (hX.2 _ _)
  rw [kc, abs_mul, abs_norm]
  calc |co X i| * ‖prj (Eb i)‖ ≤ 1 * ‖prj (Eb i)‖ := mul_le_mul_of_nonneg_right hco (norm_nonneg _)
    _ = ‖prj (Eb i)‖ := one_mul _
    _ ≤ ∑ j : J k r, ‖prj (Eb j)‖ :=
        Finset.single_le_sum (f := fun j => ‖prj (Eb j)‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ Kc k r := le_add_of_nonneg_left zero_le_one

lemma expW_coef (w : List (Bool × Mat k r)) (hw : ∀ y ∈ w, unitLie k r y.2) :
    ∀ p ∈ expW w, |p.1| ≤ Kc k r ^ w.length := by
  induction w with
  | nil =>
    intro p hp
    simp only [expW, List.mem_singleton] at hp
    subst hp
    simp
  | cons x w ih =>
    intro p hp
    simp only [expW, List.mem_flatMap, List.mem_map] at hp
    obtain ⟨q, hq, i, -, rfl⟩ := hp
    have hq' := ih (fun y hy => hw y (by simp [hy])) q hq
    have hk := kc_le (hw x (by simp)) i
    simp only [List.length_cons, pow_succ]
    rw [abs_mul, mul_comm (Kc k r ^ _)]
    exact mul_le_mul hk hq' (abs_nonneg _) (by linarith [one_le_Kc (k := k) (r := r)])

theorem W_expand : ∀ (w : List (Bool × Mat k r)), AllLie w → ∀ F : Mat k r → E,
    CkOn ((w.length : ℕ) : ℕ∞) (GV k r) F → ∀ g ∈ GV k r,
      W w F g = ((expW w).map fun p => p.1 • W p.2 F g).sum := by
  have hmono : ∀ {m n : ℕ} (F : Mat k r → E), n ≤ m → CkOn ((m : ℕ) : ℕ∞) (GV k r) F →
      CkOn ((n : ℕ) : ℕ∞) (GV k r) F := by
    intro m n F hnm hF g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', heq⟩ := hF g₀ hg₀
    exact ⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast hnm), heq⟩
  have hW_ck : ∀ w : List (Bool × Mat k r), AllLie w → ∀ (n : ℕ) (F : Mat k r → E),
      CkOn ((n + w.length : ℕ) : ℕ∞) (GV k r) F → CkOn ((n : ℕ) : ℕ∞) (GV k r) (W w F) := by
    intro w
    induction w with
    | nil =>
      intro _ n F hF
      simpa [W] using hF
    | cons x w ih =>
      intro hw n F hF
      have hw' : AllLie w := fun y hy => hw y (by simp [hy])
      have hlen : n + (x :: w).length = (n + 1) + w.length := by simp; omega
      rw [hlen] at hF
      exact ckOn_op n x.1 (ih hw' (n + 1) F hF) (hw x (by simp))
  have op_congr : ∀ (b : Bool) (Y : Mat k r) (H H' : Mat k r → E) (g : Mat k r), inLie k r Y →
      g ∈ GV k r → (∀ g' ∈ GV k r, H g' = H' g') → op b Y H g = op b Y H' g := by
    intro b Y H H' g hY hg h
    show deriv (fun t : ℝ => H (cv b Y t g)) 0 = deriv (fun t : ℝ => H' (cv b Y t g)) 0
    congr 1
    funext t
    exact h _ (cv_mem hY hg t)
  have swap : ∀ (L : List (ℝ × List (Bool × Mat k r))) (f : J k r → ℝ × List (Bool × Mat k r) → E),
      ∑ i, (L.map (f i)).sum = (L.map fun p => ∑ i, f i p).sum := by
    intro L f
    induction L with
    | nil => simp
    | cons p L ih => simp [Finset.sum_add_distrib, ih]
  intro w
  induction w with
  | nil =>
    intro _ F _ g _
    simp [W, expW]
  | cons x w ih =>
    intro hw F hF g hg
    have hx : inLie k r x.2 := hw x (by simp)
    have hw' : AllLie w := fun y hy => hw y (by simp [hy])
    have hlen : (x :: w).length = 1 + w.length := by simp [add_comm]
    rw [hlen] at hF
    have hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) (W w F) := hW_ck w hw' 1 F hF
    have hFw : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) F := hmono F (by omega) hF
    have hterm : ∀ i, op x.1 (Lt i) (W w F) g =
        ((expW w).map fun p => p.1 • op x.1 (Lt i) (W p.2 F) g).sum := by
      intro i
      rw [op_congr x.1 (Lt i) (W w F) (fun g' => ((expW w).map fun p => p.1 • W p.2 F g').sum) g
        (Lt_unit i).1 hg (fun g' hg' => ih hw' F hFw g' hg')]
      have hL := op_listSum (b := x.1) (Lt_unit i).1 ((expW w).map fun p => (p.1, W p.2 F)) ?_ g hg
      · simpa [List.map_map, Function.comp_def] using hL
      · intro q hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
        obtain ⟨hplen, hunit⟩ := expW_mem w p hp
        exact hW_ck p.2 (fun y hy => (hunit y hy).1) 1 F (by rw [hplen]; exact hF)
    show op x.1 x.2 (W w F) g = _
    rw [op_expand x.1 hx hH hg, Finset.sum_congr rfl (fun i _ => by rw [hterm i])]
    have e1 : ∀ i, kc i x.2 • ((expW w).map fun p => p.1 • op x.1 (Lt i) (W p.2 F) g).sum =
        ((expW w).map fun p => kc i x.2 • p.1 • op x.1 (Lt i) (W p.2 F) g).sum := fun i => by
      rw [List.smul_sum, List.map_map]
      rfl
    rw [Finset.sum_congr rfl (fun i _ => e1 i), swap, expW, list_sum_flatMap]
    congr 1
    apply List.map_congr_left
    intro p _
    rw [List.map_map, Finset.sum_map_toList]
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = (kc i x.2 * p.1) • op x.1 (Lt i) (W p.2 F) g
    rw [mul_smul]

lemma lr_tags (u v : List (Mat k r)) :
    (lr u v).map Prod.fst = List.replicate u.length true ++ List.replicate v.length false := by
  simp [lr, Function.comp_def, List.map_const']

private lemma eq_lr_take_drop_of_map_fst_eq_replicate (w' : List (Bool × Mat k r)) (a b : ℕ)
    (h : w'.map Prod.fst = List.replicate a true ++ List.replicate b false) :
    w' = lr ((w'.take a).map Prod.snd) ((w'.drop a).map Prod.snd) := by
  have hta : (w'.take a).map Prod.fst = List.replicate a true := by
    rw [List.map_take, h, List.take_left' (by simp)]
  have hdr : (w'.drop a).map Prod.fst = List.replicate b false := by
    rw [List.map_drop, h, List.drop_left' (by simp)]
  have e1 : w'.take a = ((w'.take a).map Prod.snd).map (fun X => (true, X)) := by
    rw [List.map_map]
    conv_lhs => rw [← List.map_id (w'.take a)]
    apply List.map_congr_left
    intro y hy
    have hy1 : y.1 ∈ (w'.take a).map Prod.fst := List.mem_map_of_mem hy
    rw [hta] at hy1
    show y = (true, y.2)
    exact Prod.ext (List.eq_of_mem_replicate hy1) rfl
  have e2 : w'.drop a = ((w'.drop a).map Prod.snd).map (fun X => (false, X)) := by
    rw [List.map_map]
    conv_lhs => rw [← List.map_id (w'.drop a)]
    apply List.map_congr_left
    intro y hy
    have hy1 : y.1 ∈ (w'.drop a).map Prod.fst := List.mem_map_of_mem hy
    rw [hdr] at hy1
    show y = (false, y.2)
    exact Prod.ext (List.eq_of_mem_replicate hy1) rfl
  calc w' = w'.take a ++ w'.drop a := (List.take_append_drop a w').symm
    _ = lr ((w'.take a).map Prod.snd) ((w'.drop a).map Prod.snd) := by
        rw [lr, ← e1, ← e2]

theorem rule_A2_of_word_expansion : C2.SmoothClassInFiniteOrder := by
  intro k r E _ _ A F hF m
  obtain ⟨hsm, hbd⟩ := hF
  classical
  let Cw : List (Bool × Mat k r) → ℝ := fun w' =>
    if h : ∃ uv : List (Mat k r) × List (Mat k r), (∀ X ∈ uv.1, unitLie k r X) ∧
        (∀ X ∈ uv.2, unitLie k r X) ∧ w' = lr uv.1 uv.2
    then max (Classical.choose (hbd h.choose.1 h.choose.2 h.choose_spec.1 h.choose_spec.2.1)) 0 else 0
  have hCw0 : ∀ w', 0 ≤ Cw w' := by
    intro w'
    dsimp only [Cw]
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  have hCw : ∀ (u v : List (Mat k r)), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → ∀ g ∈ GV k r,
      gN g ^ (A - C2.B0 r * ((u.length : ℝ) + v.length)) * ‖W (lr u v) F g‖ ≤ Cw (lr u v) := by
    intro u v hu hv g hg
    have h : ∃ uv : List (Mat k r) × List (Mat k r), (∀ X ∈ uv.1, unitLie k r X) ∧
        (∀ X ∈ uv.2, unitLie k r X) ∧ lr u v = lr uv.1 uv.2 := ⟨(u, v), hu, hv, rfl⟩
    dsimp only [Cw]
    rw [dif_pos h]
    obtain ⟨hu0, hv0, heq⟩ := h.choose_spec
    have hlen : (u.length : ℝ) + v.length = (h.choose.1.length : ℝ) + h.choose.2.length := by
      have h1 := congrArg List.length heq
      simp only [lr, List.length_append, List.length_map] at h1
      exact_mod_cast h1
    have hW : W (lr u v) F g = dLR h.choose.1 h.choose.2 F g :=
      (congrArg (fun w => W w F g) heq).trans (congrFun (dLR_eq _ _ F) g).symm
    have hspec := Classical.choose_spec (hbd h.choose.1 h.choose.2 hu0 hv0) g hg
    rw [hlen, hW]
    exact hspec.trans (le_max_left _ _)
  have hKc : 0 ≤ Kc k r := by linarith [one_le_Kc (k := k) (r := r)]
  refine ⟨∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1),
    Kc k r ^ (a + b) * ((bw (k := k) (r := r) (List.replicate a true ++ List.replicate b false)).map Cw).sum,
    ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', heq⟩ := hsm g₀ hg₀
    exact ⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast le_top), heq⟩
  · intro u v hu hv huv g hg
    have hAll : AllLie (lr u v) := by
      intro x hx
      simp only [lr, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact (hu X hX).1
      · exact (hv X hX).1
    have hunit : ∀ y ∈ lr u v, unitLie k r y.2 := by
      intro y hy
      simp only [lr, List.mem_append, List.mem_map] at hy
      rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact hu X hX
      · exact hv X hX
    have hlenlr : (lr u v).length = u.length + v.length := by simp [lr]
    have hck : CkOn (((lr u v).length : ℕ) : ℕ∞) (GV k r) F := fun g₀ hg₀ => by
      obtain ⟨U, f', hU, hgU, hf', heq⟩ := hsm g₀ hg₀
      exact ⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast le_top), heq⟩
    have hexp := W_expand (lr u v) hAll F hck g hg
    have hgN : 1 ≤ gN g := one_le_gN hg
    have hpos : 0 ≤ gN g ^ (A - C2.B0 r * (m : ℝ)) := Real.rpow_nonneg (by linarith) _
    have hmono : gN g ^ (A - C2.B0 r * (m : ℝ)) ≤ gN g ^ (A - C2.B0 r * ((u.length : ℝ) + v.length)) := by
      apply Real.rpow_le_rpow_of_exponent_le hgN
      have hB : 0 ≤ C2.B0 r := by unfold C2.B0; positivity
      have hle : ((u.length : ℝ) + v.length) ≤ m := by exact_mod_cast huv
      nlinarith
    have hterm : ∀ p ∈ expW (lr u v), gN g ^ (A - C2.B0 r * (m : ℝ)) * ‖p.1 • W p.2 F g‖ ≤
        Kc k r ^ (u.length + v.length) * Cw p.2 := by
      intro p hp
      obtain ⟨hplen, hpunit⟩ := expW_mem (lr u v) p hp
      have hcoef := expW_coef (lr u v) hunit p hp
      rw [hlenlr] at hcoef
      have htags : p.2.map Prod.fst = List.replicate u.length true ++ List.replicate v.length false := by
        have hm : p.2 ∈ bw ((lr u v).map Prod.fst) := by
          rw [← expW_snd]
          exact List.mem_map_of_mem hp
        rw [lr_tags] at hm
        exact bw_tags _ p.2 hm
      have hsplit := eq_lr_take_drop_of_map_fst_eq_replicate p.2 u.length v.length htags
      have hu'' : ∀ X ∈ (p.2.take u.length).map Prod.snd, unitLie k r X := by
        intro X hX
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hX
        exact hpunit y (List.mem_of_mem_take hy)
      have hv'' : ∀ X ∈ (p.2.drop u.length).map Prod.snd, unitLie k r X := by
        intro X hX
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hX
        exact hpunit y (List.mem_of_mem_drop hy)
      have hlen'' : (((p.2.take u.length).map Prod.snd).length : ℝ) + ((p.2.drop u.length).map Prod.snd).length =
          (u.length : ℝ) + v.length := by
        have h1 := congrArg List.length hsplit
        simp only [lr, List.length_append, List.length_map] at h1
        rw [hplen, hlenlr] at h1
        rw [List.length_map, List.length_map]
        exact_mod_cast h1.symm
      have hb := hCw _ _ hu'' hv'' g hg
      rw [← hsplit, hlen''] at hb
      rw [norm_smul, Real.norm_eq_abs]
      calc gN g ^ (A - C2.B0 r * (m : ℝ)) * (|p.1| * ‖W p.2 F g‖) =
            |p.1| * (gN g ^ (A - C2.B0 r * (m : ℝ)) * ‖W p.2 F g‖) := by ring
        _ ≤ Kc k r ^ (u.length + v.length) * Cw p.2 := by
          apply mul_le_mul hcoef _ (mul_nonneg hpos (norm_nonneg _)) (pow_nonneg hKc _)
          exact (mul_le_mul_of_nonneg_right hmono (norm_nonneg _)).trans hb
    rw [dLR_eq, hexp]
    have hnn : ∀ a b, 0 ≤ Kc k r ^ (a + b) *
        ((bw (k := k) (r := r) (List.replicate a true ++ List.replicate b false)).map Cw).sum :=
      fun a b => mul_nonneg (pow_nonneg hKc _) (list_sum_nonneg _ _ (fun w' _ => hCw0 w'))
    have hu' : u.length ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
    have hv' : v.length ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
    calc gN g ^ (A - C2.B0 r * (m : ℝ)) * ‖((expW (lr u v)).map fun p => p.1 • W p.2 F g).sum‖
        ≤ gN g ^ (A - C2.B0 r * (m : ℝ)) * ((expW (lr u v)).map fun p => ‖p.1 • W p.2 F g‖).sum :=
          mul_le_mul_of_nonneg_left (norm_list_sum_le _ _) hpos
      _ = ((expW (lr u v)).map fun p => gN g ^ (A - C2.B0 r * (m : ℝ)) * ‖p.1 • W p.2 F g‖).sum :=
          (list_sum_mul_left _ _ _).symm
      _ ≤ ((expW (lr u v)).map fun p => Kc k r ^ (u.length + v.length) * Cw p.2).sum :=
          list_sum_le _ _ _ hterm
      _ = Kc k r ^ (u.length + v.length) *
            ((bw (k := k) (r := r) (List.replicate u.length true ++ List.replicate v.length false)).map Cw).sum := by
          rw [list_sum_mul_left, ← lr_tags, ← expW_snd, List.map_map]
          rfl
      _ ≤ ∑ b ∈ Finset.range (m + 1), Kc k r ^ (u.length + b) *
            ((bw (k := k) (r := r) (List.replicate u.length true ++ List.replicate b false)).map Cw).sum :=
          Finset.single_le_sum (f := fun b => Kc k r ^ (u.length + b) *
            ((bw (k := k) (r := r) (List.replicate u.length true ++ List.replicate b false)).map Cw).sum)
            (fun b _ => hnn _ _) hv'
      _ ≤ _ :=
          Finset.single_le_sum (f := fun a => ∑ b ∈ Finset.range (m + 1), Kc k r ^ (a + b) *
            ((bw (k := k) (r := r) (List.replicate a true ++ List.replicate b false)).map Cw).sum)
            (fun a _ => Finset.sum_nonneg fun b _ => hnn a b) hu'

end Formalism.FourierDecayAlt.P.ListSumInequalities

namespace Formalism.FourierDecayAlt.P

theorem rule_A2_derivatives : C2.SmoothClassInFiniteOrder := by
  exact ListSumInequalities.rule_A2_of_word_expansion

end Formalism.FourierDecayAlt.P

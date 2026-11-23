import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Polynomial

namespace PositivityTheory.Rg.Cz

namespace CharacterRelations

section poly

variable {A : Type*} [Ring A] [Algebra ℂ A]

set_option linter.unusedSectionVars false

theorem comm_alg (y : A) (u : ℂ) : Commute y (algebraMap ℂ A u) := (Algebra.commutes u y).symm

theorem eval_mul_nc (p q : A[X]) (x : A) (h : ∀ k, Commute (q.coeff k) x) :
    (p * q).eval x = p.eval x * q.eval x := by
  exact Polynomial.eval₂_mul_noncomm (RingHom.id A) x h

theorem eval_sumMono (d : ℕ → A) (N : ℕ) (u : ℂ) :
    (∑ i ∈ Finset.range N, monomial i (d i)).eval (algebraMap ℂ A u) = ∑ i ∈ Finset.range N, u ^ i • d i := by
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_monomial, ← map_pow, Algebra.smul_def,
    Algebra.commutes]

theorem vanish (D : A[X]) (a : ℂ) (h : ∀ u : ℂ, u ≠ a → D.eval (algebraMap ℂ A u) = 0) : D = 0 := by
  ext i
  rw [Polynomial.coeff_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (D.coeff i)).1 (fun φ => ?_)
  let q : ℂ[X] := ∑ j ∈ Finset.range (D.natDegree + 1), monomial j (φ (D.coeff j))
  have hq : ∀ u : ℂ, u ≠ a → q.eval u = 0 := by
    intro u hu
    have e := congrArg φ (h u hu)
    rw [Polynomial.eval_eq_sum_range, map_zero, map_sum] at e
    simp only [q, Polynomial.eval_finset_sum, Polynomial.eval_monomial]
    rw [← e]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have q0 : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := {a}ᶜ) (fun u hu => hq u hu) ?_
    exact (Set.finite_singleton a).infinite_compl
  by_cases hi : i < D.natDegree + 1
  · have e := congrArg (fun p => p.coeff i) q0
    simpa [q, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, hi] using e
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

theorem prod_neg_zero (L : List A) (h : (L.map fun x => -x).prod = 0) : L.prod = 0 := by
  rw [List.prod_map_neg] at h
  have hu : IsUnit ((-1 : A) ^ L.length) := (isUnit_one.neg).pow _
  exact hu.mul_right_eq_zero.1 h

end poly

section rel

variable {V N : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup N] [Module ℂ N]
  (W : Submodule ℂ V) (q : W →ₗ[ℂ] N)

def Rel (X : Module.End ℂ V) (Y : Module.End ℂ N) : Prop := ∀ w : W, ∃ h : X w ∈ W, q ⟨X w, h⟩ = Y (q w)

variable {W q}

theorem rel_add {X X' Y Y'} (h : Rel W q X Y) (h' : Rel W q X' Y') : Rel W q (X + X') (Y + Y') := by
  intro w
  obtain ⟨h1, e1⟩ := h w
  obtain ⟨h2, e2⟩ := h' w
  refine ⟨W.add_mem h1 h2, ?_⟩
  show q (⟨X w, h1⟩ + ⟨X' w, h2⟩) = Y (q w) + Y' (q w)
  rw [map_add, e1, e2]

theorem rel_sub {X X' Y Y'} (h : Rel W q X Y) (h' : Rel W q X' Y') : Rel W q (X - X') (Y - Y') := by
  intro w
  obtain ⟨h1, e1⟩ := h w
  obtain ⟨h2, e2⟩ := h' w
  refine ⟨W.sub_mem h1 h2, ?_⟩
  show q (⟨X w, h1⟩ - ⟨X' w, h2⟩) = Y (q w) - Y' (q w)
  rw [map_sub, e1, e2]

theorem rel_mul {X X' Y Y'} (h : Rel W q X Y) (h' : Rel W q X' Y') : Rel W q (X * X') (Y * Y') := by
  intro w
  obtain ⟨h2, e2⟩ := h' w
  obtain ⟨h1, e1⟩ := h ⟨X' w, h2⟩
  exact ⟨h1, e1.trans (congrArg Y e2)⟩

theorem rel_alg (c : ℂ) : Rel W q (algebraMap ℂ _ c) (algebraMap ℂ _ c) := by
  intro w
  refine ⟨by rw [Module.algebraMap_end_apply]; exact W.smul_mem c w.2, ?_⟩
  have e : (⟨algebraMap ℂ (Module.End ℂ V) c w, by rw [Module.algebraMap_end_apply]; exact W.smul_mem c w.2⟩ : W) = c • w :=
    Subtype.ext (by simp [Module.algebraMap_end_apply])
  rw [e, map_smul, Module.algebraMap_end_apply]

theorem rel_zero : Rel W q 0 0 := by
  simpa using rel_alg (W := W) (q := q) 0

theorem rel_intCast (z : ℤ) : Rel W q (z : Module.End ℂ V) (z : Module.End ℂ N) := by
  simpa [map_intCast] using rel_alg (W := W) (q := q) (z : ℂ)

theorem rel_sum {ι : Type*} (s : Finset ι) (X : ι → Module.End ℂ V) (Y : ι → Module.End ℂ N)
    (h : ∀ i, Rel W q (X i) (Y i)) : Rel W q (∑ i ∈ s, X i) (∑ i ∈ s, Y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rel_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha]; exact rel_add (h a) ih

theorem rel_prod {t : ℕ} (X : Fin t → Module.End ℂ V) (Y : Fin t → Module.End ℂ N)
    (h : ∀ i, Rel W q (X i) (Y i)) : Rel W q (List.ofFn X).prod (List.ofFn Y).prod := by
  induction t with
  | zero => simpa using rel_alg (W := W) (q := q) 1
  | succ t ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact rel_mul (h 0) (ih _ _ fun i => h i.succ)

theorem rel_uniq (hq : Function.Surjective q) {X Y Y'} (h : Rel W q X Y) (h' : Rel W q X Y') : Y = Y' := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨w, rfl⟩ := hq y
  obtain ⟨h1, e1⟩ := h w
  obtain ⟨h2, e2⟩ := h' w
  rw [← e1, ← e2]

variable {n : ℕ}

theorem rel_qdet (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ N)
    (h : ∀ a b, Rel W q (E a b) (F a b)) (u : ℂ) : Rel W q (qdet E u) (qdet F u) := by
  simp only [qdet, qminor]
  refine rel_sum _ _ _ fun σ => rel_mul (rel_intCast _) (rel_prod _ _ fun k => ?_)
  unfold Tm
  refine rel_add ?_ (h _ _)
  split_ifs
  · exact rel_alg _
  · exact rel_zero

theorem rel_gl (hq : Function.Surjective q) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ N)
    (hE : GlRel E) (h : ∀ a b, Rel W q (E a b) (F a b)) : GlRel F := by
  intro a b c d
  have h1 := rel_sub (rel_mul (h a b) (h c d)) (rel_mul (h c d) (h a b))
  rw [hE a b c d] at h1
  have h2 : Rel W q ((if b = c then E a d else 0) - if d = a then E c b else 0)
      ((if b = c then F a d else 0) - if d = a then F c b else 0) := by
    refine rel_sub ?_ ?_
    · split_ifs
      · exact h _ _
      · exact rel_zero
    · split_ifs
      · exact h _ _
      · exact rel_zero
  exact rel_uniq hq h1 h2

end rel

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem piJ_one (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) :
    PiJ 1 E u = algebraMap ℂ _ u + Om E (0 : Fin 1) := by
  simp [PiJ, xJ]

theorem lift_alg {P : Type} (c : ℂ) :
    (lift (algebraMap ℂ (Module.End ℂ M) c) : Module.End ℂ (TV n M P)) = algebraMap ℂ _ c := by
  ext f I
  simp [lift, Module.algebraMap_end_apply]

theorem qdet_comm {A : Type*} [Ring A] [Algebra ℂ A] (T : A) (E : Fin n → Fin n → A)
    (h : ∀ a b, Commute T (E a b)) (u : ℂ) : Commute T (qdet E u) := by
  simp only [qdet, qminor]
  refine Commute.sum_right _ _ _ fun σ _ => ?_
  refine Commute.mul_right Commute.intCast_right (Commute.list_prod_right _ _ ?_)
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨k, rfl⟩ := hx
  unfold Tm
  refine Commute.add_right ?_ (h _ _)
  split_ifs
  · exact comm_alg _ _
  · exact Commute.zero_right _

theorem part1 (hT : TensorGl) (hS : StepFormula) (hQ : QdetFacts) (E : Fin n → Fin n → Module.End ℂ M)
    (hE : GlRel E) (l : Fin n → ℂ) (hl : HasChar E l) :
    (List.ofFn fun k => Om E (0 : Fin 1) - algebraMap ℂ _ (l k)).prod = 0 := by
  classical
  have hG := hT n M (Fin 1) E hE Finset.univ
  obtain ⟨c, hc⟩ := (hQ n (TV n M (Fin 1)) (tE Finset.univ E) hG.1).2.1
  have hcomm : ∀ u, Commute (Om E (0 : Fin 1)) (qdet (tE Finset.univ E) u) := fun u =>
    qdet_comm _ _ (fun a b => hG.2.1 0 (Finset.mem_univ _) a b) u
  have hid : ∀ u : ℂ, qdet (tE Finset.univ E) u * (algebraMap ℂ (Module.End ℂ (TV n M (Fin 1))) u + Om E 0) =
      algebraMap ℂ _ (∏ k, (u + l k)) * (algebraMap ℂ _ u + (1 + Om E 0)) := by
    intro u
    have e := hS n M E hE 1 u
    rw [piJ_one, piJ_one, hl u, lift_alg] at e
    rw [← ((comm_alg _ u).symm.add_left (hcomm u)).eq, e, map_add, map_one, add_assoc]
  have hP : (∑ i ∈ Finset.range (n + 1), monomial i (c i)) * (X + C (Om E (0 : Fin 1))) -
      (∏ k, (X + C (l k))).map (algebraMap ℂ (Module.End ℂ (TV n M (Fin 1)))) * (X + C (1 + Om E 0)) = 0 := by
    apply vanish _ 0
    intro u _
    rw [Polynomial.eval_sub, eval_mul_nc _ _ _ (fun k => comm_alg _ _), eval_mul_nc _ _ _ (fun k => comm_alg _ _),
      eval_sumMono, ← hc, Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval_prod]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    rw [hid, sub_self]
  have hc' : ∀ a : Module.End ℂ (TV n M (Fin 1)), Commute a (Om E 0) →
      ∀ k, Commute ((X + C a).coeff k) (-Om E (0 : Fin 1)) := by
    intro a ha k
    rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
    refine Commute.add_left ?_ ?_ <;> split_ifs <;> simp [ha.neg_right]
  have e := congrArg (Polynomial.eval (-Om E (0 : Fin 1))) hP
  rw [Polynomial.eval_sub, eval_mul_nc _ _ _ (hc' _ (Commute.refl _)),
    eval_mul_nc _ _ _ (hc' _ ((Commute.one_left _).add_left (Commute.refl _))), Polynomial.eval_zero] at e
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at e
  rw [neg_add_cancel, mul_zero, zero_sub, show -Om E (0 : Fin 1) + (1 + Om E 0) = 1 by abel, mul_one,
    neg_eq_zero, Polynomial.eval_map, ← Polynomial.aeval_def, ← List.prod_ofFn, map_list_prod,
    List.map_ofFn] at e
  apply prod_neg_zero
  rw [List.map_ofFn]
  refine Eq.trans (congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))) e
  simp only [Function.comp_apply, map_add, Polynomial.aeval_X, Polynomial.aeval_C, neg_sub]
  abel

theorem part2 (hT : TensorGl) (hS : StepFormula) (hQ : QdetFacts) (E : Fin n → Fin n → Module.End ℂ M)
    (hE : GlRel E) (l : Fin n → ℂ) (hl : HasChar E l)
    (W : Submodule ℂ (TV n M (Fin 1))) (N : Type) [AddCommGroup N] [Module ℂ N] (F : Fin n → Fin n → Module.End ℂ N)
    (q : W →ₗ[ℂ] N) (hW : ∀ a b, ∀ w ∈ W, tE Finset.univ E a b w ∈ W) (hO : ∀ w ∈ W, Om E 0 w ∈ W) (k : Fin n)
    (hq : Function.Surjective q) (hqF : ∀ a b (w : W), q ⟨_, hW a b w w.2⟩ = F a b (q w))
    (hqO : ∀ w : W, q ⟨_, hO w w.2⟩ = l k • q w) : HasChar F (Function.update l k (l k + 1)) := by
  classical
  have hG := hT n M (Fin 1) E hE Finset.univ
  have hrelT : ∀ a b, Rel W q (tE Finset.univ E a b) (F a b) := fun a b w => ⟨hW a b w w.2, hqF a b w⟩
  have hrelO : Rel W q (Om E 0) (algebraMap ℂ (Module.End ℂ N) (l k)) := fun w =>
    ⟨hO w w.2, by rw [Module.algebraMap_end_apply]; exact hqO w⟩
  have hFG : GlRel F := rel_gl hq _ F hG.1 hrelT
  obtain ⟨c, hc⟩ := (hQ n N F hFG).2.1
  have key : ∀ u : ℂ, u ≠ -l k →
      qdet F u = algebraMap ℂ _ (∏ j, (u + Function.update l k (l k + 1) j)) := by
    intro u hu
    have hu' : u + l k ≠ 0 := fun h0 => hu (eq_neg_of_add_eq_zero_left h0)
    have hL := rel_mul (rel_add (rel_alg (W := W) (q := q) u) hrelO) (rel_qdet _ _ hrelT u)
    have e := hS n M E hE 1 u
    rw [piJ_one, piJ_one, hl u, lift_alg] at e
    rw [e] at hL
    have hR := rel_mul (rel_alg (W := W) (q := q) (∏ j, (u + l j)))
      (rel_add (rel_alg (W := W) (q := q) (u + 1)) hrelO)
    have h3 := rel_uniq hq hL hR
    rw [← map_add (algebraMap ℂ (Module.End ℂ N)), ← map_add (algebraMap ℂ (Module.End ℂ N)),
      ← map_mul (algebraMap ℂ (Module.End ℂ N))] at h3
    have hs : (∏ j, (u + l j)) * (u + 1 + l k) = (u + l k) * ∏ j, (u + Function.update l k (l k + 1) j) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
        Function.update_self]
      have hj : ∀ j ∈ Finset.univ.erase k, u + Function.update l k (l k + 1) j = u + l j := fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [Finset.prod_congr rfl hj]
      ring
    rw [hs, map_mul] at h3
    calc qdet F u = algebraMap ℂ (Module.End ℂ N) (u + l k)⁻¹ * (algebraMap ℂ _ (u + l k) * qdet F u) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hu', map_one, one_mul]
      _ = _ := by rw [h3, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hu', map_one, one_mul]
  have hD := vanish ((∑ i ∈ Finset.range (n + 1), monomial i (c i)) -
      (∏ j, (X + C (Function.update l k (l k + 1) j))).map (algebraMap ℂ (Module.End ℂ N))) (-l k) (by
    intro u hu
    rw [Polynomial.eval_sub, eval_sumMono, ← hc, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      Polynomial.eval_prod, key u hu]
    simp)
  intro u
  have e := congrArg (Polynomial.eval (algebraMap ℂ (Module.End ℂ N) u)) hD
  rw [Polynomial.eval_sub, eval_sumMono, ← hc, Polynomial.eval_map, Polynomial.eval₂_at_apply,
    Polynomial.eval_prod, Polynomial.eval_zero, sub_eq_zero] at e
  simpa using e

end CharacterRelations

theorem stepChar_of : TensorGl → StepFormula → QdetFacts → StepChar := by
  intro hT hS hQ n M _ _ E hE l hl
  refine ⟨CharacterRelations.part1 hT hS hQ E hE l hl, ?_⟩
  intro W N _ _ F q hW hO k hq hqF hqO
  exact CharacterRelations.part2 hT hS hQ E hE l hl W N F q hW hO k hq hqF hqO

end PositivityTheory.Rg.Cz

end

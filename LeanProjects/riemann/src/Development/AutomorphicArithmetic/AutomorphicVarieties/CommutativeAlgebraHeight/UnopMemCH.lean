import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section SlopeTestRemainingChoices

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E]

private theorem unopS_tmul (S : Type) [CommRing S] [Algebra A S] (s : S) (a : Eᵐᵒᵖ) :
    Det.unopS A E S (s ⊗ₜ a) = s ⊗ₜ a.unop := by
  simp [Det.unopS]

private theorem unopS_surj (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] E) :
    ∃ z, Det.unopS A E S z = y := by
  induction y with
  | zero => exact ⟨0, map_zero _⟩
  | tmul s a => exact ⟨s ⊗ₜ MulOpposite.op a, unopS_tmul S s _⟩
  | add a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', map_add _ _ _⟩

private theorem op_D (D : Det n A E) (S : Type) [CommRing S] [Algebra A S] (x : S ⊗[A] Eᵐᵒᵖ) :
    D.op.D S x = D.D S (Det.unopS A E S x) := rfl

private theorem unopS_map (S T : Type) [CommRing S] [Algebra A S] [CommRing T] [Algebra A T] (φ : S →ₐ[A] T)
    (x : S ⊗[A] Eᵐᵒᵖ) :
    Det.unopS A E T (Algebra.TensorProduct.map φ (AlgHom.id A _) x) =
      Algebra.TensorProduct.map φ (AlgHom.id A E) (Det.unopS A E S x) := by
  induction x with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul s a => simp [Det.unopS]

private theorem op_chiS (D : Det n A E) (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] Eᵐᵒᵖ) :
    D.op.chiS S y = D.chiS S (Det.unopS A E S y) := by
  unfold Det.chiS
  rw [op_D, map_sub, unopS_map, unopS_tmul, MulOpposite.unop_one]

private theorem unopS_pow (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] Eᵐᵒᵖ) (k : ℕ) :
    Det.unopS A E S (y ^ k) = Det.unopS A E S y ^ k := by
  induction k with
  | zero => simp [Det.unopS, Algebra.TensorProduct.one_def]
  | succ k ih => rw [pow_succ, Det.unopS_mul, ih, pow_succ']

private theorem unopS_aeval (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] Eᵐᵒᵖ) (p : Polynomial S) :
    Det.unopS A E S (Polynomial.aeval y p) = Polynomial.aeval (Det.unopS A E S y) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial k s =>
    rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, unopS_pow]

private theorem unopS_gen {k : ℕ} (x : Fin k → Eᵐᵒᵖ) :
    Det.unopS A E _ (Det.gen (A := A) x) = Det.gen (A := A) fun a => (x a).unop := by
  unfold Det.gen
  rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => unopS_tmul _ _ _

private theorem lid_unopS (S : Type) [CommRing S] [Algebra A S] (f : S →ₗ[A] A) (y : S ⊗[A] Eᵐᵒᵖ) :
    (TensorProduct.lid A Eᵐᵒᵖ (f.rTensor Eᵐᵒᵖ y)).unop =
      TensorProduct.lid A E (f.rTensor E (Det.unopS A E S y)) := by
  induction y with
  | zero => simp
  | add a b ha hb => simp only [map_add, MulOpposite.unop_add, ha, hb]
  | tmul s a => simp [unopS_tmul]

private theorem op_chElt (D : Det n A E) {k : ℕ} (x : Fin k → Eᵐᵒᵖ) (α : Fin k →₀ ℕ) :
    (D.op.chElt x α).unop = D.chElt (fun a => (x a).unop) α := by
  unfold Det.chElt
  rw [lid_unopS, unopS_aeval, op_chiS, unopS_gen]

private theorem unop_mem_CH (D : Det n A E) {x : Eᵐᵒᵖ} (h : x ∈ D.op.CH) : x.unop ∈ D.CH := by
  unfold Det.CH at h
  induction h using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨k, y, α, rfl⟩ := hx
    exact TwoSidedIdeal.subset_span ⟨k, _, α, op_chElt D y α⟩
  | zero => exact D.CH.zero_mem
  | add x y _ _ hx hy => exact D.CH.add_mem hx hy
  | neg x _ hx => exact D.CH.neg_mem hx
  | left_absorb a x _ hx => exact D.CH.mul_mem_right _ _ hx
  | right_absorb b x _ hx => exact D.CH.mul_mem_left _ _ hx

private theorem op_mem_CH (D : Det n A E) {x : E} (h : x ∈ D.CH) : MulOpposite.op x ∈ D.op.CH := by
  unfold Det.CH at h
  induction h using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨k, y, α, rfl⟩ := hx
    exact TwoSidedIdeal.subset_span ⟨k, fun a => MulOpposite.op (y a), α,
      (congrArg MulOpposite.op (op_chElt D (fun a => MulOpposite.op (y a)) α)).symm⟩
  | zero => exact D.op.CH.zero_mem
  | add x y _ _ hx hy => exact D.op.CH.add_mem hx hy
  | neg x _ hx => exact D.op.CH.neg_mem hx
  | left_absorb a x _ hx => exact D.op.CH.mul_mem_right _ _ hx
  | right_absorb b x _ hx => exact D.op.CH.mul_mem_left _ _ hx

end SlopeTestRemainingChoices

theorem UpperTheory.V.CA.d_op :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E), (∀ x, D.op.chi (MulOpposite.op x) = D.chi x) ∧ (∀ x, MulOpposite.op x ∈ D.op.ker ↔ x ∈ D.ker) ∧ ∀ x, MulOpposite.op x ∈ D.op.CH ↔ x ∈ D.CH := by
  intro n A E _ _ _ D
  refine ⟨fun x => ?_, fun x => ?_, fun x => ⟨fun h => unop_mem_CH D h, op_mem_CH D⟩⟩
  · unfold Det.chi
    rw [op_D, map_sub, unopS_tmul, unopS_tmul, MulOpposite.unop_one, MulOpposite.unop_op]
  · rw [Det.mem_ker, Det.mem_ker]
    constructor
    · intro h S _ _ y u v
      obtain ⟨y, rfl⟩ := unopS_surj S y
      obtain ⟨u, rfl⟩ := unopS_surj S u
      obtain ⟨v, rfl⟩ := unopS_surj S v
      have := h S y v u
      rw [op_D, op_D, map_add, Det.unopS_mul, Det.unopS_mul, unopS_tmul, MulOpposite.unop_op, ← mul_assoc] at this
      exact this
    · intro h S _ _ y u v
      rw [op_D, op_D, map_add, Det.unopS_mul, Det.unopS_mul, unopS_tmul, MulOpposite.unop_op, ← mul_assoc]
      exact h S _ _ _

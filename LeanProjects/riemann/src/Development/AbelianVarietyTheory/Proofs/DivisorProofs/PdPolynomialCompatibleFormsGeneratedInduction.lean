import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem rel_mul_mem_right {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {J : Ideal B}
    (δ : DividedPowers J) {x : DR R B} (hx : x ∈ rel R δ) (y : DR R B) : x * y ∈ rel R δ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, a, ha, rfl⟩ := hx
    rw [ι_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n, a, ha, rfl⟩)
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul a x _ ih => rw [smul_eq_mul, mul_assoc]; exact Ideal.mul_mem_left _ _ ih

section Poly

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {J : Ideal B}
  {Q : PDPoly B} [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J))
  (h : SemiHom (RingHom.id R) (algebraMap B Q.P))

def pdGen : Set (DR R Q.P) :=
  {x | ∃ n α, x = Q.e n • h.mDR α} ∪ {x | ∃ n α, x = Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α)} ∪
    (rel R η : Set (DR R Q.P))

theorem pdGen_mem_one (n : ℕ) (α : DR R B) : Q.e n • h.mDR α ∈ pdGen η h :=
  Set.mem_union_left _ (Set.mem_union_left _ ⟨n, α, rfl⟩)

theorem pdGen_mem_two (n : ℕ) (α : DR R B) : Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α) ∈ pdGen η h :=
  Set.mem_union_left _ (Set.mem_union_right _ ⟨n, α, rfl⟩)

theorem pdGen_mem_rel {x : DR R Q.P} (hx : x ∈ rel R η) : x ∈ pdGen η h :=
  Set.mem_union_right _ hx

theorem smul_gen_mem (b : Q.P) : ∀ α : DR R B,
    b • h.mDR α ∈ AddSubgroup.closure (pdGen η h) ∧
      b • (ι1 (D R Q.P (Q.e 1)) * h.mDR α) ∈ AddSubgroup.closure (pdGen η h) := by
  have hb : b ∈ Submodule.span B (Set.range Q.e) := by rw [Q.e.span_eq]; trivial
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    exact fun α ↦ ⟨AddSubgroup.subset_closure (pdGen_mem_one η h n α),
      AddSubgroup.subset_closure (pdGen_mem_two η h n α)⟩
  | zero => intro α; simp only [zero_smul]; exact ⟨zero_mem _, zero_mem _⟩
  | add x y _ _ hx hy =>
    intro α
    rw [add_smul, add_smul]
    exact ⟨add_mem (hx α).1 (hy α).1, add_mem (hx α).2 (hy α).2⟩
  | smul c x _ ih =>
    intro α
    have e1 : (c • x) • h.mDR α = x • h.mDR (c • α) := by
      rw [h.mDR_smul, Algebra.smul_def c x, mul_comm, mul_smul]
    have e2 : (c • x) • (ι1 (D R Q.P (Q.e 1)) * h.mDR α) = x • (ι1 (D R Q.P (Q.e 1)) * h.mDR (c • α)) := by
      rw [h.mDR_smul, mul_smul_comm, Algebra.smul_def c x, mul_comm, mul_smul]
    rw [e1, e2]
    exact ih (c • α)

theorem smul_mem_closure (b : Q.P) {x : DR R Q.P} (hx : x ∈ AddSubgroup.closure (pdGen η h)) :
    b • x ∈ AddSubgroup.closure (pdGen η h) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with (⟨n, α, rfl⟩ | ⟨n, α, rfl⟩) | hx
    · rw [smul_smul]; exact (smul_gen_mem η h _ α).1
    · rw [smul_smul]; exact (smul_gen_mem η h _ α).2
    · refine AddSubgroup.subset_closure (pdGen_mem_rel η h ?_)
      rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ hx
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem D_mem_closure {δ : DividedPowers J} (hs : Q.IsStd δ η) (b : Q.P) :
    ι1 (D R Q.P b) ∈ AddSubgroup.closure (pdGen η h) := by
  have hb : b ∈ Submodule.span B (Set.range Q.e) := by rw [Q.e.span_eq]; trivial
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    cases n with
    | zero => rw [Q.e_zero, Derivation.map_one_eq_zero, map_zero]; exact zero_mem _
    | succ n =>
      have hr : ι1 (D R Q.P (η.dpow (n + 1) (Q.e 1)) - η.dpow n (Q.e 1) • D R Q.P (Q.e 1)) ∈ rel R η :=
        Ideal.subset_span ⟨n, Q.e 1, Q.e_one_mem_ext J, rfl⟩
      rw [hs.var, hs.var] at hr
      have e : ι1 (D R Q.P (Q.e (n + 1))) = ι1 (D R Q.P (Q.e (n + 1)) - Q.e n • D R Q.P (Q.e 1)) +
          Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR 1) := by
        rw [map_one h.mDR, mul_one, map_sub, map_smul, sub_add_cancel]
      rw [e]
      exact add_mem (AddSubgroup.subset_closure (pdGen_mem_rel η h hr))
        (AddSubgroup.subset_closure (pdGen_mem_two η h n 1))
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
  | smul c x _ ih =>
    rw [Algebra.smul_def, Derivation.leibniz, map_add, map_smul, map_smul]
    refine add_mem (smul_mem_closure η h _ ih) ?_
    have e : ι1 (D R Q.P (algebraMap B Q.P c)) = h.mDR (ι1 (D R B c)) := by rw [h.mDR_ι, h.m1_D]
    rw [e]; exact (smul_gen_mem η h x _).1

omit [IsScalarTower R B Q.P] in

theorem mDR_mul_dtau (α β : DR R B) :
    h.mDR α * (ι1 (D R Q.P (Q.e 1)) * h.mDR β) = ι1 (D R Q.P (Q.e 1)) * h.mDR (sgn α * β) := by
  rw [← mul_assoc, map_mul, h.mDR_sgn, ← mul_assoc, ι_mul (D R Q.P (Q.e 1)) (sgn (h.mDR α)), sgn_sgn]

theorem gen_mul_gen {x y : DR R Q.P} (hx : x ∈ pdGen η h) (hy : y ∈ pdGen η h) :
    x * y ∈ AddSubgroup.closure (pdGen η h) := by
  have base : ∀ α : DR R B, h.mDR α ∈ AddSubgroup.closure (pdGen η h) := fun α ↦ by
    have := (smul_gen_mem η h 1 α).1; rwa [one_smul] at this
  have base2 : ∀ α : DR R B, ι1 (D R Q.P (Q.e 1)) * h.mDR α ∈ AddSubgroup.closure (pdGen η h) := fun α ↦ by
    have := (smul_gen_mem η h 1 α).2; rwa [one_smul] at this
  have relL : ∀ {z : DR R Q.P} (w : DR R Q.P), z ∈ rel R η → w * z ∈ AddSubgroup.closure (pdGen η h) :=
    fun w hz ↦ AddSubgroup.subset_closure (pdGen_mem_rel η h (Ideal.mul_mem_left _ w hz))
  rcases hx with (⟨m, α, rfl⟩ | ⟨m, α, rfl⟩) | hx
  · rcases hy with (⟨n, β, rfl⟩ | ⟨n, β, rfl⟩) | hy
    · rw [smul_mul_assoc, mul_smul_comm, ← map_mul]
      exact smul_mem_closure η h _ (smul_mem_closure η h _ (base _))
    · rw [smul_mul_assoc, mul_smul_comm, mDR_mul_dtau]
      exact smul_mem_closure η h _ (smul_mem_closure η h _ (base2 _))
    · exact relL _ hy
  · rcases hy with (⟨n, β, rfl⟩ | ⟨n, β, rfl⟩) | hy
    · rw [smul_mul_assoc, mul_smul_comm, mul_assoc, ← map_mul]
      exact smul_mem_closure η h _ (smul_mem_closure η h _ (base2 _))
    · rw [smul_mul_assoc, mul_smul_comm, mul_assoc, mDR_mul_dtau, ← mul_assoc, ExteriorAlgebra.ι_sq_zero,
        zero_mul, smul_zero, smul_zero]
      exact zero_mem _
    · exact relL _ hy
  · exact AddSubgroup.subset_closure (pdGen_mem_rel η h (rel_mul_mem_right η hx _))

theorem mul_mem_closure {x y : DR R Q.P} (hx : x ∈ AddSubgroup.closure (pdGen η h))
    (hy : y ∈ AddSubgroup.closure (pdGen η h)) : x * y ∈ AddSubgroup.closure (pdGen η h) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    induction hy using AddSubgroup.closure_induction with
    | mem y hy => exact gen_mul_gen η h hx hy
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

end Poly

theorem pdPoly_forms_induction : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B)
    (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J))
    (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η →
    (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) →
    (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (p : DR R Q.P → Prop),
    (∀ x ∈ rel R η, p x) → (∀ x y, p x → p y → p (x + y)) → (∀ n α, p (Q.e n • h.mDR α)) →
    (∀ n α, p (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α))) → ∀ x, p x := by
  intro R B _ _ _ J δ Q _ _ η _ h hs _ _ _ p hrel hadd h1 h2 x
  have hS : ∀ x, x ∈ AddSubgroup.closure (pdGen η h) := fun x ↦ by
    induction x using indDR with
    | h b =>
      have := (smul_gen_mem η h b 1).1
      rwa [map_one, ← Algebra.algebraMap_eq_smul_one] at this
    | hd b => exact D_mem_closure η h hs b
    | hm x y hx hy => exact mul_mem_closure η h hx hy
    | ha x y hx hy => exact add_mem hx hy
  have key : ∀ x ∈ AddSubgroup.closure (pdGen η h), p x ∧ p (-x) := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      rcases hx with (⟨n, α, rfl⟩ | ⟨n, α, rfl⟩) | hx
      · exact ⟨h1 n α, by rw [← smul_neg, ← map_neg]; exact h1 n (-α)⟩
      · exact ⟨h2 n α, by rw [← smul_neg, ← mul_neg, ← map_neg]; exact h2 n (-α)⟩
      · exact ⟨hrel x hx, hrel _ (neg_mem hx)⟩
    | zero => exact ⟨hrel 0 (zero_mem _), by rw [neg_zero]; exact hrel 0 (zero_mem _)⟩
    | add x y _ _ hx hy => exact ⟨hadd _ _ hx.1 hy.1, by rw [neg_add]; exact hadd _ _ hx.2 hy.2⟩
    | neg x _ hx => exact ⟨hx.2, by rw [neg_neg]; exact hx.1⟩
  exact (key x (hS x)).1

end GlobalTheory.PDForm

import Formalism.SharpRestriction.GrowthBounds.RootWeights.MemWeightSpaceIffDiagonalRep
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HwvLoweringSpanLower
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsotypicStableOperator

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def loweringMonoid (E : GLOps n K V) : Submonoid (Module.End K V) :=
  Submonoid.closure {g | ∃ c d : Fin n, d < c ∧ g = E c d}

def hwvLoweringSpan (E : GLOps n K V) (mu : Fin n → ℤ) : Submodule K V :=
  Submodule.span K {x | ∃ u ∈ loweringMonoid E, ∃ w, IsHWV E mu w ∧ x = u w}

theorem isotypic_stable_operator (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) {x : V} (hx : x ∈ isoSub E mu) :
    E a b x ∈ isoSub E mu := by
  first | exact UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator .. | (apply UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu a b x hx | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu a b x | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu a b | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu a | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n

theorem hwv_lowering_span_lower (E : GLOps n K V) (mu : Fin n → ℤ) {a b : Fin n} (hab : b < a) {x : V}
    (hx : x ∈ hwvLoweringSpan E mu) : E a b x ∈ hwvLoweringSpan E mu := by
  first | exact UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower .. | (apply UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a b hab x hx | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a b hab x | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a b hab | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a b | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n

theorem lowering_word_hwv_operator_mem {E : GLOps n K V} (hE : IsGLRep E) (mu : Fin n → ℤ) {w : V} (hw : IsHWV E mu w)
    {u : Module.End K V} (hu : u ∈ loweringMonoid E) : ∀ c d : Fin n, E c d (u w) ∈ hwvLoweringSpan E mu := by
  unfold loweringMonoid at hu
  induction hu using Submonoid.closure_induction_left with
  | one =>
    intro c d
    rw [Module.End.one_apply]
    rcases lt_trichotomy c d with h | h | h
    · rw [hw.2.2 c d h]; exact Submodule.zero_mem _
    · subst h
      rw [(mem_weightSpace_iff_diagonal_rep E mu w).1 hw.2.1 c]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, (loweringMonoid E).one_mem, w, hw, rfl⟩)
    · exact Submodule.subset_span ⟨E c d, Submonoid.subset_closure ⟨c, d, h, rfl⟩, w, hw, rfl⟩
  | mul_left g hg y _ ih =>
    obtain ⟨b, a, hab, rfl⟩ := hg
    intro c d
    rw [Module.End.mul_apply, gl_commutation_apply hE c d b a (y w)]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (hwv_lowering_span_lower E mu hab (ih c d)) ?_) ?_
    · split_ifs
      · exact ih c a
      · exact Submodule.zero_mem _
    · split_ifs
      · exact ih b d
      · exact Submodule.zero_mem _

theorem hwv_lowering_span_stable {E : GLOps n K V} (hE : IsGLRep E) (mu : Fin n → ℤ) (c d : Fin n) {x : V}
    (hx : x ∈ hwvLoweringSpan E mu) : E c d x ∈ hwvLoweringSpan E mu := by
  have hx' := hx
  unfold hwvLoweringSpan at hx'
  induction hx' using Submodule.span_induction with
  | mem x hx1 =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx1
    exact lowering_word_hwv_operator_mem hE mu hv hu c d
  | zero => simp
  | add x y hx1 hy1 hx2 hy2 =>
    rw [map_add]; exact Submodule.add_mem _ (hx2 hx1) (hy2 hy1)
  | smul c x hx1 hx2 => rw [map_smul]; exact Submodule.smul_mem _ _ (hx2 hx1)

theorem isotypic_le_lowering_span {E : GLOps n K V} (hE : IsGLRep E) (mu : Fin n → ℤ) : isoSub E mu ≤ hwvLoweringSpan E mu := by
  unfold isoSub
  rw [Submodule.span_le]
  rintro x ⟨u, hu, v, hv, rfl⟩
  unfold Umon at hu
  induction hu using Submonoid.closure_induction_left with
  | one => exact Submodule.subset_span ⟨1, (loweringMonoid E).one_mem, v, hv, rfl⟩
  | mul_left g hg y _ ih =>
    obtain ⟨ab, rfl⟩ := hg
    exact hwv_lowering_span_stable hE mu ab.1 ab.2 ih

theorem hwv_orthogonal_lowering_span [CharZero K] {E : GLOps n K V} (B : V →ₗ[K] V →ₗ[K] K)
    (hB : ∀ a b x y, B (E a b x) y = B x (E b a y)) {lam mu : Fin n → ℤ} (hne : lam ≠ mu) {v : V}
    (hv : IsHWV E lam v) {z : V} (hz : z ∈ hwvLoweringSpan E mu) : B v z = 0 := by
  unfold hwvLoweringSpan at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, w, hw, rfl⟩ := hx
    unfold loweringMonoid at hu
    induction hu using Submonoid.closure_induction_left with
    | one =>
      rw [Module.End.one_apply]
      obtain ⟨a, ha⟩ : ∃ a, lam a ≠ mu a := by
        by_contra h
        push_neg at h
        exact hne (funext h)
      have h1 := hB a a v w
      rw [(mem_weightSpace_iff_diagonal_rep E lam v).1 hv.2.1 a, (mem_weightSpace_iff_diagonal_rep E mu w).1 hw.2.1 a, map_smul, map_smul,
        LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
      have h2 : ((lam a : K) - (mu a : K)) * B v w = 0 := by rw [sub_mul, h1, sub_self]
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exfalso; apply ha
        have : (lam a : K) = (mu a : K) := sub_eq_zero.1 h3
        exact_mod_cast this
      · exact h3
    | mul_left g hg y _ _ =>
      obtain ⟨c, d, hcd, rfl⟩ := hg
      rw [Module.End.mul_apply, ← hB d c v (y w), hv.2.2 d c hcd]
      simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

theorem contravariant_orthogonality_holds : ContravariantIsotypicOrthogonal := by
  intro K V _ _ _ _ n E hE B hB lam mu hne x hx
  unfold isoSub at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    unfold Umon at hu
    induction hu using Submonoid.closure_induction_left with
    | one =>
      intro y hy
      exact hwv_orthogonal_lowering_span B hB hne hv (isotypic_le_lowering_span hE mu hy)
    | mul_left g hg u' _ ih =>
      obtain ⟨ab, rfl⟩ := hg
      intro y hy
      rw [Module.End.mul_apply]
      show B (E ab.1 ab.2 (u' v)) y = 0
      rw [hB]
      exact ih _ (isotypic_stable_operator E mu _ _ hy)
  | zero => intro y _; simp
  | add x y _ _ hx hy => intro z hz; rw [map_add, LinearMap.add_apply, hx z hz, hy z hz, add_zero]
  | smul c x _ hx => intro z hz; rw [map_smul, LinearMap.smul_apply, hx z hz, smul_zero]

end Formalism.MainNotions.G.GLWeightTheory

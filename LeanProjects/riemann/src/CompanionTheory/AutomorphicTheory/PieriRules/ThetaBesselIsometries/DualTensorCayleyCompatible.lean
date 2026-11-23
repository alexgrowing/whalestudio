import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DualTensorCapelliIntertwineStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.RawTens

def lm {k r : ℕ} {R R' : Rep k r} {T : R.H → R'.H} (h : SmMap R R' T) : R.smSub →ₗ[ℂ] R'.smSub where
  toFun v := ⟨T v, h.mem v v.2⟩
  map_add' v w := Subtype.ext (h.add v v.2 w w.2)
  map_smul' a v := Subtype.ext (h.smul a v v.2)

@[simp] theorem lm_coe {k r : ℕ} {R R' : Rep k r} {T : R.H → R'.H} (h : SmMap R R' T) (v : R.smSub) :
    ((lm h v : R'.smSub) : R'.H) = T v := rfl

section alg

variable {n : ℕ} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem change_inv (A B : Matrix (Fin n) (Fin n) ℂ) (h : A * B = 1) (x : Fin n → M) (c : Fin n) :
    ∑ d, B d c • ∑ e, A e d • x e = x c := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have : ∀ e, ∑ d, B d c * A e d = (1 : Matrix (Fin n) (Fin n) ℂ) e c := by
    intro e
    rw [← h, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  simp_rw [this]
  simp [Matrix.one_apply]

theorem dualTens_sum {ι : Type} (S : Finset ι) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n)
    (x : ι → Fin n → M) : dualTens E a b (∑ i ∈ S, x i) = ∑ i ∈ S, dualTens E a b (x i) := by
  funext i
  by_cases h : i = b <;> simp [dualTens, Finset.sum_apply, h, map_sum, Finset.sum_sub_distrib]

theorem alg {N : Fin n → Type} [∀ s, AddCommGroup (N s)] [∀ s, Module ℂ (N s)]
    (I : ∀ s, Fin n → N s →ₗ[ℂ] M) (P : ∀ s, Fin n → M →ₗ[ℂ] N s)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1) (hBA : B * A = 1)
    (E : Fin n → Fin n → Module.End ℂ M) (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s))
    (hI : ∀ s a b y c, I s c (F s a b y) =
      E a b (I s c y) - ∑ j, (B * Matrix.single a b (1 : ℂ) * A) j c • I s j y)
    (h1 : ∀ (x : Fin n → M) c, ∑ s, I s c (∑ d, P s d (x d)) = x c)
    (h2 : ∀ s y, ∑ c, P s c (I s c y) = y)
    (h3 : ∀ s t, s ≠ t → ∀ y, ∑ c, P s c (I t c y) = 0) :
    ∃ (io' : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr' : ∀ s, (Fin n → M) →ₗ[ℂ] N s),
      (∀ s a b y, io' s (F s a b y) = dualTens E a b (io' s y)) ∧
      (∀ s a b x, pr' s (dualTens E a b x) = F s a b (pr' s x)) ∧
      (∀ x, ∑ s, io' s (pr' s x) = x) ∧ (∀ s y, pr' s (io' s y) = y) ∧
      (∀ s t, s ≠ t → ∀ y, pr' s (io' t y) = 0) ∧
      (∀ s y d, io' s y d = ∑ c, B c d • I s c y) ∧
      ∀ s x, pr' s x = ∑ c, P s c (∑ d, A d c • x d) := by
  let io' : ∀ s, N s →ₗ[ℂ] (Fin n → M) := fun s => LinearMap.pi fun d => ∑ c, B c d • I s c
  let pr' : ∀ s, (Fin n → M) →ₗ[ℂ] N s := fun s =>
    ∑ c, (P s c).comp (∑ d, A d c • LinearMap.proj d)
  have e1 : ∀ s y d, io' s y d = ∑ c, B c d • I s c y := by
    intro s y d
    simp [io', LinearMap.sum_apply]
  have e2 : ∀ s x, pr' s x = ∑ c, P s c (∑ d, A d c • x d) := by
    intro s x
    simp only [pr', LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.proj_apply]
  have c1 : ∀ s a b y, io' s (F s a b y) = dualTens E a b (io' s y) := by
    intro s a b y
    funext d
    have hY : ∀ j c, (B * Matrix.single a b (1 : ℂ) * A) j c = A b c * B j a := by
      intro j c
      rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single a]
      · simp [mul_comm]
      · intro e _ he
        simp [Matrix.single_mul_apply_of_ne, he]
      · simp
    have hz : ∀ c, ∑ j, (B * Matrix.single a b (1 : ℂ) * A) j c • I s j y = A b c • io' s y a := by
      intro c
      rw [e1, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hY, mul_smul]
    have hd : ∑ c, B c d * A b c = if d = b then 1 else 0 := by
      have : ∑ c, B c d * A b c = (A * B) b d := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun d _ => mul_comm _ _
      rw [this, hAB, Matrix.one_apply]
      simp [eq_comm]
    simp only [dualTens]
    rw [e1, e1 s y d, map_sum]
    simp_rw [hI, hz, smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul, hd, map_smul]
    by_cases h : d = b <;> simp [h]
  have c3 : ∀ x, ∑ s, io' s (pr' s x) = x := by
    intro x
    funext d
    rw [Finset.sum_apply]
    simp_rw [e1, e2]
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, h1]
    exact change_inv A B hAB x d
  have c4 : ∀ s y, pr' s (io' s y) = y := by
    intro s y
    rw [e2]
    simp_rw [e1, change_inv B A hBA]
    exact h2 s y
  have c5 : ∀ s t, s ≠ t → ∀ y, pr' s (io' t y) = 0 := by
    intro s t hst y
    rw [e2]
    simp_rw [e1, change_inv B A hBA]
    exact h3 s t hst y
  refine ⟨io', pr', c1, ?_, c3, c4, c5, e1, e2⟩
  intro s a b x
  conv_lhs => rw [← c3 x]
  rw [dualTens_sum, map_sum, Finset.sum_eq_single s]
  · rw [← c1, c4]
  · intro t _ ht
    rw [← c1, c5 s t (Ne.symm ht)]
  · simp

end alg

theorem rawTens : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)) (F : ∀ s, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (RI s).smSub), (∀ s, (RI s).IsDG ε (muI s)) → TensRaw dualM R RI io pr → IsUnit Q → R.IsE Q E → (∀ s, (RI s).IsE Q (F s)) → ∃ (io' : ∀ s, (RI s).smSub →ₗ[ℂ] (Fin (2 * r + k + 1) → R.smSub)) (pr' : ∀ s, (Fin (2 * r + k + 1) → R.smSub) →ₗ[ℂ] (RI s).smSub), (∀ s a b y, io' s (F s a b y) = dualTens E a b (io' s y)) ∧ (∀ s a b x, pr' s (dualTens E a b x) = F s a b (pr' s x)) ∧ (∀ x, ∑ s, io' s (pr' s x) = x) ∧ (∀ s y, pr' s (io' s y) = y) ∧ (∀ s t, s ≠ t → ∀ y, pr' s (io' t y) = 0) ∧ (∀ s y d, ((io' s y d : R.smSub) : R.H) = ∑ c, Q⁻¹ c d • io s c (y : (RI s).H)) ∧ ∀ s x, ((pr' s x : (RI s).smSub) : (RI s).H) = ∑ c, pr s c (∑ d, Q d c • ((x d : R.smSub) : R.H)) := by
  intro hK k r ε mu R hR RI muI io pr Q E F hRI hT hQ hE hF
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  obtain ⟨io', pr', c1, c2, c3, c4, c5, e1, e2⟩ :=
    alg (N := fun s => (RI s).smSub) (fun s c => lm (hT.io_sm s c)) (fun s c => lm (hT.pr_sm s c)) Q Q⁻¹
      (Matrix.mul_nonsing_inv Q hdet) (Matrix.nonsing_inv_mul Q hdet) E F
      (by
        intro s a b y c
        apply Subtype.ext
        rw [lm_coe, hF s a b y, GlobalTheory.T.dual_tensor_capelli_intertwine hK k r ε mu R hR RI muI io pr hRI hT s _ y y.2 c,
          Submodule.coe_sub, hE a b, Submodule.coe_sum]
        rfl)
      (by
        intro x c
        apply Subtype.ext
        have := hT.sum_io_pr (fun d => (x d : R.H)) (fun d => (x d).2) c
        simpa only [Submodule.coe_sum, lm_coe] using this)
      (by
        intro s y
        apply Subtype.ext
        have := hT.pr_io s y y.2
        simpa only [Submodule.coe_sum, lm_coe] using this)
      (by
        intro s t hst y
        apply Subtype.ext
        have := hT.pr_io_ne s t hst y y.2
        simpa only [Submodule.coe_sum, lm_coe, Submodule.coe_zero] using this)
  refine ⟨io', pr', c1, c2, c3, c4, c5, ?_, ?_⟩
  · intro s y d
    rw [e1]
    simp only [Submodule.coe_sum, lm_coe, Submodule.coe_smul]
  · intro s x
    rw [e2]
    simp only [Submodule.coe_sum, lm_coe, Submodule.coe_smul]

end GlobalTheory.RawTens

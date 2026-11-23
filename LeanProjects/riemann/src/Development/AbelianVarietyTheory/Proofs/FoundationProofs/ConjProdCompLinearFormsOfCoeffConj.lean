import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaConj.ProdLin

def CjN (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (x y : ℂ) : Prop := x ∈ M ∧ y = cj M ρ x

theorem CjN.add {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {x y x' y' : ℂ} (h : CjN M ρ x x')
    (h' : CjN M ρ y y') : CjN M ρ (x + y) (x' + y') :=
  ⟨add_mem h.1 h'.1, by rw [cj_add ρ h.1 h'.1, h.2, h'.2]⟩

theorem CjN.mul {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {x y x' y' : ℂ} (h : CjN M ρ x x')
    (h' : CjN M ρ y y') : CjN M ρ (x * y) (x' * y') :=
  ⟨mul_mem h.1 h'.1, by rw [cj_mul ρ h.1 h'.1, h.2, h'.2]⟩

theorem CjN.rat (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (q : ℚ) : CjN M ρ (q : ℂ) (q : ℂ) := by
  have h : (q : ℂ) ∈ M := SubfieldClass.ratCast_mem M q
  refine ⟨h, ?_⟩
  rw [cj_mem ρ h]
  have : (⟨(q : ℂ), h⟩ : M) = (q : M) := by apply Subtype.ext; simp
  rw [this, map_ratCast]

inductive Rel {E I : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : I → E)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : (E → ℂ) → (E → ℂ) → Prop
  | const (c c' : ℂ) : CjN M ρ c c' → Rel v M ρ (fun _ => c) (fun _ => c')
  | base (g g' : ℂ → ℂ) (L L' : E →L[ℂ] ℂ) : Differentiable ℂ g → Differentiable ℂ g' →
      (∀ n, CjN M ρ (iteratedDeriv n g 0) (iteratedDeriv n g' 0)) →
      (∀ k, CjN M ρ (L (v k)) (L' (v k))) → Rel v M ρ (fun z => g (L z)) (fun z => g' (L' z))
  | add (F F' G G' : E → ℂ) : Rel v M ρ F F' → Rel v M ρ G G' →
      Rel v M ρ (fun z => F z + G z) (fun z => F' z + G' z)
  | mul (F F' G G' : E → ℂ) : Rel v M ρ F F' → Rel v M ρ G G' →
      Rel v M ρ (fun z => F z * G z) (fun z => F' z * G' z)

variable {E I : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {v : I → E}
  {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}

theorem Rel.contDiff {F F' : E → ℂ} (h : Rel v M ρ F F') :
    ContDiff ℂ ⊤ F ∧ ContDiff ℂ ⊤ F' := by
  induction h with
  | const c c' _ => exact ⟨contDiff_const, contDiff_const⟩
  | base g g' L L' hg hg' _ _ => exact ⟨hg.contDiff.comp L.contDiff, hg'.contDiff.comp L'.contDiff⟩
  | add F F' G G' _ _ h1 h2 => exact ⟨h1.1.add h2.1, h1.2.add h2.2⟩
  | mul F F' G G' _ _ h1 h2 => exact ⟨h1.1.mul h2.1, h1.2.mul h2.2⟩

theorem Rel.diff {F F' : E → ℂ} (h : Rel v M ρ F F') :
    Differentiable ℂ F ∧ Differentiable ℂ F' :=
  ⟨h.contDiff.1.differentiable (by simp), h.contDiff.2.differentiable (by simp)⟩

theorem Rel.at_zero {F F' : E → ℂ} (h : Rel v M ρ F F') : CjN M ρ (F 0) (F' 0) := by
  induction h with
  | const c c' h => exact h
  | base g g' L L' _ _ h _ => simpa using h 0
  | add F F' G G' _ _ h1 h2 => exact h1.add h2
  | mul F F' G G' _ _ h1 h2 => exact h1.mul h2

theorem fderiv_base {g : ℂ → ℂ} (hg : Differentiable ℂ g) (L : E →L[ℂ] ℂ) (w : E) :
    (fun z => fderiv ℂ (fun z => g (L z)) z w) = fun z => L w * deriv g (L z) := by
  funext z
  have := ((hg (L z)).hasDerivAt.comp_hasFDerivAt z L.hasFDerivAt).fderiv
  change fderiv ℂ (g ∘ L) z w = _
  rw [this]; simp [mul_comm]

theorem fderiv_add' {F G : E → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (w : E) :
    (fun z => fderiv ℂ (fun z => F z + G z) z w) = fun z => fderiv ℂ F z w + fderiv ℂ G z w := by
  funext z
  rw [fderiv_fun_add (hF z) (hG z)]; simp

theorem fderiv_mul' {F G : E → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (w : E) :
    (fun z => fderiv ℂ (fun z => F z * G z) z w) =
      fun z => F z * fderiv ℂ G z w + G z * fderiv ℂ F z w := by
  funext z
  rw [fderiv_fun_mul (hF z) (hG z)]; simp

theorem Rel.fderiv {F F' : E → ℂ} (h : Rel v M ρ F F') (k : I) :
    Rel v M ρ (fun z => fderiv ℂ F z (v k)) (fun z => fderiv ℂ F' z (v k)) := by
  induction h with
  | const c c' h =>
    have := Rel.const (v := v) _ _ (CjN.rat M ρ 0)
    simpa using this
  | base g g' L L' hg hg' h hL =>
    rw [fderiv_base hg, fderiv_base hg']
    refine Rel.mul _ _ _ _ (Rel.const _ _ (hL k))
      (Rel.base (deriv g) (deriv g') L L' hg.deriv hg'.deriv (fun n => ?_) hL)
    rw [← iteratedDeriv_succ', ← iteratedDeriv_succ']
    exact h (n + 1)
  | add F F' G G' hF hG h1 h2 =>
    rw [fderiv_add' hF.diff.1 hG.diff.1, fderiv_add' hF.diff.2 hG.diff.2]
    exact Rel.add _ _ _ _ h1 h2
  | mul F F' G G' hF hG h1 h2 =>
    rw [fderiv_mul' hF.diff.1 hG.diff.1, fderiv_mul' hF.diff.2 hG.diff.2]
    exact Rel.add _ _ _ _ (Rel.mul _ _ _ _ hF h2) (Rel.mul _ _ _ _ hG h1)

theorem iteratedFDeriv_step {F : E → ℂ} (hF : ContDiff ℂ ⊤ F) (n : ℕ) (m : Fin (n + 1) → E) :
    iteratedFDeriv ℂ (n + 1) F 0 m =
      iteratedFDeriv ℂ n (fun z => fderiv ℂ F z (m (Fin.last n))) 0 (Fin.init m) := by
  rw [iteratedFDeriv_succ_apply_right,
    iteratedFDeriv_clm_apply_const_apply (n := ⊤) (hF.fderiv_right (m := ⊤) le_top) le_top]

theorem Rel.iterated (n : ℕ) : ∀ {F F' : E → ℂ}, Rel v M ρ F F' → ∀ k : Fin n → I,
    CjN M ρ (iteratedFDeriv ℂ n F 0 fun i => v (k i)) (iteratedFDeriv ℂ n F' 0 fun i => v (k i)) := by
  induction n with
  | zero => intro F F' h k; simpa using h.at_zero
  | succ n ih =>
    intro F F' h k
    rw [iteratedFDeriv_step h.contDiff.1, iteratedFDeriv_step h.contDiff.2]
    exact ih (h.fderiv (k (Fin.last n))) (Fin.init k)

theorem Rel.prod {ι : Type} (s : Finset ι) {F F' : ι → E → ℂ} (h : ∀ i, Rel v M ρ (F i) (F' i)) :
    Rel v M ρ (fun z => ∏ i ∈ s, F i z) (fun z => ∏ i ∈ s, F' i z) := by
  induction s using Finset.induction_on with
  | empty =>
    have := Rel.const (v := v) _ _ (CjN.rat M ρ 1)
    simpa using this
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact Rel.mul _ _ _ _ (h i) ih

theorem Rel.cjF {D : D7} {N N' : ℕ} {F F' : VC D N N' → ℂ} (h : Rel (coordV D) M ρ F F') :
    CjF D M ρ F F' := by
  refine ⟨h.diff.1, h.diff.2, fun α => ?_⟩
  have h1 := (Rel.iterated _ h (fun i : Fin (Multiset.card α.toMultiset) =>
    α.toMultiset.toList.get ⟨i, by rw [Multiset.length_toList]; exact i.2⟩)).mul
      (CjN.rat M ρ (α.prod fun _ n => (n.factorial : ℚ))⁻¹)
  have h2 : (((α.prod fun _ n => (n.factorial : ℚ))⁻¹ : ℚ) : ℂ) =
      (α.prod fun _ n => (n.factorial : ℂ))⁻¹ := by
    simp [Finsupp.prod]
  rw [h2] at h1
  unfold taylor
  simp only [div_eq_mul_inv]
  exact h1

def linF (D : D7) {N N' : ℕ} (l : VC D N N') : VC D N N' →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => ∑ τ, ∑ a, ∑ c, z τ a c * l τ a c
      map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.mul_sum, mul_assoc] }

theorem linF_apply (D : D7) {N N' : ℕ} (l z : VC D N N') :
    linF D l z = ∑ τ, ∑ a, ∑ c, z τ a c * l τ a c := rfl

theorem linF_coordV (D : D7) {N N' : ℕ} (l : VC D N N') (k : D.what₂.Tau × Fin N' × Fin N) :
    linF D l (coordV D k) = l k.1 k.2.1 k.2.2 := by
  rw [linF_apply]
  simp [coordV, ite_and]

theorem cjF_prod : ∀ (D : D7) (N N' r : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (g g' : Fin r → ℂ → ℂ) (l l' : Fin r → VC D N N'), (∀ j, Differentiable ℂ (g j)) →
    (∀ j, Differentiable ℂ (g' j)) →
    (∀ j n, coef1 (g j) n ∈ M ∧ coef1 (g' j) n = cj M ρ (coef1 (g j) n)) →
    (∀ j τ a c, l j τ a c ∈ M ∧ l' j τ a c = cj M ρ (l j τ a c)) →
    CjF D M ρ (fun z : VC D N N' => ∏ j, g j (∑ τ, ∑ a, ∑ c, z τ a c * l j τ a c))
      (fun z : VC D N N' => ∏ j, g' j (∑ τ, ∑ a, ∑ c, z τ a c * l' j τ a c)) := by
  intro D N N' r M ρ g g' l l' hg hg' hc hl
  refine Rel.cjF (Rel.prod Finset.univ fun j =>
    Rel.base (g j) (g' j) (linF D (l j)) (linF D (l' j)) (hg j) (hg' j) (fun n => ?_) fun k => ?_)
  · have h1 := CjN.mul (hc j n) (CjN.rat M ρ (n.factorial : ℚ))
    have h0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    simpa only [coef1, Rat.cast_natCast, div_mul_cancel₀ _ h0] using h1
  · rw [linF_coordV, linF_coordV]; exact hl j _ _ _

end GlobalTheory.ThetaConj.ProdLin

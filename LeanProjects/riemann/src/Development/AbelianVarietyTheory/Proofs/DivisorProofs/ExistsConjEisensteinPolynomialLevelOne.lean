import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDeltaQExpansionIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModularFormLevelOneOfInvariantQExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionsCoeffwiseConjugateRingClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularFormPolynomialE4E6

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in
private theorem exists_eisensteinCombination_of_isModularForm {w : ℕ} {F : ℍ → ℂ}
    (hF : _root_.ReciprocityTheory.ChartRestriction.L1.IsMF (w : ℤ) F) :
    ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ), (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧
      ∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  obtain ⟨f, hf⟩ := hF
  have hmem := _root_.ReciprocityTheory.PGsh.coe_mem_monoSpanF w f
  unfold _root_.ReciprocityTheory.PGsh.monoSpanF at hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  classical
  refine ⟨(_root_.ReciprocityTheory.PGsh.monoIdx w).image fun a => (a, _root_.ReciprocityTheory.PGsh.monoB w a),
    fun p => if hp : p.1 ∈ _root_.ReciprocityTheory.PGsh.monoIdx w then c ⟨p.1, hp⟩ else 0, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hp
    exact _root_.ReciprocityTheory.PGsh.monoIdx_wt ha
  · intro τ
    rw [Finset.sum_image (fun x _ y _ h => congrArg Prod.fst h), ← hf τ, ← hc]
    rw [Finset.sum_apply, ← Finset.sum_attach (_root_.ReciprocityTheory.PGsh.monoIdx w)]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, a.2, dif_pos]
    rw [_root_.ReciprocityTheory.PGsh.coe_monoW a.2]
    rfl

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in
private theorem qConj_eisensteinCombination (g : ℂ ≃+* ℂ) {N : ℕ}
    (hN : 0 < N) {ι : Type} (s : Finset ι) (c : ι → ℂ) (u v : ι → ℕ) :
    _root_.GlobalTheory.QFam.QConj g N (fun τ => ∑ i ∈ s, c i * (E₄ τ ^ u i * E₆ τ ^ v i))
      (fun τ => ∑ i ∈ s, g (c i) * (E₄ τ ^ u i * E₆ τ ^ v i)) := by
  refine _root_.GlobalTheory.QFam.QConj.sum s fun i _ => ?_
  have h₄ := _root_.GlobalTheory.QFam.eis_qConj N hN _ (Or.inl rfl) g
  have h₆ := _root_.GlobalTheory.QFam.eis_qConj N hN _ (Or.inr (Or.inl rfl)) g
  exact (_root_.GlobalTheory.QFam.QConj.const g N (c i)).mul hN
    ((h₄.pow hN (u i)).mul hN (h₆.pow hN (v i)))

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in

theorem _root_.GlobalTheory.QFam.levelPoly_conj : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F F' : ℍ → ℂ),
    0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → _root_.GlobalTheory.QFam.QConj g N F F' →
    ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ), (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧
      (∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) ∧
      ∀ τ, F' τ = ∑ p ∈ s, g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  intro g w N F F' hN hinv hconj
  obtain ⟨a, ha, ha'⟩ := hconj
  obtain ⟨s, c, hw, hF⟩ := exists_eisensteinCombination_of_isModularForm
    (_root_.GlobalTheory.QFam.isMF_of_invariant_of_hasQ N w F a hN hinv ha)
  refine ⟨s, c, hw, hF, ?_⟩
  obtain ⟨b, hb, hb'⟩ :=
    qConj_eisensteinCombination g hN s c Prod.fst Prod.snd
  have hFeq : F = fun τ => ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := funext hF
  rw [← hFeq] at hb
  have hab : a = b := ha.coeff_unique hN hb
  subst hab
  intro τ
  exact congrFun (ha'.fun_unique hb') τ

end GlobalTheory.QFam

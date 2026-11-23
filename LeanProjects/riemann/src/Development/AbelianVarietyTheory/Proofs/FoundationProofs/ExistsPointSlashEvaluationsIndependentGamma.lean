import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.CosetEval

def mfMonoid (Γ : Subgroup SL(2, ℤ)) : Submonoid (Multiplicative ℤ × (ℍ → ℂ)) where
  carrier := {p | IsMF Γ (Multiplicative.toAdd p.1) p.2}
  mul_mem' := by
    rintro ⟨a, f⟩ ⟨b, g⟩ ha hb
    exact IsMF.mul ha hb (by simp)
  one_mem' := IsMF.one Γ

def evHom (Γ : Subgroup SL(2, ℤ)) (x : SL(2, ℤ)) (τ : ℍ) : mfMonoid Γ →* ℂ where
  toFun p := (p.1.2 ∣[Multiplicative.toAdd p.1.1] x) τ
  map_one' := by
    show ((1 : ℍ → ℂ) ∣[Multiplicative.toAdd (1 : Multiplicative ℤ)] x) τ = 1
    rw [toAdd_one, ModularForm.is_invariant_one]; rfl
  map_mul' p q := by
    show ((p.1.2 * q.1.2) ∣[Multiplicative.toAdd (p.1.1 * q.1.1)] x) τ = _
    rw [toAdd_mul, ModularForm.mul_slash_SL2]; rfl

@[simp] theorem evHom_apply (Γ : Subgroup SL(2, ℤ)) (x : SL(2, ℤ)) (τ : ℍ) (p : mfMonoid Γ) :
    evHom Γ x τ p = (p.1.2 ∣[Multiplicative.toAdd p.1.1] x) τ := rfl

open UpperHalfPlane Filter in
open ModularForm (E₄ E₆) in
open scoped MatrixGroups ModularForm Manifold Topology in
private lemma dense_setOf_ne_zero_of_mdifferentiable_of_ne_zero {D : ℍ → ℂ} (hD : MDiff D) (hD0 : D ≠ 0) :
    Dense {τ | D τ ≠ 0} := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨τ, hτ⟩
  by_contra hempty
  have hzero : ∀ σ ∈ U, D σ = 0 := fun σ hσ => by_contra fun h => hempty ⟨σ, hσ, h⟩
  have hS : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have han : AnalyticOnNhd ℂ (D ∘ ofComplex) {w : ℂ | 0 < w.im} :=
    (UpperHalfPlane.mdifferentiable_iff.1 hD).analyticOnNhd hS
  have hev : D ∘ ofComplex =ᶠ[𝓝 (τ : ℂ)] 0 := by
    have hUc : IsOpen (((↑) : ℍ → ℂ) '' U) := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap U hU
    filter_upwards [hUc.mem_nhds ⟨τ, hτ, rfl⟩] with w hw
    obtain ⟨σ, hσ, rfl⟩ := hw
    simp [hzero σ hσ]
  have hall := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ.im_pos hev
  apply hD0
  funext σ
  simpa using hall σ.im_pos

open UpperHalfPlane Filter in
open ModularForm (E₄ E₆) in
open scoped MatrixGroups ModularForm Manifold Topology in

theorem _root_.GlobalTheory.CosetEval.evals_independent : ∀ M : ℕ, 0 < M → (∀ x : SL(2, ℤ), x ∉ CongruenceSubgroup.Gamma M → ∃ (k : ℤ) (f : ℍ → ℂ), _root_.GlobalTheory.OddFrame.IsMF (CongruenceSubgroup.Gamma M) k f ∧ f ∣[k] x ≠ f) → ∃ τ₀ : ℍ, ∀ (ι : Type) [Fintype ι] (x : ι → SL(2, ℤ)) (c : ι → ℂ), (∀ i j, x i * (x j)⁻¹ ∈ CongruenceSubgroup.Gamma M → i = j) → (∀ (k : ℤ) (f : ℍ → ℂ), _root_.GlobalTheory.OddFrame.IsMF (CongruenceSubgroup.Gamma M) k f → ∑ i, c i * (f ∣[k] x i) τ₀ = 0) → c = 0 := by
  intro M _ hsep
  classical
  have hsep' : ∀ p : SL(2, ℤ) × SL(2, ℤ), ∃ (k : ℤ) (f : ℍ → ℂ),
      _root_.GlobalTheory.OddFrame.IsMF (CongruenceSubgroup.Gamma M) k f ∧
      (p.1 * p.2⁻¹ ∉ CongruenceSubgroup.Gamma M → f ∣[k] p.1 ≠ f ∣[k] p.2) := by
    intro p
    by_cases hp : p.1 * p.2⁻¹ ∈ CongruenceSubgroup.Gamma M
    · exact ⟨0, 0, _root_.GlobalTheory.OddFrame.IsMF.zero _ _, fun h => absurd hp h⟩
    · obtain ⟨k, f, hf, hne⟩ := hsep _ hp
      refine ⟨k, f, hf, fun _ heq => hne ?_⟩
      have := congrArg (fun g => g ∣[k] p.2⁻¹) heq

      rwa [← SlashAction.slash_mul, ← SlashAction.slash_mul, mul_inv_cancel,
        SlashAction.slash_one] at this
  choose k f hf hne using hsep'
  set O : SL(2, ℤ) × SL(2, ℤ) → Set ℍ := fun p =>
    {_τ | p.1 * p.2⁻¹ ∈ CongruenceSubgroup.Gamma M} ∪
      {τ | (f p ∣[k p] p.1) τ ≠ (f p ∣[k p] p.2) τ} with hO
  have hcont : ∀ p (y : SL(2, ℤ)), Continuous (f p ∣[k p] y) := fun p y =>
    (_root_.GlobalTheory.OddFrame.mdiff_slash (hf p).2.1 _ y).continuous
  have hOopen : ∀ p, IsOpen (O p) := fun p =>
    isOpen_const.union (isOpen_ne_fun (hcont p p.1) (hcont p p.2))
  have hOdense : ∀ p, Dense (O p) := by
    intro p
    by_cases hp : p.1 * p.2⁻¹ ∈ CongruenceSubgroup.Gamma M
    · exact dense_univ.mono fun τ _ => Or.inl hp
    · have hD : MDiff (f p ∣[k p] p.1 - f p ∣[k p] p.2) :=
        (_root_.GlobalTheory.OddFrame.mdiff_slash (hf p).2.1 _ _).sub (_root_.GlobalTheory.OddFrame.mdiff_slash (hf p).2.1 _ _)
      refine (dense_setOf_ne_zero_of_mdifferentiable_of_ne_zero hD
        (fun h0 => hne p hp (sub_eq_zero.1 h0))).mono fun τ hτ => Or.inr ?_
      exact sub_ne_zero.1 hτ
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) := Subtype.countable
  obtain ⟨τ₀, hτ₀⟩ := (dense_iInter_of_isOpen hOopen hOdense).nonempty
  refine ⟨τ₀, fun ι _ x c hx hc => ?_⟩
  let χ : ι → (_root_.GlobalTheory.CosetEval.mfMonoid (CongruenceSubgroup.Gamma M) →* ℂ) :=
    fun i => _root_.GlobalTheory.CosetEval.evHom (CongruenceSubgroup.Gamma M) (x i) τ₀
  have hinj : Function.Injective χ := by
    intro i j hij
    by_contra hij'
    have hnot : x i * (x j)⁻¹ ∉ CongruenceSubgroup.Gamma M := fun h => hij' (hx i j h)
    rcases Set.mem_iInter.1 hτ₀ (x i, x j) with h | h
    · exact hnot h
    · exact h (DFunLike.congr_fun hij
        ⟨(Multiplicative.ofAdd (k (x i, x j)), f (x i, x j)), hf (x i, x j)⟩)
  have hli := (linearIndependent_monoidHom (_root_.GlobalTheory.CosetEval.mfMonoid (CongruenceSubgroup.Gamma M)) ℂ).comp χ hinj
  funext i
  refine Fintype.linearIndependent_iff.1 hli c ?_ i
  funext p
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, Pi.zero_apply]
  exact hc _ _ p.2

end GlobalTheory.CosetEval

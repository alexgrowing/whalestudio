import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open scoped TensorProduct
open MvPolynomial

noncomputable section

namespace GlobalTheory.CompanionTheory.DSCover

open Formalism.REAL (GlRel)
open CompanionTheory.D.DSIC

theorem glRel_add {A : Type} [Ring A] {n : ℕ} {E F : Fin n → Fin n → A} (hE : GlRel E) (hF : GlRel F)
    (h : ∀ a b c d, E a b * F c d = F c d * E a b) : GlRel fun a b => E a b + F a b := by
  intro a b c d
  have h1 := hE a b c d
  have h2 := hF a b c d
  have h3 := h a b c d
  have h4 := h c d a b
  have e : (E a b + F a b) * (E c d + F c d) - (E c d + F c d) * (E a b + F a b) =
      (E a b * E c d - E c d * E a b) + (F a b * F c d - F c d * F a b) := by
    simp only [add_mul, mul_add, h3, h4]
    abel
  beta_reduce
  rw [e, h1, h2]
  split_ifs <;> abel

theorem glRel_map {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {n : ℕ} {E : Fin n → Fin n → A} (hE : GlRel E) :
    GlRel fun a b => φ (E a b) := by
  intro a b c d
  have h := congrArg φ (hE a b c d)
  simp only [map_sub, map_mul] at h
  rw [h]
  split_ifs <;> simp

section Pol

variable {σ : Type}

def pd (i : σ) : Module.End ℂ (MvPolynomial σ ℂ) := (pderiv i : Derivation ℂ (MvPolynomial σ ℂ) _).toLinearMap

theorem pd_apply (i : σ) (f : MvPolynomial σ ℂ) : pd i f = pderiv i f := rfl

theorem pd_comm (i j : σ) : pd i * pd j = pd j * pd i := by
  classical
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply, pd_apply]
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul, pderiv_X, hp]
    by_cases h1 : i = k <;> by_cases h2 : j = k <;> simp [h1, h2, add_comm]

theorem word_monomial (l : List σ) : ∀ (s : σ →₀ ℕ) (c : ℂ), s.degree < l.length →
    (l.map pd).prod (monomial s c) = 0 := by
  induction l using List.reverseRecOn with
  | nil => intro s c h; simp at h
  | append_singleton l i ih =>
    intro s c h
    rw [List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply, pd_apply,
      pderiv_monomial]
    by_cases hs : s i = 0
    · simp [hs]
    · apply ih
      have e : s = (s - Finsupp.single i 1) + Finsupp.single i 1 := by
        rw [tsub_add_cancel_of_le]
        rw [Finsupp.single_le_iff]
        omega
      have e2 := congrArg Finsupp.degree e
      rw [map_add, Finsupp.degree_single] at e2
      simp only [List.length_append, List.length_singleton] at h
      omega

theorem word_pol (f : MvPolynomial σ ℂ) : ∃ m : ℕ, ∀ l : List σ, m ≤ l.length → (l.map pd).prod f = 0 := by
  induction f using MvPolynomial.induction_on' with
  | monomial s c => exact ⟨s.degree + 1, fun l hl => word_monomial l s c (by omega)⟩
  | add p q hp hq =>
    obtain ⟨m, hm⟩ := hp
    obtain ⟨k, hk⟩ := hq
    exact ⟨max m k, fun l hl => by
      rw [map_add, hm l (le_trans (le_max_left _ _) hl), hk l (le_trans (le_max_right _ _) hl), add_zero]⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem word_tmul (l : List σ) (v : V) (f : MvPolynomial σ ℂ) :
    (l.map fun i => ((pd i).lTensor V : Module.End ℂ (V ⊗[ℂ] MvPolynomial σ ℂ))).prod (v ⊗ₜ f) =
      v ⊗ₜ (l.map pd).prod f := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, LinearMap.lTensor_tmul]

theorem word_tens (z : V ⊗[ℂ] MvPolynomial σ ℂ) : ∃ m : ℕ, ∀ l : List σ, m ≤ l.length →
    (l.map fun i => ((pd i).lTensor V : Module.End ℂ (V ⊗[ℂ] MvPolynomial σ ℂ))).prod z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, fun l _ => map_zero _⟩
  | tmul v f =>
    obtain ⟨m, hm⟩ := word_pol f
    exact ⟨m, fun l hl => by rw [word_tmul, hm l hl, TensorProduct.tmul_zero]⟩
  | add p q hp hq =>
    obtain ⟨m, hm⟩ := hp
    obtain ⟨k, hk⟩ := hq
    exact ⟨max m k, fun l hl => by
      rw [map_add, hm l (le_trans (le_max_left _ _) hl), hk l (le_trans (le_max_right _ _) hl), add_zero]⟩

end Pol

theorem cover : Koszul → Verma → Cover := by
  intro hK hV n ε V _ _ E hE
  classical
  obtain ⟨M, hM, hX, h0⟩ := hV n ε
  let P := MvPolynomial (NC ε) ℂ
  let EY : Fin n → Fin n → Module.End ℂ (V ⊗[ℂ] P) := fun a b => (E a b).rTensor P + (M a b).lTensor V
  have hEY : GlRel EY := by
    refine glRel_add (E := fun a b => ((E a b).rTensor P : Module.End ℂ (V ⊗[ℂ] P)))
      (F := fun a b => ((M a b).lTensor V : Module.End ℂ (V ⊗[ℂ] P))) ?_ ?_ ?_
    · exact glRel_map (Module.End.rTensorAlgHom ℂ V P).toRingHom hE
    · exact glRel_map (Module.End.lTensorAlgHom ℂ P V).toRingHom hM
    · intro a b c d
      apply TensorProduct.ext'
      intro v f
      simp [Module.End.mul_apply]
  let cc : P →ₗ[ℂ] ℂ := (MvPolynomial.lcoeff ℂ (0 : NC ε →₀ ℕ))
  have hcc : ∀ f : P, cc f = constantCoeff f := fun f => rfl
  refine ⟨V ⊗[ℂ] P, inferInstance, inferInstance, EY, (TensorProduct.rid ℂ V).toLinearMap ∘ₗ cc.lTensor V,
    hEY, ?_, ?_, ?_⟩
  · intro v
    exact ⟨v ⊗ₜ 1, by simp [hcc]⟩
  · intro a b y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v f => simp [EY, hcc, h0]
    | add p q hp hq => simp only [map_add, hp, hq]
  · refine hK n ε (V ⊗[ℂ] P) (fun i => EY i.1.1 i.1.2) (fun i => (pd i).lTensor V) ?_ ?_ ?_ ?_
    · intro i j
      have h := hEY i.1.1 i.1.2 j.1.1 j.1.2
      have h1 : i.1.2 ≠ j.1.1 := fun e => by
        have := i.2.2; rw [e, j.2.1] at this; exact Bool.noConfusion this
      have h2 : j.1.2 ≠ i.1.1 := fun e => by
        have := j.2.2; rw [e, i.2.1] at this; exact Bool.noConfusion this
      rw [if_neg h1, if_neg h2, sub_zero, sub_eq_zero] at h
      exact h
    · intro i j
      apply TensorProduct.ext'
      intro v f
      have := congrArg (fun T : Module.End ℂ P => T f) (pd_comm i j)
      simp only [Module.End.mul_apply] at this
      simp only [Module.End.mul_apply, LinearMap.lTensor_tmul, this]
    · intro i j
      apply TensorProduct.ext'
      intro v f
      simp only [EY, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.lTensor_tmul,
        LinearMap.rTensor_tmul, map_add, hX, pd_apply, Derivation.leibniz, pderiv_X, smul_eq_mul,
        TensorProduct.tmul_add]
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    · intro z
      obtain ⟨m, hm⟩ := word_tens z
      exact ⟨m, fun l hl => hm l hl.ge⟩

end GlobalTheory.CompanionTheory.DSCover

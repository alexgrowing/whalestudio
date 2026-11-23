import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}
  (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)

theorem fock_hx_add_left (z z' w : Fin g → ℂ) :
    hx X bas idx x (z + z') w = hx X bas idx x z w + hx X bas idx x z' w := by
  simp only [hx, mulVec_add, add_dotProduct]

theorem fock_hx_add_right (z w w' : Fin g → ℂ) :
    hx X bas idx x z (w + w') = hx X bas idx x z w + hx X bas idx x z w' := by
  simp only [hx, mulVec_add, star_add, dotProduct_add]

theorem fock_hx_smul_left (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x (c • z) w = c * hx X bas idx x z w := by
  simp only [hx, mulVec_smul, smul_dotProduct, smul_eq_mul]

theorem fock_hx_smul_right (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x z (c • w) = conj c * hx X bas idx x z w := by
  simp only [hx, mulVec_smul, star_smul, dotProduct_smul, smul_eq_mul]
  rfl

theorem fock_hx_zero_right (z : Fin g → ℂ) : hx X bas idx x z 0 = 0 := by
  simp [hx]

theorem fock_hx_differentiable (w : Fin g → ℂ) : Differentiable ℂ fun z => hx X bas idx x z w := by
  simp only [hx, dotProduct, mulVec]
  fun_prop

theorem fock_hx_conj (hs : IsSympl X bas) (hd : x ∈ X.dom) (z w : Fin g → ℂ) :
    hx X bas idx x w z = conj (hx X bas idx x z w) := by
  have h := imInv_isSymm idx hs hd
  have hr : ∀ i j, conj (imInv X bas idx x i j) = imInv X bas idx x j i := by
    intro i j
    rw [h.apply i j]
    simp [ThFr.imInv]
  simp only [hx]
  generalize hMat X bas idx x *ᵥ z = u
  generalize hMat X bas idx x *ᵥ w = v
  simp only [dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply, hr, RCLike.star_def,
    conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end

theorem fock_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, ∀ (k : ℕ) (θ : (Fin g → ℂ) → ℂ), (∀ a b, fock X bas idx x k a (fock X bas idx x k b θ) = cexp (-((k : ℂ) * Real.pi * I * ((hx X bas idx x a b).im : ℂ))) • fock X bas idx x k (a + b) θ) ∧ fock X bas idx x k 0 θ = θ ∧ (∀ (N : ℕ) a, fock X bas idx x (N ^ 2) a (fun z => θ ((N : ℂ) • z)) = fun z => fock X bas idx x 1 ((N : ℂ) • a) θ ((N : ℂ) • z)) ∧ (Differentiable ℂ θ → ∀ a, Differentiable ℂ (fock X bas idx x k a θ)) ∧ ∀ (th : Fin n → (Fin g → ℂ) → ℂ) (κ : ℂ) (φ : TF n g), IsSB φ → (∀ z : Fin n → Fin g → ℂ, ∏ b, th b (z b) = κ * thA X bas idx φ x z) → ∀ (y : Matrix (Fin n) (Fin r) E) (z : Fin n → Fin g → ℂ), ∏ b, fock X bas idx x 1 (pv X idx x (y b)) (th b) (z b) = κ * thA X bas idx (heisG X bas y φ) x z := by
  intro E _ _ _ r X g bas idx n hs hn x hd k θ
  refine ⟨fun a b => ?_, ?_, fun N a => ?_, fun hθ a => ?_, fun th κ φ hφ h y z => ?_⟩
  · funext z
    simp only [fock, Pi.smul_apply, smul_eq_mul]
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    rw [add_assoc z a b]
    congr 2
    simp only [fock_hx_add_left, fock_hx_add_right, fock_hx_smul_left, smul_add]
    rw [fock_hx_conj X bas idx x hs hd a b]
    have := Complex.sub_conj (hx X bas idx x a b)
    push_cast at this
    linear_combination (-(k : ℂ) * Real.pi / 2) * this
  · funext z
    simp [fock, fock_hx_zero_right]
  · funext z
    simp only [fock, smul_add]
    congr 2
    simp only [fock_hx_add_left, fock_hx_smul_left, fock_hx_smul_right, map_natCast]
    push_cast
    ring
  · have h1 := fock_hx_differentiable X bas idx x a
    unfold fock
    refine Differentiable.mul (Differentiable.cexp (Differentiable.neg (Differentiable.const_mul ?_ _))) ?_
    · exact h1.comp (differentiable_id.add_const _)
    · exact hθ.comp (differentiable_id.add_const _)
  · rw [((heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ).2.2.2.2 x hd z]
    simp only [fock, Finset.prod_mul_distrib]
    rw [h fun b => z b + pv X idx x (y b), ← Complex.exp_sum, mul_left_comm]
    congr 2
    simp only [hx, pv, Finset.mul_sum, Finset.sum_neg_distrib, Nat.cast_one, _root_.one_mul]

end GlobalTheory.Dict

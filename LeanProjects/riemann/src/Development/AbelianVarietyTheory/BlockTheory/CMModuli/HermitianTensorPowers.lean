import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

def herm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : ℂ := z ⬝ᵥ Hm.mulVec (star w)

def factor {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (l z : Fin g → ℂ) : ℂ :=
  c * Complex.exp (Real.pi * herm Hm z l + Real.pi / 2 * herm Hm l l)

def IsThetaFn {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (n : ℕ)
    (θ : (Fin g → ℂ) → ℂ) : Prop :=
  Differentiable ℂ θ ∧ ∀ (l : Λ) (z : Fin g → ℂ), θ (z + l) = factor Hm (χ l) l z ^ n * θ z

abbrev tpow {X : Scheme.{0}} (L : LB X) (n : ℕ) : LB X :=
  LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (n : ℤ))

def IsFnPow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (n : ℕ)
    (s : (tpow L n).Sec) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (j : (tpow L n).ι) (z : Fin g → ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ (tpow L n).U j →
    valAt' (u.ex z).left ((tpow L n).U j) (s.f j) = θ z * u.fr (j PUnit.unit) z ^ n

def commVal {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (k : ℕ) (v w : Fin g → ℂ) : ℂˣ :=
  Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I * (k * ((herm Hm v w).im : ℂ))))) (Complex.exp_ne_zero _)

def ThetaUniformisation : Prop :=
  ∀ (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen →
    ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ),

      u.IsAH Hm χ ∧ u.IsRig rig ∧

      (∀ l, χ l = 1 ∨ χ l = -1) ∧
      (∀ l m : u.Λ, χ (l + m) = χ l * χ m * Complex.exp (Real.pi * Complex.I * ((herm Hm l m).im : ℂ))) ∧

      (∀ v : epsR ℂ ⟶ P.A, IsTangent v → ∃! w : Fin P.g → ℂ, u.IsDiff w v) ∧
      (∀ w : Fin P.g → ℂ, ∃! v : epsR ℂ ⟶ P.A, IsTangent v ∧ u.IsDiff w v) ∧

      (∀ f : P.A ⟶ P.A, IsMonHom f → ∃ M : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ),
        (∀ l ∈ u.Λ, M l ∈ u.Λ) ∧ ∀ z, u.ex (M z) = u.ex z ≫ f) ∧

      (∀ n : ℕ,
        (∀ s : (tpow P.L n).Sec, ∃! θ, IsThetaFn u.Λ Hm χ n θ ∧ IsFnPow u n s θ) ∧
        (∀ θ, IsThetaFn u.Λ Hm χ n θ → ∃! s : (tpow P.L n).Sec, IsFnPow u n s θ)) ∧

      (∀ l m : u.Λ, ∃ a : ℤ, (herm Hm l m).im = a) ∧
      (∀ φ : u.Λ →ₗ[ℤ] ℤ, ∃! l : u.Λ, ∀ m : u.Λ, (herm Hm l m).im = φ m) ∧

      (∀ k : ℕ, 0 < k → ∀ v w : Fin P.g → ℂ, k • v ∈ u.Λ → k • w ∈ u.Λ →
        Out.WeilIs P.A P.L (k : ℤ) (u.ex v) (u.ex w) (unitOn (commVal Hm k v w)))

lemma herm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    herm Hm (z + z') w = herm Hm z w + herm Hm z' w := add_dotProduct _ _ _

lemma herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (v w : Fin g → ℂ) :
    herm Hm w v = starRingEnd ℂ (herm Hm v w) := by
  simp only [herm, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul, Pi.star_apply,
    RCLike.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have : starRingEnd ℂ (Hm a b) = Hm b a := h.apply b a
  rw [this]; ring

def shift {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (k : ℕ) (v : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ) :
    (Fin g → ℂ) → ℂ := fun z => Complex.exp (-(k * Real.pi * herm Hm z v)) * θ (z + v)

lemma shift_comm {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (k : ℕ) (v w : Fin g → ℂ)
    (θ : (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) :
    shift Hm k v (shift Hm k w θ) z = commVal Hm k v w * shift Hm k w (shift Hm k v θ) z := by
  have h1 : herm Hm v w - herm Hm w v = 2 * ((herm Hm v w).im : ℂ) * Complex.I := by
    rw [herm_swap h v w, Complex.sub_conj]; push_cast; ring
  simp only [shift, commVal, Units.val_mk0, herm_add_left]
  rw [add_right_comm z w v, ← _root_.mul_assoc (Complex.exp _) (Complex.exp _) (θ _), ← _root_.mul_assoc (Complex.exp _) (Complex.exp _) (θ _),
    ← _root_.mul_assoc (Complex.exp _) _ (θ _), ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  refine congrArg (fun t => Complex.exp t * θ (z + v + w)) ?_
  linear_combination (-(k : ℂ) * Real.pi) * h1

lemma shift_factor {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (k : ℕ) (c : ℂ)
    (v l : Fin g → ℂ) (a : ℤ) (ha : k * (herm Hm v l).im = a) (θ : (Fin g → ℂ) → ℂ)
    (hθ : ∀ z, θ (z + l) = factor Hm c l z ^ k * θ z) (z : Fin g → ℂ) :
    shift Hm k v θ (z + l) = factor Hm c l z ^ k * shift Hm k v θ z := by
  have h1 : herm Hm v l - herm Hm l v = 2 * ((herm Hm v l).im : ℂ) * Complex.I := by
    rw [herm_swap h v l, Complex.sub_conj]; push_cast; ring
  have ha' : (k : ℂ) * ((herm Hm v l).im : ℂ) = a := by exact_mod_cast ha
  have h2 : Complex.exp (a * (2 * Real.pi * Complex.I)) = 1 := Complex.exp_int_mul_two_pi_mul_I a
  simp only [shift, factor, add_right_comm z l v, hθ, herm_add_left, mul_pow, ← Complex.exp_nat_mul]
  have h3 : Complex.exp (-(k * Real.pi * (herm Hm z v + herm Hm l v))) *
      Complex.exp (k * (Real.pi * (herm Hm z l + herm Hm v l) + Real.pi / 2 * herm Hm l l)) =
      Complex.exp (k * (Real.pi * herm Hm z l + Real.pi / 2 * herm Hm l l)) *
      Complex.exp (-(k * Real.pi * herm Hm z v)) := by
    rw [← mul_one (Complex.exp _ * Complex.exp (-(k * Real.pi * herm Hm z v))), ← h2]
    simp only [← Complex.exp_add]
    congr 1
    linear_combination ((k : ℂ) * Real.pi) * h1 + (2 * Real.pi * Complex.I) * ha'
  linear_combination (c ^ k * θ (z + v)) * h3

end GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers

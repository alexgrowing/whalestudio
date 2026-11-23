import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RTensorPairingEqZeroOfFlipInjectiveStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon.StPairing

section

variable {F : Type} [Field F] {B : Type} [CommRing B] [Algebra F B]
  {V V' : Type} [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V']

def tensorPairing (m : V →ₗ[F] V' →ₗ[F] F) : V ⊗[F] B →ₗ[F] V' ⊗[F] B →ₗ[F] B :=
  (TensorProduct.map₂ m (LinearMap.mul F B)).compr₂ (TensorProduct.lid F B).toLinearMap

@[simp] theorem tensorPairing_tmul (m : V →ₗ[F] V' →ₗ[F] F) (v : V) (a : B) (v' : V') (b : B) :
    tensorPairing m (v ⊗ₜ[F] a) (v' ⊗ₜ[F] b) = m v v' • (a * b) := by
  simp [tensorPairing, TensorProduct.map₂_apply_tmul]

theorem tensorPairing_one (m : V →ₗ[F] V' →ₗ[F] F) (v : V) (y : V' ⊗[F] B) :
    tensorPairing m (v ⊗ₜ[F] (1 : B)) y = TensorProduct.lid F B (LinearMap.rTensor B (m v) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b => simp [tensorPairing_tmul]
  | add y y' hy hy' => simp only [map_add, hy, hy']

theorem induction_two {p : V ⊗[F] B → V' ⊗[F] B → Prop} (h0 : ∀ y, p 0 y) (h0' : ∀ x, p x 0)
    (ht : ∀ v a v' b, p (v ⊗ₜ[F] a) (v' ⊗ₜ[F] b))
    (ha : ∀ x x' y, p x y → p x' y → p (x + x') y)
    (ha' : ∀ x y y', p x y → p x y' → p x (y + y')) (x : V ⊗[F] B) (y : V' ⊗[F] B) : p x y := by
  induction x using TensorProduct.induction_on with
  | zero => exact h0 y
  | tmul v a =>
    induction y using TensorProduct.induction_on with
    | zero => exact h0' _
    | tmul v' b => exact ht v a v' b
    | add y y' hy hy' => exact ha' _ _ _ hy hy'
  | add x x' hx hx' => exact ha _ _ _ hx hx'

end

theorem exists_stPairing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → ∃ pr : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] Bst P, (∀ x y, pr (phiV P ℚ_[l] V x) (phiV P ℚ_[l] V' y) = phiSt P (pr x y)) ∧ (∀ x y, pr (monV P ℚ_[l] V x) y + pr x (monV P ℚ_[l] V' y) = monSt P (pr x y)) ∧ (∀ (g : ↥(GK K)) x y, pr (stRep P ρ g x) (stRep P ρ' g y) = ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) • actSt P (g : GQ l) (pr x y)) ∧ (∀ a x y, pr (onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) x) y = a * pr x y) ∧ ∀ y, (∀ v : V, pr (v ⊗ₜ[ℚ_[l]] (1 : Bst P)) y = 0) → y = 0 := by
  intro l _ P K V _ _ _ V' _ _ _ ρ ρ' m hm
  obtain ⟨hg, -, hr, -⟩ := hm
  have hcyc : ∀ g : ↥(GK K), ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) =
      ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) := fun g => by
    have h := P.PD_χ K g
    simp [cycLL, h]
  refine ⟨tensorPairing m, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    refine induction_two (p := fun x y => tensorPairing m (phiV P ℚ_[l] V x) (phiV P ℚ_[l] V' y) =
      phiSt P (tensorPairing m x y)) (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v a v' b
      simp [tensorPairing_tmul, map_mul, map_smul]
    · intro x x' y hx hx'
      simp only [map_add, LinearMap.add_apply, hx, hx']
    · intro x y y' hy hy'
      simp only [map_add, hy, hy']
  · intro x y
    refine induction_two (p := fun x y => tensorPairing m (monV P ℚ_[l] V x) y +
      tensorPairing m x (monV P ℚ_[l] V' y) = monSt P (tensorPairing m x y)) (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v a v' b
      simp only [monV_tmul, tensorPairing_tmul]
      rw [map_smul, ← smul_add]
      congr 1
      simp only [monSt_apply, Polynomial.derivative_mul]
      ring
    · intro x x' y hx hx'
      simp only [map_add, LinearMap.add_apply, ← hx, ← hx']
      abel
    · intro x y y' hy hy'
      simp only [map_add, ← hy, ← hy']
      abel
  · intro g x y
    refine induction_two (p := fun x y => tensorPairing m (stRep P ρ g x) (stRep P ρ' g y) =
      ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) • actSt P (g : GQ l) (tensorPairing m x y))
      (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v a v' b
      rw [stRep_tmul, stRep_tmul, tensorPairing_tmul, tensorPairing_tmul, hg, hcyc, map_smul, map_mul,
        smul_smul]
    · intro x x' y hx hx'
      simp only [map_add, LinearMap.add_apply, hx, hx', smul_add]
    · intro x y y' hy hy'
      simp only [map_add, hy, hy', smul_add]
  · intro a x y
    refine induction_two (p := fun x y => tensorPairing m (onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) x) y =
      a * tensorPairing m x y) (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v b v' c
      rw [onB_tmul, tensorPairing_tmul, tensorPairing_tmul, LinearMap.mulLeft_apply, mul_smul_comm,
        mul_assoc]
    · intro x x' y hx hx'
      simp only [map_add, LinearMap.add_apply, hx, hx', mul_add]
    · intro x y y' hy hy'
      simp only [map_add, hy, hy', mul_add]
  · intro y hy
    refine GlobalTheory.T.eq_zero_of_rTensor_pairing_eq_zero ℚ_[l] (Bst P) V V' m hr y fun v => ?_
    rw [← tensorPairing_one]
    exact hy v

end GlobalTheory.PMon.StPairing

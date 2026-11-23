import Formalism.PieriBlockIdeals.PieriColumnMinors.RowGenDerivative

open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

def idx (p q : ℕ) : Fin p ⊕ Fin q → Fin (p + q) := Sum.elim (Fin.castAdd q) (Fin.natAdd p)

theorem idx_inj (p q : ℕ) : Function.Injective (idx p q) := finSumFinEquiv.injective

abbrev VQ (p q w : ℕ) (lam2 : Fin q → ℕ) : Type :=
  ↥(dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2))

def EV (p q w : ℕ) (lam2 : Fin q → ℕ) (a b : Fin p ⊕ Fin q) : Module.End ℚ (VQ p q w lam2) :=
  LinearMap.restrict (der (p + q) (p + q) (idx p q a) (idx p q b) : Module.End ℚ _)
    (fun f hf => der_mem _ _ _ f hf)

theorem EV_coe (p q w : ℕ) (lam2 : Fin q → ℕ) (a b : Fin p ⊕ Fin q) (x : VQ p q w lam2) :
    ((EV p q w lam2 a b x : VQ p q w lam2) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) =
      der (p + q) (p + q) (idx p q a) (idx p q b) x := rfl

theorem EV_comm (p q w : ℕ) (lam2 : Fin q → ℕ) (a b c d : Fin p ⊕ Fin q) :
    EV p q w lam2 a b * EV p q w lam2 c d - EV p q w lam2 c d * EV p q w lam2 a b =
      (if b = c then EV p q w lam2 a d else 0) - (if d = a then EV p q w lam2 c b else 0) := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  have h := der_comm (idx p q a) (idx p q b) (idx p q c) (idx p q d)
    (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ)
  simp only [(idx_inj p q).eq_iff] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, EV_coe]
  rw [h]
  split_ifs <;> simp [EV_coe]

def W0 (p q w : ℕ) (lam2 : Fin q → ℕ) : Submodule ℚ (VQ p q w lam2) :=
  (⨅ (α : Fin p) (a : Fin q), LinearMap.ker (EV p q w lam2 (Sum.inl α) (Sum.inr a))) ⊓
    ⨅ (α : Fin p) (β : Fin p), LinearMap.ker (EV p q w lam2 (Sum.inl α) (Sum.inl β) -
      if α = β then (w : ℚ) • (1 : Module.End ℚ (VQ p q w lam2)) else 0)

theorem mem_orthogonal_frame_iff (p q w : ℕ) (lam2 : Fin q → ℕ) (u : VQ p q w lam2) :
    u ∈ W0 p q w lam2 ↔ (∀ (α : Fin p) (a : Fin q), EV p q w lam2 (Sum.inl α) (Sum.inr a) u = 0) ∧
      ∀ α β : Fin p, EV p q w lam2 (Sum.inl α) (Sum.inl β) u = if α = β then (w : ℚ) • u else 0 := by
  simp only [W0, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  refine and_congr Iff.rfl (forall_congr' fun α => forall_congr' fun β => ?_)
  split_ifs <;> simp

theorem w_zero_stable_right_block (p q w : ℕ) (lam2 : Fin q → ℕ) (b b' : Fin q) (u : VQ p q w lam2) (hu : u ∈ W0 p q w lam2) :
    EV p q w lam2 (Sum.inr b) (Sum.inr b') u ∈ W0 p q w lam2 := by
  rw [mem_orthogonal_frame_iff] at hu ⊢
  refine ⟨fun α a => ?_, fun α β => ?_⟩
  · have h := congrArg (fun T => T u) (EV_comm p q w lam2 (Sum.inl α) (Sum.inr a) (Sum.inr b) (Sum.inr b'))
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hu.1, map_zero, sub_zero, reduceCtorEq, if_false] at h
    rw [h]
    split_ifs <;> simp [hu.1]
  · have h := congrArg (fun T => T u) (EV_comm p q w lam2 (Sum.inl α) (Sum.inl β) (Sum.inr b) (Sum.inr b'))
    simp only [LinearMap.sub_apply, Module.End.mul_apply, reduceCtorEq, if_false, sub_zero, LinearMap.zero_apply,
      sub_eq_zero] at h
    rw [h, hu.2]
    split_ifs <;> simp

def rationalBlockModuleSetting (p q w : ℕ) (lam2 : Fin q → ℕ) : HidaSetting ℚ (VQ p q w lam2) (Fin p) (Fin q) where
  E := EV p q w lam2
  comm := EV_comm p q w lam2
  W := W0 p q w lam2
  w := (w : ℚ)
  kill := fun α a u hu => ((mem_orthogonal_frame_iff p q w lam2 u).1 hu).1 α a
  scal := fun α β u hu => ((mem_orthogonal_frame_iff p q w lam2 u).1 hu).2 α β
  stab := w_zero_stable_right_block p q w lam2

def formB (p q w : ℕ) (lam2 : Fin q → ℕ) : LinearMap.BilinForm ℚ (VQ p q w lam2) :=
  LinearMap.mk₂ ℚ
    (fun x y => fockQ (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) y /
      fockQ (hw ℚ le_rfl (LD.blockWt p q w lam2)) (hw ℚ le_rfl (LD.blockWt p q w lam2)))
    (fun x x' y => by simp only [Submodule.coe_add, fock_add_left, add_div])
    (fun c x y => by simp only [Submodule.coe_smul, fock_smul_left, smul_eq_mul, mul_div_assoc])
    (fun x y y' => by simp only [Submodule.coe_add, fock_add_right, add_div])
    (fun c x y => by simp only [Submodule.coe_smul, fock_smul_right, smul_eq_mul, mul_div_assoc])

def PieriReal : Prop :=
  ∀ (p q w : ℕ) (lam2 : Fin q → ℕ), Antitone lam2 → (∀ b, lam2 b ≤ w) → ∀ n : ℕ,
    (⨆ tau, PathSpace ℚ (P := Fin p) (rationalBlockModuleSetting p q w lam2).EW n lam2 tau) = ⊤

def ColumnsReal : Prop :=
  ∀ (p q w : ℕ) (lam2 : Fin q → ℕ), Antitone lam2 → (∀ b, lam2 b ≤ w) → ∀ (n : ℕ) (tau : Fin q → ℕ),
    (∃ b : Fin q, ∃ j < tau b, p < LD.colLen lam2 tau j) →
    ∀ z ∈ PathSpace ℚ (P := Fin p) (rationalBlockModuleSetting p q w lam2).EW n lam2 tau, toSym ℚ z = 0

def HighestWeightMemWZero : Prop :=
  ∀ (p q w : ℕ) (lam2 : Fin q → ℕ), Antitone lam2 → (∀ b, lam2 b ≤ w) →
    ∃ h : VQ p q w lam2, (h : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = hw ℚ le_rfl (LD.blockWt p q w lam2) ∧
      h ∈ W0 p q w lam2

def RealContra : Prop :=
  ∀ (p q w : ℕ) (lam2 : Fin q → ℕ), Contra (rationalBlockModuleSetting p q w lam2) (formB p q w lam2)

def RealNondeg : Prop :=
  ∀ (p q w : ℕ) (lam2 : Fin q → ℕ) (v : VQ p q w lam2), (∀ x, formB p q w lam2 x v = 0) → v = 0

def RealIrred : Prop :=
  ∀ (p q w : ℕ) (lam2 : Fin q → ℕ), Antitone lam2 → (∀ b, lam2 b ≤ w) →
    ∀ Z : Submodule ℚ (VQ p q w lam2), Z ≤ W0 p q w lam2 →
      (∀ b b' : Fin q, ∀ u ∈ Z, EV p q w lam2 (Sum.inr b) (Sum.inr b') u ∈ Z) → Z ≠ ⊥ →
      ∀ h : VQ p q w lam2, (h : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = hw ℚ le_rfl (LD.blockWt p q w lam2) → h ∈ Z

def RealGenerated : Prop :=
  ∀ (p q w : ℕ) (lam2 : Fin q → ℕ), Antitone lam2 → (∀ b, lam2 b ≤ w) → Generated (rationalBlockModuleSetting p q w lam2)

def RealWeight : Prop :=
  ∀ (p q w : ℕ) (lam2 : Fin q → ℕ) (v : VQ p q w lam2) (μ : Fin (p + q) → ℕ),
    IsWeightedHomogeneous (rowW (p + q) (p + q)) (v : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) μ ↔
      v ∈ (rationalBlockModuleSetting p q w lam2).wt fun a => (μ (idx p q a) : ℤ)

def RealOfSkeleton : Prop :=
  CoeffWord → LowerTriIntegral → PieriReal → ColumnsReal → LD.LemmaDGraded

def RealOfPieri : Prop :=
  PieriReal → ColumnsReal → LD.LemmaDGraded

end Formalism.CohomologicalDescent.LR

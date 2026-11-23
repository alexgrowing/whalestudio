import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.AlgInfCharIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.WignerVanishingGL
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.AntisymmetrizedProductEqFactorialSmulQdet

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh

namespace UpperTheory.V.AlgRepEndIrreducible

section Tel

variable {X M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M]

def rp : (n : ℕ) → (Fin n → X →ₗ[ℂ] Module.End ℂ M) → (Fin n → X) → Module.End ℂ M
  | 0, _, _ => 1
  | n + 1, b, x => rp n (Fin.tail b) (Fin.tail x) * b 0 (x 0)

def tel : (n : ℕ) → (Fin n → X →ₗ[ℂ] Module.End ℂ M) → (Fin n → X →ₗ[ℂ] Module.End ℂ M) → (X →ₗ[ℂ] M) →
    (Fin n → X) → M
  | 0, _, _, _, _ => 0
  | n + 1, a, b, f, x =>
    a 0 (x 0) (tel n (Fin.tail a) (Fin.tail b) f (Fin.tail x)) + rp n (Fin.tail b) (Fin.tail x) (f (x 0))

theorem rp_zero (b : Fin 0 → X →ₗ[ℂ] Module.End ℂ M) (x : Fin 0 → X) : rp 0 b x = 1 := rfl

theorem rp_succ {n : ℕ} (b : Fin (n + 1) → X →ₗ[ℂ] Module.End ℂ M) (x : Fin (n + 1) → X) :
    rp (n + 1) b x = rp n (Fin.tail b) (Fin.tail x) * b 0 (x 0) := rfl

theorem tel_zero (a b : Fin 0 → X →ₗ[ℂ] Module.End ℂ M) (f : X →ₗ[ℂ] M) (x : Fin 0 → X) : tel 0 a b f x = 0 := rfl

theorem tel_succ {n : ℕ} (a b : Fin (n + 1) → X →ₗ[ℂ] Module.End ℂ M) (f : X →ₗ[ℂ] M) (x : Fin (n + 1) → X) :
    tel (n + 1) a b f x =
      a 0 (x 0) (tel n (Fin.tail a) (Fin.tail b) f (Fin.tail x)) + rp n (Fin.tail b) (Fin.tail x) (f (x 0)) := rfl

def units {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (k : Fin n) : Matrix (Fin n) (Fin n) ℂ := Matrix.single (σ k) (τ k) 1

def eps {n : ℕ} (μ : (Fin n → Matrix (Fin n) (Fin n) ℂ) → M) : M :=
  ∑ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n),
    ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) • μ (units σ τ)

end Tel

section HW

variable {ι V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

def IsMultiGl {A : Type} [Ring A] (F : ι → Fin n → Fin n → A) : Prop :=
  (∀ t, Formalism.REAL.GlRel (F t)) ∧ ∀ s t, s ≠ t → ∀ i j k l, F s i j * F t k l = F t k l * F s i j

def Stab (F : ι → Fin n → Fin n → Module.End ℂ V) (W : Submodule ℂ V) : Prop := ∀ t i j, ∀ w ∈ W, F t i j w ∈ W

def low (F : ι → Fin n → Fin n → Module.End ℂ V) (v : V) : Submodule ℂ V :=
  sInf {W | v ∈ W ∧ ∀ t i j, j < i → ∀ w ∈ W, F t i j w ∈ W}

def Dom (ν : Fin n → ℂ) : Prop := ∀ i j, i < j → ∃ m : ℕ, ν i - ν j = (m : ℂ)

end HW

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

section Hol

variable {N : Type} [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N]

omit [NumberField E] in

def eL (L : Lie E a →ₗ[ℝ] N) (τ : E →+* ℂ) (i j : Fin a) : N :=
  (1 / 2 : ℂ) • (L (toL (Matrix.single i j (atEmb τ 1))) - Complex.I • L (toL (Matrix.single i j (atEmb τ Complex.I))))

omit [NumberField E] in

def hol (τ : E →+* ℂ) (L : Lie E a →ₗ[ℝ] N) : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] N where
  toFun x := ∑ i, ∑ j, x i j • eL L τ i j
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, mul_smul]

omit [NumberField E] [IsScalarTower ℝ ℂ N] in
theorem hol_apply (τ : E →+* ℂ) (L : Lie E a →ₗ[ℝ] N) (x : Matrix (Fin a) (Fin a) ℂ) :
    hol τ L x = ∑ i, ∑ j, x i j • eL L τ i j := rfl

omit [NumberField E] [IsScalarTower ℝ ℂ N] in
theorem hol_single (τ : E →+* ℂ) (L : Lie E a →ₗ[ℝ] N) (i j : Fin a) : hol τ L (Matrix.single i j 1) = eL L τ i j := by
  simp [hol_apply, Matrix.single_apply, ite_and]

end Hol

theorem eL_dmat (Ξ : AlgRep E a) (τ : E →+* ℂ) : eL Ξ.dmat τ = WeylC.eOf Ξ.mat τ := rfl

theorem dualE_eq (Ξ : AlgRep E a) (τ : E →+* ℂ) (i j : Fin a) :
    GlobalTheory.WignerGL.dualE Ξ τ i j = -(eL Ξ.dmat τ i j)ᵀ := by
  simp only [GlobalTheory.WignerGL.dualE, GlobalTheory.WignerGL.dualS, eL, Matrix.transpose_smul, Matrix.transpose_sub]
  module

omit [NumberField E] in

def IsLieHom {A : Type} [Ring A] [Module ℝ A] (L : Lie E a →ₗ[ℝ] A) : Prop :=
  ∀ X Y : Matrix (Fin a) (Fin a) (Cinf E), L (toL X) * L (toL Y) - L (toL Y) * L (toL X) = L (toL (X * Y - Y * X))

omit [NumberField E] in

def hp : Lie E a →ₗ[ℝ] Herm E a where
  toFun X := ⟨(1 / 2 : ℝ) • (Matrix.of X + star (Matrix.of X)), by
    change star _ = _
    rw [star_smul, star_add, star_star, add_comm, star_trivial]⟩
  map_add' X Y := Subtype.ext (by
    change (1 / 2 : ℝ) • ((Matrix.of X + Matrix.of Y) + star (Matrix.of X + Matrix.of Y)) = _ + _
    rw [star_add, ← smul_add]; congr 1; abel)
  map_smul' c X := Subtype.ext (by
    change (1 / 2 : ℝ) • (c • Matrix.of X + star (c • Matrix.of X)) = c • ((1 / 2 : ℝ) • _)
    rw [star_smul, star_trivial, ← smul_add, smul_comm])

omit [NumberField E] in
theorem hp_val (X : Matrix (Fin a) (Fin a) (Cinf E)) : (hp (toL X)).1 = (1 / 2 : ℝ) • (X + star X) := rfl

omit [NumberField E] in

def brH (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) (Y : Herm E a) : Herm E a :=
  ⟨Z * Y.1 - Y.1 * Z, by
    have h : star Y.1 = Y.1 := Y.2
    change star _ = _
    rw [star_sub, star_mul, star_mul, h, hZ]
    noncomm_ring⟩

section Complex

variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M)

omit [NumberField E] in

def InfEq {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : Prop :=
  ∀ (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) (Y : Fin q → Herm E a),
    L (toL Z) (ω Y) = ∑ i, ω (Function.update Y i (brH Z hZ (Y i)))

def SepDer : Prop :=
  ∀ (k : ℝ → Kinf E a) (Z : Matrix (Fin a) (Fin a) (Cinf E)), k 0 = 1 → HasDerivAt (fun t => toL (k t).1) (toL Z) 0 →
    ∀ m' : M, m' ≠ 0 → ∃ l : M →ₗ[ℂ] ℂ, l m' ≠ 0 ∧ ∀ m, HasDerivAt (fun t => l (κ (k t) m)) (l (L (toL Z) m)) 0

omit [NumberField E] in

structure IsRetr (α : (Lie E a →ₗ[ℝ] M) →ₗ[ℝ] M) : Prop where
  lie : ∀ (Y : Matrix (Fin a) (Fin a) (Cinf E)) (f f' : Lie E a →ₗ[ℝ] M),
    (∀ X, L (toL Y) (f (toL X)) = f' (toL X) + f (toL (Y * X - X * Y))) → L (toL Y) (α f) = α f'
  cpt : ∀ (k : Kinf E a) (f f' : Lie E a →ₗ[ℝ] M),
    (∀ X, κ k (f (toL X)) = f' (toL (k.1 * X * star k.1))) → κ k (α f) = α f'
  retr : ∀ (m : M) (f : Lie E a →ₗ[ℝ] M), (∀ X, f X = L X m) → α f = m

end Complex

section Tensor

open scoped TensorProduct

variable [IsTotallyComplex E]

def lieA (π : CuspSub E a) (Ξ : AlgRep E a) : Lie E a →ₗ[ℝ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) where
  toFun X := (lieOp π X).rTensor _
  map_add' X Y := by simp only [map_add, LinearMap.rTensor_add]
  map_smul' c X := by
    rw [map_smul, RingHom.id_apply, ← algebraMap_smul ℂ c (lieOp π X),
      ← algebraMap_smul ℂ c (LinearMap.rTensor _ _ : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))), LinearMap.rTensor_smul]

def lieB (π : CuspSub E a) (Ξ : AlgRep E a) : Lie E a →ₗ[ℝ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) where
  toFun X := (Matrix.toLin' (Ξ.dmat X)).lTensor _
  map_add' X Y := by simp only [map_add, LinearMap.lTensor_add]
  map_smul' c X := by
    rw [map_smul, RingHom.id_apply, ← algebraMap_smul ℂ c (Ξ.dmat X),
      ← algebraMap_smul ℂ c (LinearMap.lTensor _ _ : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))), map_smul,
      LinearMap.lTensor_smul]

theorem lieA_apply (π : CuspSub E a) (Ξ : AlgRep E a) (X : Lie E a) : lieA π Ξ X = (lieOp π X).rTensor _ := rfl

theorem lieB_apply (π : CuspSub E a) (Ξ : AlgRep E a) (X : Lie E a) :
    lieB π Ξ X = (Matrix.toLin' (Ξ.dmat X)).lTensor _ := rfl

theorem tensorLie_eq (π : CuspSub E a) (Ξ : AlgRep E a) : tensorLie π Ξ = lieA π Ξ + lieB π Ξ := rfl

theorem lieA_commute (π : CuspSub E a) (Ξ : AlgRep E a) (X Y : Lie E a) : Commute (lieA π Ξ X) (lieB π Ξ Y) :=
  TensorProduct.ext' fun _ _ => rfl

end Tensor

def eEnd (Ξ : AlgRep E a) (τ : E →+* ℂ) (i j : Fin a) : Module.End ℂ (Fin Ξ.d → ℂ) := Matrix.toLin' (eL Ξ.dmat τ i j)

def IsAlgIso (Ξ Ξ' : AlgRep E a) (T : (Fin Ξ.d → ℂ) ≃ₗ[ℂ] (Fin Ξ'.d → ℂ)) : Prop :=
  (∀ y v, T (Ξ.mat y *ᵥ v) = Ξ'.mat y *ᵥ T v) ∧ ∀ X v, T (Ξ.dmat X *ᵥ v) = Ξ'.dmat X *ᵥ T v

theorem isAlgIso_refl (Ξ : AlgRep E a) : IsAlgIso Ξ Ξ (LinearEquiv.refl _ _) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

end UpperTheory.V.AlgRepEndIrreducible

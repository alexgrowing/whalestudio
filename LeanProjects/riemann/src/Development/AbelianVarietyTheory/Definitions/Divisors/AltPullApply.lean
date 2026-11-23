import Mathlib

noncomputable section

namespace GlobalTheory.KS

variable {O : Type} [Ring O] {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]

def matAct (ρ : O →+* Module.End R V) {m : ℕ} (M : Matrix (Fin m) (Fin m) O) : (Fin m → V) →ₗ[R] (Fin m → V) :=
  LinearMap.pi fun i => ∑ j, ρ (M i j) ∘ₗ LinearMap.proj j

theorem matAct_apply (ρ : O →+* Module.End R V) {m : ℕ} (M : Matrix (Fin m) (Fin m) O) (x : Fin m → V) (i : Fin m) :
    matAct ρ M x i = ∑ j, ρ (M i j) (x j) := by
  simp [matAct]

abbrev Alt (R : Type) [CommRing R] (W : Type) [AddCommGroup W] [Module R W] (E : Type) [CommRing E] [Algebra R E] (q : ℕ) :
    Type := W [⋀^Fin q]→ₗ[R] E

variable {E : Type} [CommRing E] [Algebra R E]

def altPull (E : Type) [CommRing E] [Algebra R E] {W W' : Type} [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (u : W' →ₗ[R] W) (q : ℕ) : Alt R W E q →ₗ[E] Alt R W' E q where
  toFun f := f.compLinearMap u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem altPull_apply {W W' : Type} [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (u : W' →ₗ[R] W) (q : ℕ) (f : Alt R W E q) (x : Fin q → W') : altPull E u q f x = f fun i => u (x i) := rfl

def altOp (ρ : O →+* Module.End R V) {m : ℕ} (ε : Matrix (Fin m) (Fin m) O →₀ E) (q : ℕ) :
    Module.End E (Alt R (Fin m → V) E q) :=
  ε.sum fun M c => c • altPull E (matAct ρ M) q

structure IsCut (ρ : O →+* Module.End R V) {m : ℕ} (ε : Matrix (Fin m) (Fin m) O →₀ E) (k : ℕ) : Prop where
  idem : altOp ρ ε k * altOp ρ ε k = altOp ρ ε k
  zero : ∀ q, q ≠ k → altOp ρ ε q = 0

variable {Γ : Type} [Group Γ]

def altRep (E : Type) [CommRing E] [Algebra R E] {W : Type} [AddCommGroup W] [Module R W] (σ : Representation R Γ W) (q : ℕ) :
    Representation E Γ (Alt R W E q) where
  toFun γ := altPull E (σ γ⁻¹) q
  map_one' := by
    ext f x
    simp [altPull]
  map_mul' γ δ := by
    ext f x
    simp [Module.End.mul_apply]

def powRep (σ : Representation R Γ V) (m : ℕ) : Representation R Γ (Fin m → V) where
  toFun γ := LinearMap.pi fun i => σ γ ∘ₗ LinearMap.proj i
  map_one' := by
    ext x i
    simp
  map_mul' γ δ := by
    ext x i
    simp

theorem altOp_comm (ρ : O →+* Module.End R V) (σ : Representation R Γ V) (hσ : ∀ γ b, σ γ * ρ b = ρ b * σ γ) {m : ℕ}
    (ε : Matrix (Fin m) (Fin m) O →₀ E) (q : ℕ) (γ : Γ) :
    altRep E (powRep σ m) q γ * altOp ρ ε q = altOp ρ ε q * altRep E (powRep σ m) q γ := by
  have h : ∀ (M : Matrix (Fin m) (Fin m) O) (x : Fin m → V),
      matAct ρ M (powRep σ m γ⁻¹ x) = powRep σ m γ⁻¹ (matAct ρ M x) := by
    intro M x
    funext i
    have h1 : ∀ b y, σ γ⁻¹ (ρ b y) = ρ b (σ γ⁻¹ y) := fun b y => LinearMap.congr_fun (hσ γ⁻¹ b) y
    simp [matAct_apply, powRep, map_sum, h1]
  unfold altOp Finsupp.sum
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  ext f x
  change f (fun i => matAct ρ M (powRep σ m γ⁻¹ (x i))) = f (fun i => powRep σ m γ⁻¹ (matAct ρ M (x i)))
  simp only [h]

def xiRep (ρ : O →+* Module.End R V) (σ : Representation R Γ V) (hσ : ∀ γ b, σ γ * ρ b = ρ b * σ γ) {m : ℕ}
    (ε : Matrix (Fin m) (Fin m) O →₀ E) (k : ℕ) : Representation E Γ (LinearMap.range (altOp ρ ε k)) :=
  (altRep E (powRep σ m) k).subrepresentation _ fun γ => by
    rintro _ ⟨f, rfl⟩
    exact ⟨altRep E (powRep σ m) k γ f, (LinearMap.congr_fun (altOp_comm ρ σ hσ ε k γ) f).symm⟩

example (ρ : O →+* Module.End R V) : IsCut ρ (Finsupp.single (1 : Matrix (Fin 0) (Fin 0) O) (1 : E)) 0 where
  idem := by
    have : altOp ρ (Finsupp.single (1 : Matrix (Fin 0) (Fin 0) O) (1 : E)) 0 = 1 := by
      ext f x
      simp only [altOp, zero_smul, Finsupp.sum_single_index, one_smul, altPull_apply, Module.End.one_apply]
      exact congrArg f (Subsingleton.elim _ _)
    rw [this, one_mul]
  zero q hq := by
    ext f x
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    simp only [altOp, zero_smul, Finsupp.sum_single_index, one_smul, altPull, LinearMap.coe_mk, AddHom.coe_mk,
      AlternatingMap.compLinearMap_apply, LinearMap.zero_apply, AlternatingMap.zero_apply]
    exact f.map_coord_zero 0 (Subsingleton.elim _ _)

end GlobalTheory.KS

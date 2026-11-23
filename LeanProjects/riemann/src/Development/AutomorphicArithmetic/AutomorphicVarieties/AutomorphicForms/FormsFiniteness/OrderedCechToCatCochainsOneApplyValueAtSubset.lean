import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspFinite
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

noncomputable section

open NumberField NumberField.mixedEmbedding Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped TensorProduct

namespace UpperTheory.V.Af.Fin

attribute [local instance 100] LieRing.ofAssociativeRing

section Emb

variable {a n : ℕ} (e : Fin a ↪ Fin n) (R : Type) [CommRing R]

def inc : Matrix (Fin n) (Fin a) R := Matrix.of fun i k => if i = e k then 1 else 0

theorem inc_tr_mul : (inc e R)ᵀ * inc e R = 1 := by
  ext k l
  simp [inc, Matrix.mul_apply, Matrix.one_apply, eq_comm]

variable {R}

def ext0 (X : Matrix (Fin a) (Fin a) R) : Matrix (Fin n) (Fin n) R := inc e R * X * (inc e R)ᵀ

theorem matrixExtendByZero_mul (X Y : Matrix (Fin a) (Fin a) R) : ext0 e X * ext0 e Y = ext0 e (X * Y) := by
  simp only [ext0, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (inc e R)ᵀ, inc_tr_mul, Matrix.one_mul]

theorem matrixExtendByZero_add (X Y : Matrix (Fin a) (Fin a) R) : ext0 e (X + Y) = ext0 e X + ext0 e Y := by
  simp only [ext0, Matrix.mul_add, Matrix.add_mul]

theorem extension_zero_sub (X Y : Matrix (Fin a) (Fin a) R) : ext0 e (X - Y) = ext0 e X - ext0 e Y := by
  simp only [ext0, Matrix.mul_sub, Matrix.sub_mul]

theorem matrixExtendByZero_zero : ext0 e (0 : Matrix (Fin a) (Fin a) R) = 0 := by simp [ext0]

theorem matrixExtendByZero_apply (X : Matrix (Fin a) (Fin a) R) (i j : Fin a) : ext0 e X (e i) (e j) = X i j := by
  simp [ext0, inc, Matrix.mul_apply]

theorem extendByZero_apply_eq_zero_of_row_not_mem (X : Matrix (Fin a) (Fin a) R) {i : Fin n} (hi : ∀ k, i ≠ e k) (j : Fin n) : ext0 e X i j = 0 := by
  simp [ext0, inc, Matrix.mul_apply, hi]

theorem matrixExtendByZero_apply_of_outside_col (X : Matrix (Fin a) (Fin a) R) (i : Fin n) {j : Fin n} (hj : ∀ k, j ≠ e k) : ext0 e X i j = 0 := by
  simp [ext0, inc, Matrix.mul_apply, hj]

theorem matrixExtendByZero_map {S : Type} [CommRing S] (f : R →+* S) (X : Matrix (Fin a) (Fin a) R) :
    (ext0 e X).map f = ext0 e (X.map f) := by
  have h : (inc e R).map f = inc e S := by
    ext i k
    simp [inc, apply_ite f]
  simp only [ext0, Matrix.map_mul, Matrix.transpose_map, h]

theorem matrixExtendByZero_single (i j : Fin a) (x : R) : ext0 e (Matrix.single i j x) = Matrix.single (e i) (e j) x := by
  ext k l
  by_cases hk : ∃ k', k = e k'
  · obtain ⟨k, rfl⟩ := hk
    by_cases hl : ∃ l', l = e l'
    · obtain ⟨l, rfl⟩ := hl
      simp [matrixExtendByZero_apply, Matrix.single_apply]
    · push Not at hl
      rw [matrixExtendByZero_apply_of_outside_col e _ _ hl, Matrix.single_apply, if_neg fun h => hl j h.2.symm]
  · push Not at hk
    rw [extendByZero_apply_eq_zero_of_row_not_mem e _ hk, Matrix.single_apply, if_neg fun h => hk i h.1.symm]

def embM : Matrix (Fin a) (Fin a) R →* Matrix (Fin n) (Fin n) R where
  toFun X := 1 + ext0 e (X - 1)
  map_one' := by rw [sub_self, matrixExtendByZero_zero, add_zero]
  map_mul' X Y := by
    rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, matrixExtendByZero_mul, add_assoc, ← matrixExtendByZero_add, ← matrixExtendByZero_add]
    congr 2
    noncomm_ring

def emb : GL (Fin a) R →* GL (Fin n) R := Units.map (embM e)

theorem coe_emb (g : GL (Fin a) R) : (emb e g).val = 1 + ext0 e (g.val - 1) := rfl

theorem emb_map {S : Type} [CommRing S] (f : R →+* S) (g : GL (Fin a) R) :
    Matrix.GeneralLinearGroup.map f (emb e g) = emb e (Matrix.GeneralLinearGroup.map f g) := by
  refine Units.ext ?_
  change (1 + ext0 e (g.val - 1)).map f = 1 + ext0 e (g.val.map f - 1)
  rw [Matrix.map_add _ (map_add f), matrixExtendByZero_map, Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f),
    Matrix.map_one _ (map_zero f) (map_one f)]

end Emb

def e1 (r s : ℕ) : Fin r ↪ Fin (r + s) := Fin.castAddEmb s

def e2 (r s : ℕ) : Fin s ↪ Fin (r + s) := Fin.natAddEmb r

@[simp] theorem orderedCechToCatCochainsOne_apply_valueAtSubset {r s : ℕ} (i : Fin r) : e1 r s i = Fin.castAdd s i := rfl

@[simp] theorem alternatingToOrderedCechDegreeTwo_apply_valueAtSubset {r s : ℕ} (i : Fin s) : e2 r s i = Fin.natAdd r i := rfl

def blk {r s : ℕ} {R : Type} [CommRing R] (m₁ : GL (Fin r) R) (m₂ : GL (Fin s) R) : GL (Fin (r + s)) R :=
  emb (e1 r s) m₁ * emb (e2 r s) m₂

theorem emb_comm {r s : ℕ} {R : Type} [CommRing R] (m₁ : GL (Fin r) R) (m₂ : GL (Fin s) R) :
    emb (e1 r s) m₁ * emb (e2 r s) m₂ = emb (e2 r s) m₂ * emb (e1 r s) m₁ := by
  have h : (inc (e1 r s) R)ᵀ * inc (e2 r s) R = 0 := by
    ext k l
    have : ¬ Fin.natAdd r l = Fin.castAdd s k := fun h => by have := congrArg Fin.val h; simp at this; omega
    simp only [inc, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h1 h2
    · exact absurd (h2.symm.trans h1) this
    · exact mul_zero _
    · exact zero_mul _
    · exact zero_mul _
  have h' : (inc (e2 r s) R)ᵀ * inc (e1 r s) R = 0 := by
    rw [← Matrix.transpose_transpose (inc (e1 r s) R), ← Matrix.transpose_mul, h, Matrix.transpose_zero]
  have h1 : ∀ X Y, ext0 (e1 r s) X * ext0 (e2 r s) (Y : Matrix _ _ R) = 0 := fun X Y => by
    simp only [ext0, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (inc (e1 r s) R)ᵀ, h]
    simp
  have h2 : ∀ X Y, ext0 (e2 r s) X * ext0 (e1 r s) (Y : Matrix _ _ R) = 0 := fun X Y => by
    simp only [ext0, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (inc (e2 r s) R)ᵀ, h']
    simp
  refine Units.ext ?_
  simp only [Units.val_mul, coe_emb, add_mul, mul_add, one_mul, mul_one, h1, h2]
  abel

structure Idem (R : Type) [CommRing R] [Algebra ℝ R] (ι : Type) [Fintype ι] where

  e : ι → ℂ ⊗[ℝ] R

  ch : ι → R →+* ℂ
  mul_e : ∀ τ x, ((1 : ℂ) ⊗ₜ[ℝ] x) * e τ = ch τ x • e τ
  orth : ∀ τ σ, τ ≠ σ → e τ * e σ = 0
  sum : ∑ τ, e τ = 1

section Gen

variable {R : Type} [CommRing R] [Algebra ℝ R] {ι : Type} [Fintype ι] {n : ℕ}
  {A : Type} [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A]

def IsLie (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A) : Prop := ∀ X Y, l X * l Y - l Y * l X = l (X * Y - Y * X)

def unitMap (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A) (i j : Fin n) : ℂ ⊗[ℝ] R →ₗ[ℂ] A :=
  LinearMap.liftBaseChange ℂ (l ∘ₗ Matrix.singleLinearMap ℝ i j)

theorem unitMap_tmul (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A) (i j : Fin n) (c : ℂ) (x : R) :
    unitMap l i j (c ⊗ₜ x) = c • l (Matrix.single i j x) := by
  simp [unitMap]

def gen (D : Idem R ι) (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A) (τ : ι) (i j : Fin n) : A := unitMap l i j (D.e τ)

theorem gen_mem (D : Idem R ι) (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A) (τ : ι) (i j : Fin n) (P : Submodule ℂ A)
    (h : ∀ x, l (Matrix.single i j x) ∈ P) : gen D l τ i j ∈ P := by
  unfold gen
  induction D.e τ with
  | zero => rw [map_zero]; exact P.zero_mem
  | tmul c x => rw [unitMap_tmul]; exact P.smul_mem c (h x)
  | add x y hx hy => rw [map_add]; exact P.add_mem hx hy

theorem gen_inter {m : ℕ} {B : Type} [Ring B] [Algebra ℂ B] [Algebra ℝ B] [IsScalarTower ℝ ℂ B] {N : Type}
    [AddCommGroup N] [Module ℂ N] (D : Idem R ι) (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A)
    (l' : Matrix (Fin m) (Fin m) R →ₗ[ℝ] B) (τ : ι) (i j : Fin n) (i' j' : Fin m) (f : A →ₗ[ℂ] N) (f' : B →ₗ[ℂ] N)
    (h : ∀ x, f (l (Matrix.single i j x)) = f' (l' (Matrix.single i' j' x))) :
    f (gen D l τ i j) = f' (gen D l' τ i' j') := by
  unfold gen
  induction D.e τ with
  | zero => simp only [map_zero]
  | tmul c x => simp only [unitMap_tmul, map_smul, h]
  | add x y hx hy => simp only [map_add, hx, hy]

end Gen

variable (K : Type) [Field K] [NumberField K] (n : ℕ)

def toLie : Matrix (Fin n) (Fin n) (mixedSpace K) ≃ₗ[ℝ] (isExpLieAlgebra K n).lieSubalgebra where
  toFun X := ⟨X, mem_lie (K := K) (n := n) X⟩
  invFun Y := mat Y.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def lam : Matrix (Fin n) (Fin n) (mixedSpace K) →ₗ[ℝ] Module.End ℂ (archSmooth K n) :=
  (uAction (K := K) (n := n)).toLinearMap ∘ₗ
    (UniversalEnvelopingAlgebra.ι ℝ (L := (isExpLieAlgebra K n).lieSubalgebra)).toLinearMap ∘ₗ (toLie K n).toLinearMap

theorem lam_apply (X : Matrix (Fin n) (Fin n) (mixedSpace K)) :
    lam K n X = uAction (UniversalEnvelopingAlgebra.ι ℝ (toLie K n X)) := rfl

theorem isLie_lam : IsLie (lam K n) := fun X Y => by
  simp only [lam_apply]
  rw [← map_mul uAction, ← map_mul uAction, ← map_sub uAction, ← Ring.lie_def, ← LieHom.map_lie]
  rfl

def Zc : Subalgebra ℂ (Module.End ℂ (archSmooth K n)) :=
  Algebra.adjoin ℂ (uAction '' ((isExpLieAlgebra K n).centerU : Set (UEnv K n)))

variable {K n}

theorem uAction_mem_Zc {z : UEnv K n} (hz : z ∈ (isExpLieAlgebra K n).centerU) : uAction z ∈ Zc K n :=
  Algebra.subset_adjoin ⟨z, hz, rfl⟩

theorem Zc_comm_uAction {x : Module.End ℂ (archSmooth K n)} (hx : x ∈ Zc K n) (u : UEnv K n) :
    Commute x (uAction u) := by
  refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx ?_).symm
  rintro _ ⟨z, hz, rfl⟩
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 hz]

theorem Zc_comm {x y : Module.End ℂ (archSmooth K n)} (hx : x ∈ Zc K n) (hy : y ∈ Zc K n) : x * y = y * x := by
  refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy ?_).eq
  rintro _ ⟨z, -, rfl⟩
  exact Zc_comm_uAction hx z

def capOp {ι : Type} [Fintype ι] (D : Idem (mixedSpace K) ι) (n : ℕ) (τ : ι) (u : ℂ) : Module.End ℂ (archSmooth K n) :=
  Formalism.REAL.qdet (gen D (lam K n) τ) u

def archCapBlock {ι : Type} [Fintype ι] (D : Idem (mixedSpace K) ι) {a : ℕ} (e : Fin a ↪ Fin n) (τ : ι) (u : ℂ) :
    Module.End ℂ (archSmooth K n) :=
  Formalism.REAL.qdet (fun i j => gen D (lam K n) τ (e i) (e j)) u

def rt (g : AdelicGLn.AdelicGL K n) : Module.End ℂ (archSmooth K n) := rtInf (archPart g) ∘ₗ rtFin (finPart g)

theorem rt_apply (g : AdelicGLn.AdelicGL K n) (φ : archSmooth K n) (x : AdelicGLn.AdelicGL K n) :
    (rt g φ).1 x = φ.1 (x * g) := by
  change φ.1 (x * infEmb K n (archPart g) * finEmb K n (finPart g)) = _
  rw [mul_assoc, infEmb_archPart_mul_finEmb_finPart]

def Sat (S : Submodule ℂ (archSmooth K n)) : Prop := ∀ k ∈ Reduction.maxCompact (K := K) (n := n), ∀ φ ∈ S, rt k φ ∈ S

variable (K n) in

def NInv (r : ℕ) : Submodule ℂ (archSmooth K n) where
  carrier := {ψ | ∀ (X : UPos n r → AdeleRing (𝓞 K) K) g, ψ.1 (unipGL X * g) = ψ.1 g}
  add_mem' h1 h2 X g := congrArg₂ (· + ·) (h1 X g) (h2 X g)
  zero_mem' _ _ := rfl
  smul_mem' c _ h X g := congrArg (c • ·) (h X g)

variable (K) in

def Van (r s : ℕ) : Submodule ℂ (archSmooth K (r + s)) where
  carrier := {ψ | ∀ m₁ m₂, ψ.1 (blk m₁ m₂) = 0}
  add_mem' {x y} h1 h2 m₁ m₂ := by
    change x.1 _ + y.1 _ = 0
    rw [h1, h2, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c x h m₁ m₂ := by
    change c • x.1 _ = 0
    rw [h, smul_zero]

def embArch {a : ℕ} (e : Fin a ↪ Fin n) : archGroup K a →* archGroup K n where
  toFun x := ⟨emb (R := mixedSpace K) e x.1, Subgroup.mem_top _⟩
  map_one' := Subtype.ext (map_one (emb (R := mixedSpace K) e))
  map_mul' x y := Subtype.ext (map_mul (emb (R := mixedSpace K) e) x.1 y.1)

def ctSp (r : ℕ) (S : Submodule ℂ (archSmooth K n)) : Submodule ℂ (archSmooth K n) :=
  Submodule.span ℂ {ψ | ∃ φ ∈ S, ψ.1 = constantTerm r φ.1}

def slSp {a : ℕ} (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n)) (S : Submodule ℂ (archSmooth K n)) :
    Submodule ℂ (archSmooth K a) :=
  Submodule.span ℂ {f | ∃ ψ ∈ S, ∃ g ∈ Γ, ∀ m, f.1 m = ψ.1 (g * emb e m)}

end UpperTheory.V.Af.Fin

import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open Matrix GlobalTheory.PRep

namespace GlobalTheory.BZMir

section Group

variable (k : Type) [Field k]

def eLast (n : ℕ) : Fin (n + 1) → k := Pi.single (Fin.last n) 1

def Mir (n : ℕ) : Subgroup (GL (Fin (n + 1)) k) where
  carrier := {g | vecMul (eLast k n) (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = eLast k n}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    rw [← vecMul_vecMul, ha, hb]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [vecMul_vecMul, Units.mul_inv, vecMul_one]

def colMat (n : ℕ) (v : Fin n → k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  fun i j => if j = Fin.last n then Fin.lastCases (0 : k) v i else 0

theorem colMat_mul_colMat (n : ℕ) (v w : Fin n → k) : colMat k n v * colMat k n w = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l = Fin.last n
  · subst hl
    simp [GlobalTheory.BZMir.colMat]
  · simp [GlobalTheory.BZMir.colMat, hl]

theorem colMat_add (n : ℕ) (v w : Fin n → k) : colMat k n (v + w) = colMat k n v + colMat k n w := by
  ext i j
  simp only [GlobalTheory.BZMir.colMat, Matrix.add_apply]
  split_ifs
  · cases i using Fin.lastCases <;> simp
  · simp

theorem colMat_zero (n : ℕ) : colMat k n 0 = 0 := by
  ext i j
  simp only [GlobalTheory.BZMir.colMat, Matrix.zero_apply]
  split_ifs
  · cases i using Fin.lastCases <;> simp
  · rfl

def unip (n : ℕ) : Multiplicative (Fin n → k) →* GL (Fin (n + 1)) k where
  toFun v := ⟨1 + colMat k n v.toAdd, 1 - colMat k n v.toAdd,
    by simp only [add_mul, mul_sub, one_mul, mul_one, colMat_mul_colMat]; abel,
    by simp only [sub_mul, mul_add, one_mul, mul_one, colMat_mul_colMat]; abel⟩
  map_one' := by
    ext1
    simp [colMat_zero]
  map_mul' v w := by
    ext1
    simp only [toAdd_mul, colMat_add, Units.val_mul, mul_add, add_mul, one_mul, mul_one, colMat_mul_colMat, add_zero]
    abel

theorem unip_apply_castSucc_last (n : ℕ) (v : Multiplicative (Fin n → k)) (i : Fin n) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n) =
      v.toAdd i := by
  change (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) (Fin.castSucc i) (Fin.last n) = _
  simp [GlobalTheory.BZMir.colMat, Matrix.one_apply_ne (Fin.castSucc_ne_last i)]

theorem unip_injective (n : ℕ) : Function.Injective (unip k n) := by
  intro v w hvw
  apply Multiplicative.toAdd.injective
  funext i
  have hi := congrArg
    (fun g : GL (Fin (n + 1)) k => (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n)) hvw
  simpa only [GlobalTheory.BZMir.unip_apply_castSucc_last] using hi

def MirU (n : ℕ) : Subgroup (GL (Fin (n + 1)) k) := (unip k n).range

def unipEquiv (n : ℕ) : Multiplicative (Fin n → k) ≃* MirU k n := MonoidHom.ofInjective (unip_injective k n)

theorem vecMul_eLast (n : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : vecMul (eLast k n) M = M (Fin.last n) := by
  ext j
  simp [GlobalTheory.BZMir.eLast, Matrix.vecMul, dotProduct, Pi.single_apply]

theorem MirU_le_Mir (n : ℕ) : MirU k n ≤ Mir k n := by
  rintro _ ⟨v, rfl⟩
  change vecMul (GlobalTheory.BZMir.eLast k n)
    ((GlobalTheory.BZMir.unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      GlobalTheory.BZMir.eLast k n
  rw [GlobalTheory.BZMir.vecMul_eLast]
  ext j
  change (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) (Fin.last n) j = GlobalTheory.BZMir.eLast k n j
  by_cases h : j = Fin.last n
  · subst h
    simp [GlobalTheory.BZMir.colMat, GlobalTheory.BZMir.eLast]
  · simp [GlobalTheory.BZMir.colMat, GlobalTheory.BZMir.eLast, Matrix.one_apply_ne (Ne.symm h), h, Pi.single_apply]

def glEmbMat (n : ℕ) (A : Matrix (Fin n) (Fin n) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  fun i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j) (fun i' => Fin.lastCases 0 (fun j' => A i' j') j) i

theorem glEmbMat_mul (n : ℕ) (A B : Matrix (Fin n) (Fin n) k) :
    glEmbMat k n (A * B) = glEmbMat k n A * glEmbMat k n B := by
  ext i j
  cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
    simp [GlobalTheory.BZMir.glEmbMat, Matrix.mul_apply, Fin.sum_univ_castSucc]

theorem glEmbMat_one (n : ℕ) : glEmbMat k n 1 = 1 := by
  ext i j
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last => simp [GlobalTheory.BZMir.glEmbMat]
    | cast b => simp [GlobalTheory.BZMir.glEmbMat, Matrix.one_apply_ne (Fin.castSucc_ne_last b).symm]
  | cast a =>
    cases j using Fin.lastCases with
    | last => simp [GlobalTheory.BZMir.glEmbMat, Matrix.one_apply_ne (Fin.castSucc_ne_last a)]
    | cast b => simp [GlobalTheory.BZMir.glEmbMat, Matrix.one_apply]

def glEmbHom (n : ℕ) : Matrix (Fin n) (Fin n) k →* Matrix (Fin (n + 1)) (Fin (n + 1)) k where
  toFun := glEmbMat k n
  map_one' := glEmbMat_one k n
  map_mul' := glEmbMat_mul k n

def glEmb (n : ℕ) : GL (Fin n) k →* GL (Fin (n + 1)) k := Units.map (glEmbHom k n)

theorem glEmb_mem_Mir (n : ℕ) (g : GL (Fin n) k) : glEmb k n g ∈ Mir k n := by
  change vecMul (GlobalTheory.BZMir.eLast k n) (GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k)) =
    GlobalTheory.BZMir.eLast k n
  rw [GlobalTheory.BZMir.vecMul_eLast]
  ext j
  cases j using Fin.lastCases with
  | last => simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.eLast]
  | cast b => simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.eLast, Pi.single_apply, Fin.castSucc_ne_last]

end Group

section Twisted

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def twAct (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) {M : Type} [Group M] (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) :
    Representation ℂ M (TwJacquet ρ N θ) where
  toFun m := (twKer ρ N θ).mapQ (twKer ρ N θ) (ρ (s m)) (by
    refine Submodule.span_le.2 ?_
    rintro w ⟨n, v, rfl⟩
    obtain ⟨h, hθ⟩ := hs m n
    refine Submodule.subset_span ⟨⟨_, h⟩, ρ (s m) v, ?_⟩
    rw [hθ, map_sub, map_smul]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group)
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp
    rfl

end Twisted

end GlobalTheory.BZMir

end

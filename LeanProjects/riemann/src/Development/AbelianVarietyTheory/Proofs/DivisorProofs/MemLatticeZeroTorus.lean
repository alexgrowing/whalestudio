import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps

noncomputable section

open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.EisRestrict

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem hE_eq_dot (x z : Fin n → E) : hE σ J x z = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ z) := by
  simp only [hE, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by simp [mul_assoc]

def hRight (x : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun z := hE σ J x z
  map_add' z z' := by simp only [hE_eq_dot, Matrix.mulVec_add, dotProduct_add]
  map_smul' c z := by simp only [hE_eq_dot, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, RingHom.id_apply]

variable {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)

def V0 : Submodule E (Fin n → E) :=
  LinearMap.ker (hRight σ J (GlobalTheory.EisMidHt.firstColumn X)) ⊓ LinearMap.ker (hRight σ J (GlobalTheory.EisMidHt.firstColumn Y))

theorem mem_invariant_forms {z : Fin n → E} :
    z ∈ V0 σ J X Y ↔ hE σ J (GlobalTheory.EisMidHt.firstColumn X) z = 0 ∧ hE σ J (GlobalTheory.EisMidHt.firstColumn Y) z = 0 := Iff.rfl

abbrev dim : ℕ := Module.finrank E (V0 σ J X Y)

def bas : Module.Basis (Fin (dim σ J X Y)) E (V0 σ J X Y) := Module.finBasis E _

def P : Matrix (Fin n) (Fin (dim σ J X Y)) E := Matrix.of fun i j => (bas σ J X Y j : Fin n → E) i

def ι : (Fin (dim σ J X Y) → E) →ₗ[E] (Fin n → E) := (P σ J X Y).mulVecLin

def J0 : Matrix (Fin (dim σ J X Y)) (Fin (dim σ J X Y)) E := Formalism.UG.cT (σ : E →+* E) (P σ J X Y) * J * P σ J X Y

def coordTail (Z : Matrix (Fin n) (Fin (r + 1)) E) : Matrix (Fin (dim σ J X Y)) (Fin r) E :=
  Matrix.of fun i j => Function.invFun (ι σ J X Y) (fun k => Z k j.succ) i

abbrev X0 : Matrix (Fin (dim σ J X Y)) (Fin r) E := coordTail σ J X Y X

abbrev Y0 : Matrix (Fin (dim σ J X Y)) (Fin r) E := coordTail σ J X Y Y

def L0 (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin (dim σ J X Y) → E) :=
  L.comap ((ι σ J X Y).restrictScalars (𝓞 E))

theorem mem_lattice_zeroTorus {L : Submodule (𝓞 E) (Fin n → E)} {u : Fin (dim σ J X Y) → E} :
    u ∈ L0 σ J X Y L ↔ P σ J X Y *ᵥ u ∈ L := Iff.rfl

theorem ι_apply (u : Fin (dim σ J X Y) → E) : ι σ J X Y u = P σ J X Y *ᵥ u := rfl

theorem ι_eq_sum (u : Fin (dim σ J X Y) → E) :
    ι σ J X Y u = ((∑ j, u j • bas σ J X Y j : V0 σ J X Y) : Fin n → E) := by
  funext i
  simp [ι, P, Matrix.mulVec, dotProduct, mul_comm]

theorem ι_mem (u : Fin (dim σ J X Y) → E) : ι σ J X Y u ∈ V0 σ J X Y := by
  rw [ι_eq_sum]; exact Submodule.coe_mem _

theorem ι_injective : Function.Injective (ι σ J X Y) := by
  intro u u' h
  rw [ι_eq_sum, ι_eq_sum] at h
  have h2 := congrArg (bas σ J X Y).repr (Subtype.ext h)
  funext j
  have := congrArg (· j) h2
  simpa [map_sum, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply] using this

theorem exists_ι_eq {z : Fin n → E} (hz : z ∈ V0 σ J X Y) : ∃ u, ι σ J X Y u = z :=
  ⟨fun j => (bas σ J X Y).repr ⟨z, hz⟩ j, by
    rw [ι_eq_sum, (bas σ J X Y).sum_repr ⟨z, hz⟩]⟩

theorem ι_coordTail (Z : Matrix (Fin n) (Fin (r + 1)) E) (j : Fin r) (hZ : (fun k => Z k j.succ) ∈ V0 σ J X Y) :
    ι σ J X Y (fun i => coordTail σ J X Y Z i j) = fun k => Z k j.succ :=
  Function.invFun_eq (exists_ι_eq σ J X Y hZ)

theorem hE_J0 (u u' : Fin (dim σ J X Y) → E) :
    hE σ (J0 σ J X Y) u u' = hE σ J (ι σ J X Y u) (ι σ J X Y u') := by
  simp only [hE_eq_dot, J0, ι_apply, Formalism.UG.cT, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  congr 1
  funext i
  simp [Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, mul_comm]

end GlobalTheory.EisRestrict

end

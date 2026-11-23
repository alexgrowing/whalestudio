import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasKHW

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DiracK

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι]

def lft (ι : Type) [Fintype ι] [DecidableEq ι] : Module.End ℂ V →ₐ[ℂ] Module.End ℂ (ι → V) where
  toFun T :=
    { toFun := fun x i => T (x i)
      map_add' := fun x y => by funext i; simp
      map_smul' := fun s x => by funext i; simp }
  map_one' := by ext x i; simp
  map_mul' S T := by ext x i; simp
  map_zero' := by ext x i; simp
  map_add' S T := by ext x i; simp
  commutes' s := by ext x i; simp [Module.algebraMap_end_apply]

def rgt (V : Type) [AddCommGroup V] [Module ℂ V] : Matrix ι ι ℂ →ₐ[ℂ] Module.End ℂ (ι → V) where
  toFun M :=
    { toFun := fun x i => ∑ j, M i j • x j
      map_add' := fun x y => by funext i; simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun s x => by
        funext i
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _ }
  map_one' := by
    ext x i
    simp [Matrix.one_apply]
  map_mul' M N := by
    apply LinearMap.ext
    intro x
    funext i
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum,
      smul_smul]
    exact Finset.sum_comm
  map_zero' := by ext x i; simp
  map_add' M N := by
    apply LinearMap.ext
    intro x
    funext i
    simp [add_smul, Finset.sum_add_distrib]
  commutes' s := by
    apply LinearMap.ext
    intro x
    funext i
    simp [Module.algebraMap_end_apply, Matrix.algebraMap_matrix_apply, ite_smul]

theorem lft_apply (T : Module.End ℂ V) (x : ι → V) (i : ι) : lft ι T x i = T (x i) := rfl

theorem rgt_apply (M : Matrix ι ι ℂ) (x : ι → V) (i : ι) : rgt V M x i = ∑ j, M i j • x j := rfl

theorem lft_mul_rgt (T : Module.End ℂ V) (M : Matrix ι ι ℂ) : lft ι T * rgt V M = rgt V M * lft ι T := by
  apply LinearMap.ext
  intro x
  funext i
  simp [lft_apply, rgt_apply, map_sum]

theorem yF_eq (Kf : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) :
    yF Kf c a b = lft ι (Kf a b) + rgt V (spinM c a b) := rfl

def dirac (P : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix ι ι ℂ) : Module.End ℂ (ι → V) :=
  ∑ a, ∑ b, lft ι (P a b) * rgt V (c b a)

end GlobalTheory.CompanionTheory.DiracK

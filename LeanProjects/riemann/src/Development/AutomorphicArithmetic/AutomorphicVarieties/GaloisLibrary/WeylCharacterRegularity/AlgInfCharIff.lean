import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasCohomology
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProjectionCompact

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh

namespace UpperTheory.V.WeylC

section Kron

variable {T κ : Type} [Fintype T] [DecidableEq T] [Fintype κ] [DecidableEq κ]

noncomputable def piK : (T → Matrix κ κ ℂ) →* Matrix (T → κ) (T → κ) ℂ :=
  _root_.UpperTheory.Reformulated.B.ProjectionCompact.piK

theorem piK_apply (A : T → Matrix κ κ ℂ) (f g : T → κ) : piK A f g = ∏ t, A t (f t) (g t) := rfl

theorem piK_mulSingle (t : T) (A : Matrix κ κ ℂ) (f g : T → κ) :
    piK (Pi.mulSingle t A) f g = A (f t) (g t) * ∏ s ∈ Finset.univ.erase t, (1 : Matrix κ κ ℂ) (f s) (g s) := by
  rw [piK_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ t), Pi.mulSingle_eq_same]
  congr 1
  exact Finset.prod_congr rfl fun s hs => by rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hs)]

def intersection_update_fsHerm_neg_one (t : T) : Matrix κ κ ℂ →ₐ[ℂ] Matrix (T → κ) (T → κ) ℂ :=
  AlgHom.ofLinearMap
    { toFun := fun A => piK (Pi.mulSingle t A)
      map_add' := fun A B => by ext f g; simp [piK_mulSingle, add_mul]
      map_smul' := fun c A => by ext f g; simp [piK_mulSingle, mul_assoc] }
    (by simp) (fun A B => by simp [Pi.mulSingle_mul])

theorem position_apply (t : T) (A : Matrix κ κ ℂ) (f g : T → κ) :
    intersection_update_fsHerm_neg_one t A f g = A (f t) (g t) * ∏ s ∈ Finset.univ.erase t, (1 : Matrix κ κ ℂ) (f s) (g s) :=
  piK_mulSingle t A f g

end Kron

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ι κ : Type}

def IsReg (M : GL (Fin a) (Cinf E) → Matrix ι κ ℂ) : Prop := ∀ i j, (fun y => M y i j) ∈ regFun E a

def dOf (M : GL (Fin a) (Cinf E) → Matrix ι κ ℂ) (X : Lie E a) : Matrix ι κ ℂ :=
  Matrix.of fun i j => fderiv ℝ (extGL fun y => M y i j) (oneL E a) X

def eOf (M : GL (Fin a) (Cinf E) → Matrix ι κ ℂ) (τ : E →+* ℂ) (i j : Fin a) : Matrix ι κ ℂ :=
  (1 / 2 : ℂ) • (dOf M (toL (Matrix.single i j (atEmb τ 1))) - Complex.I • dOf M (toL (Matrix.single i j (atEmb τ Complex.I))))

theorem dmat_eq (Ξ : AlgRep E a) (X : Lie E a) : Ξ.dmat X = dOf Ξ.mat X := rfl

theorem algInfChar_iff (Ξ : AlgRep E a) (τ : E →+* ℂ) (m : Multiset ℂ) :
    UpperTheory.V.Af.AlgInfChar Ξ τ m ↔ Multiset.card m = a ∧ ∀ u : ℂ, Formalism.REAL.qdet (eOf Ξ.mat τ) (u + ((a : ℂ) - 1) / 2) =
      (m.map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) := Iff.rfl

end UpperTheory.V.WeylC

import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeIndex

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open scoped TensorProduct

def IsSelfDualLat {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (N : Submodule (𝓞 E) (n → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧ Submodule.span E (N : Set (n → E)) = ⊤ ∧
    (N : Set (n → E)) = dualSet σ J N

def IsSelfDualDefiniteLattice (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) : Prop :=
  letI := D.host.cmStar
  IsSelfDualLat (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N

def stabHat (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  levelAfL D.sp.cm.sig D.sp.gram0 N

def levelU (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  (Lv u).U

def IndexAt (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  (∀ i : Fin 2, SplitsF D (D.host.g i)) → SplitsF D (D.mem u).A.T →
    ∀ N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E), IsSelfDualDefiniteLattice D N →
      levelU D Lv u ≤ stabHat D N →
      (((levelU D Lv u).relIndex (stabHat D N) : ℕ) : ℝ) =
        idxPi D (D.host.g 0) (D.host.g 1) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f

def StabiliserLevelIndexFormula : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), IndexAt D Lv u

def ExistsOverBase : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), SplitsF D (D.mem u).A.T →
    ∃ N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E), IsSelfDualDefiniteLattice D N ∧
      (letI := D.host.cmStar; (Lv u).Lb) ≤ N ∧ levelU D Lv u ≤ stabHat D N

theorem factorT_pos (D : D7) (u : D.what₂.Word) :
    0 < (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f := by
  have hT : (1 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.one_lt
  have hk : D.R.k ≠ 0 := by
    have := D.R.m_add_three_le_k
    omega
  have hTk : (1 : ℝ) < ((D.mem u).A.T : ℝ) ^ D.R.k := one_lt_pow₀ hT hk
  exact pow_pos (by linarith) _

theorem stabHat_le (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) :
    letI := D.host.cmStar
    stabHat D N ≤ UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  intro g hg
  unfold stabHat levelAfL level at hg
  exact (Subgroup.mem_inf.mp hg).1

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeIndex

end

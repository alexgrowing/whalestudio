import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalRingCardinality.DataRows

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts

open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def eps (i : N.Loc) : G H.E N.Om →* (N.O i)ˣ :=
  (Units.map (algebraMap ℤ_[N.l i] (N.O i)).toMonoidHom).comp
    (cycZ (F := H.E) (Ω := N.Om) (N.l i))

def IsRankPart (i : N.Loc) (x : N.X i) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))) ∧
  IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ) ∧
  ∀ w, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
    ((ρ σ : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)).charpoly *
        ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)) =
      heckePol N i x w

def matW (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om) :
    Matrix (Fin R.r) (Fin R.r) (Kf N i) :=
  ((((N.chi i 1 g)⁻¹ : (N.O i)ˣ) : N.O i) •
    ((ρ g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))).map
      (algebraMap (N.O i) (Kf N i))

def matT (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om) :
    Matrix (Fin R.r) (Fin R.r) (Kf N i) :=
  algebraMap (N.O i) (Kf N i) ((eps N i g : (N.O i)ˣ) : N.O i) • (matW N i ρ g⁻¹)ᵀ

def NoInv {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (D : Subgroup Γ)
    (M : Γ → Matrix (Fin a) (Fin a) K) : Prop :=
  ∀ v : Fin a → K, (∀ g ∈ D, (M g).mulVec v = v) → v = 0

def NoLocalInv (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  ∀ w : PlE H, NoInv (Dec (F := H.E) (N.plOm.1 w)) (matW N i ρ) ∧
    NoInv (Dec (F := H.E) (N.plOm.1 w)) (matT N i ρ)

def IsCuspPoint (i : N.Loc) (x : N.X i) : Prop :=
  x ∈ ZN N A i ∧ ∃ Sig, HasParamX N A i x Sig ∧ IsCuspIso N A Sig

def NoLocalInvCusp : Prop :=
  ∀ (i : N.Loc) (x : N.X i), IsCuspPoint N A i x →
    ∀ ρ, IsRankPart N i x ρ → NoLocalInv N i ρ

def NoLocalInvGood : Prop :=
  ∀ (i : N.Loc) (x : N.X i), x ∈ ZgoodN N A i →
    ∀ ρ, IsRankPart N i x ρ → NoLocalInv N i ρ

def NoLocalInvariants : Prop :=
  ∀ (i : N.Loc) (x : N.X i), (IsCuspPoint N A i x ∨ x ∈ ZgoodN N A i) →
    ∀ ρ, IsRankPart N i x ρ → NoLocalInv N i ρ

theorem matW_mul (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g h : G H.E N.Om) :
    matW N i ρ (g * h) = matW N i ρ g * matW N i ρ h := by
  unfold matW
  rw [← Matrix.map_mul, smul_mul_smul_comm, map_mul, map_mul, mul_inv, Units.val_mul, Units.val_mul]

theorem matW_one (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : matW N i ρ 1 = 1 := by
  simp [matW]

theorem matT_transpose_mul_matW (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i))
    (g : G H.E N.Om) :
    (matT N i ρ g)ᵀ * matW N i ρ g =
      algebraMap (N.O i) (Kf N i) ((eps N i g : (N.O i)ˣ) : N.O i) • (1 : Matrix _ _ (Kf N i)) := by
  unfold matT
  rw [Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.smul_mul, ← matW_mul, inv_mul_cancel,
    matW_one]

end GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts

import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIso
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryKFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviSubmoduleDense
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocSizeBlocks
import Formalism.SharpRestriction.CuspSpanNormBounds.SchurRelationsDiscreteSeries
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.THProvA

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.HCSide

section Circle

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def circleSpace (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (m : ℤ) : Submodule ℂ H where
  carrier := {x | ∀ z : ℂ, ‖z‖ = 1 → π (z • (1 : Matrix (Fin n) (Fin n) ℂ)) x = z ^ m • x}
  zero_mem' := fun z _ => by simp
  add_mem' := fun {x y} hx hy z hz => by rw [map_add, hx z hz, hy z hz, smul_add]
  smul_mem' := fun c x hx z hz => by rw [map_smul, hx z hz, smul_comm]

theorem mem_circleSpace {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {m : ℤ} {x : H} :
    x ∈ circleSpace π m ↔ ∀ z : ℂ, ‖z‖ = 1 → π (z • (1 : Matrix (Fin n) (Fin n) ℂ)) x = z ^ m • x := Iff.rfl

theorem isClosed_circleSpace (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (m : ℤ) :
    IsClosed (circleSpace π m : Set H) := by
  have : (circleSpace π m : Set H) =
      ⋂ z : ℂ, ⋂ _ : ‖z‖ = 1, {x | π (z • (1 : Matrix (Fin n) (Fin n) ℂ)) x = z ^ m • x} := by
    ext x; simp [mem_circleSpace]
  rw [this]
  exact isClosed_iInter fun z => isClosed_iInter fun _ =>
    isClosed_eq (π _).continuous (continuous_const_smul _)

instance [CompleteSpace H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (m : ℤ) :
    CompleteSpace (circleSpace π m) :=
  (isClosed_circleSpace π m).completeSpace_coe

def subRep (L : Submodule ℂ H) [L.HasOrthogonalProjection] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (g : Matrix (Fin n) (Fin n) ℂ) : L →L[ℂ] L :=
  L.orthogonalProjection ∘L π g ∘L L.subtypeL

end Circle

section Blocks

variable {n : ℕ} {ι : Type} [Fintype ι]

structure CentralBlocks (G : Set (Matrix (Fin n) (Fin n) ℂ)) (P D : ι → Matrix (Fin n) (Fin n) ℂ) : Prop where

  lin : IsLinRed G

  closed : IsClosed G

  polar : ∀ g ∈ G, ∃ X Y : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) ∧
    (∀ t : ℝ, NormedSpace.exp (t • Y) ∈ G) ∧ g = NormedSpace.exp X * NormedSpace.exp Y

  proj_isHermitian : ∀ l, (P l)ᴴ = P l

  P_idem : ∀ l, P l * P l = P l

  P_ne : ∀ l, P l ≠ 0

  P_comm : ∀ l, ∀ g ∈ G, P l * g = g * P l

  det_norm : ∀ l, ∀ g ∈ G, ‖(1 - P l + P l * g).det‖ = 1

  D_idem : ∀ l, D l * D l = D l

  D_orth : ∀ l k, l ≠ k → D l * D k = 0

  D_sum : ∑ l, D l = 1

  D_comm : ∀ l, ∀ g ∈ G, D l * g = g * D l

  PD : ∀ l, P l * D l = P l

  PD_ne : ∀ l k, l ≠ k → P l * D k = 0

  scal_mem : ∀ c : ι → ℂ, (∀ l, ‖c l‖ = 1) → ∑ l, c l • D l ∈ G

  centre : ∀ z ∈ G, (∀ g ∈ G, z * g = g * z) → ∃ c : ι → ℂ, z = ∑ l, c l • D l

def derivedLie (G : Set (Matrix (Fin n) (Fin n) ℂ)) (P : ι → Matrix (Fin n) (Fin n) ℂ) :
    Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | (∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) ∧ ∀ l, (P l * X).trace = 0}

def derivedWords (G : Set (Matrix (Fin n) (Fin n) ℂ)) (P : ι → Matrix (Fin n) (Fin n) ℂ) :
    Set (Matrix (Fin n) (Fin n) ℂ) :=
  {g | ∃ L : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ L, X ∈ derivedLie G P) ∧
    g = (L.map fun X => NormedSpace.exp X).prod}

def derivedGroup (G : Set (Matrix (Fin n) (Fin n) ℂ)) (P : ι → Matrix (Fin n) (Fin n) ℂ) :
    Set (Matrix (Fin n) (Fin n) ℂ) :=
  closure (derivedWords G P)

section Exp

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

end Exp

end Blocks

section Levi

variable {n a : ℕ}

def projOf (V : Submodule ℂ (Fin n → ℂ)) : Matrix (Fin n) (Fin n) ℂ :=
  Classical.choose (GlobalTheory.IsoTorus.exists_proj V)

variable (ε : Fin n → Bool)

def blkP (W : Flag n a) (i : Fin a) : Matrix (Fin n) (Fin n) ℂ := projOf (W i.succ) - projOf (W i.castSucc)

def blkC (W : Flag n a) : Matrix (Fin n) (Fin n) ℂ :=
  1 - projOf (W (Fin.last a)) - Jm ε * projOf (W (Fin.last a)) * Jm ε

def levP (W : Flag n a) : Option (Fin a) → Matrix (Fin n) (Fin n) ℂ
  | some i => blkP W i
  | none => blkC ε W

def levD (W : Flag n a) : Option (Fin a) → Matrix (Fin n) (Fin n) ℂ
  | some i => blkP W i + Jm ε * blkP W i * Jm ε
  | none => blkC ε W

end Levi

end GlobalTheory.CompanionTheory.HCSide

end

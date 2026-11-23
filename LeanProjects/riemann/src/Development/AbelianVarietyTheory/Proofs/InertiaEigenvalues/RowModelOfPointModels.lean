import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCharpolyCoeffOfMatrix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntSubMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting

noncomputable section

namespace GlobalTheory.RowModelRoad

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.BlockComplement GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple

section Twist

variable {Γ O : Type} [Group Γ] [CommRing O] {n : ℕ}

def twistRep (ψ : Γ →* Oˣ) (ρ : Γ →* GL (Fin n) O) : Γ →* GL (Fin n) O :=
  MonoidHom.toHomUnits
    { toFun := fun g => ((ψ g : Oˣ) : O) • ((ρ g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)
      map_one' := by simp
      map_mul' := fun g h => by simp [smul_smul, mul_comm] }

theorem coe_twistRep (ψ : Γ →* Oˣ) (ρ : Γ →* GL (Fin n) O) (g : Γ) :
    ((twistRep ψ ρ g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) =
      ((ψ g : Oˣ) : O) • ((ρ g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := rfl

end Twist

section Lift

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

end Lift

section Eig

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N) (i : N.Loc)

theorem frobEig_block (θ : A.CG 1) (t : ℕ) (w : PlE H) (b : ℂ) (hu : A.unr (A.locG θ w))
    (hb : A.frobEig (A.locG θ w) = {b}) :
    A.unr (spehLoc N A ⟨1, θ, t⟩ w) ∧ A.frobEig (spehLoc N A ⟨1, θ, t⟩ w) =
      ((List.range t : List ℕ) : Multiset ℕ).map
        fun k : ℕ => b * ((normV w : ℕ) : ℂ) ^ (((((t : ℝ) - 1) / 2 - k : ℝ)) : ℂ) := by
  unfold spehLoc
  dsimp only
  induction List.range t with
  | nil => exact ⟨A.lpZero_unr w, by simp [A.frobEig_zero]⟩
  | cons k l ih =>
    have h1 := (A.unr_tw _ (((t : ℝ) - 1) / 2 - k)).2 hu
    refine ⟨(A.unr_sum _ _).2 ⟨h1, ih.1⟩, ?_⟩
    refine (A.frobEig_sum _ _ h1 ih.1).trans ?_
    rw [ih.2, A.frobEig_tw _ _ hu, hb]
    simp

end Eig

def RowLift (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ →
    ∃ (P : D.naut.AV i) (π : D.naut.CG D.R.r), thetaOf D.nd D.naut i σ P ∧ D.naut.csd π ∧ D.naut.ralg π ∧
      HasParamW D.nd D.naut i σ [⟨D.R.r, π, 1⟩] ∧
      IsBCV D.nd D.naut i P (twistIso D.nd D.naut ([⟨D.R.r, π, 1⟩] ++ [muPart D.nd D.naut i]) D.naut.etaTinv)

def AllMaximal (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (P : D.naut.AV i), ∃ (i' : D.nd.Loc) (P' : D.naut.AV i') (x : D.nd.X i'),
    D.nd.w i' = D.nd.w i ∧
    (⟨D.nd.j i', D.nbc.embAV i' P'⟩ : Σ j, D.nbc.AU j) = ⟨D.nd.j i, D.nbc.embAV i P⟩ ∧ D.naut.ptV i' P' = some x

def LocFree (D : D7) : Prop :=
  ∀ i i' : D.nd.Loc, D.nd.j i' = D.nd.j i → D.nd.w i' = D.nd.w i →
    D.naut.muC i' = D.naut.muC i ∧ ∀ σ w, IsSplitPl D.host w → D.naut.locW i' σ w = D.naut.locW i σ w

def EtaValues (D : D7) : Prop :=
  ∀ w : PlE D.host, ∀ a ∈ D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaT w) (1 / 2)),
    ∃ y : D.what₂.LL, D.what₂.embLL y = a

def PointModels (D : D7) : Prop := ∀ (i : D.nd.Loc) (x : D.nd.X i), ∃ r, IsHeckeGalois D.nd i x r

variable {D : D7}

end GlobalTheory.RowModelRoad

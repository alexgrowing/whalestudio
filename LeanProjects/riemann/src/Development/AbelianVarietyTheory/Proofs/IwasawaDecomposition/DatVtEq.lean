import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn

section Cut

variable {G Γ : Type} [Group G] [Group Γ] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

def cutSp (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (Q : Subgroup G) (ch : Q →* ℂˣ)
    {G₀ : Type} [Group G₀] (red : Q →* G₀) (P : Subgroup G₀) (ψ : P →* ℂˣ) : Submodule ℂ (G → W) :=
  Bridge.AdForms ι ρ J χ ⊓
    { carrier := {F | ∀ (κ : Q) (hκ : red κ ∈ P) (h : G), F (h * κ) = ((ch κ * ψ ⟨red κ, hκ⟩ : ℂˣ) : ℂ) • F h}
      add_mem' := fun {F F'} hF hF' κ hκ h => by simp only [Pi.add_apply, hF κ hκ h, hF' κ hκ h, smul_add]
      zero_mem' := fun κ hκ h => by simp
      smul_mem' := fun c F hF κ hκ h => by simp only [Pi.smul_apply, hF κ hκ h]; rw [smul_comm] }

def lvlForm {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G₀ : Type} [Group G₀] [Fintype G₀]
    (r : Representation K G₀ S.Forms) (P : Subgroup G₀) (ψ : P →* Kˣ) (x : Fin (S.lvlDim r P ψ) → K) : S.Forms :=
  S.basis.equivFun.symm ((S.lvlE r P ψ).mulVec x)

end Cut

variable {D : D7}

variable (D) in

def km (n : ℕ) : Formalism.AUTREP.GAf D.host.E n →* GL (Fin n) (EAf D) := (ReciprocityTheory.Aut.GA D.host.E n).subtype

def stdJ {n : ℕ} (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n) : Subgroup (Formalism.AUTREP.GAf D.host.E n) :=
  (Formalism.L2.DIV.lev D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) 1 Ld).comap (km D n)

def stdX {n : ℕ} (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n) : stdJ Ld →* ℂˣ :=
  (Formalism.L2.DIV.levChar D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) 1 Ld).comp ((km D n).subgroupComap _)

variable (D) in

def datV (n : ℕ) (hr : D.R.r ≤ n) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ)
    (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Formalism.L2.DIV.LevDat D.host.E ℂ n :=
  datY n D.R.r D.R.t 1 hr Pg Q P (fun _ => chi) xi Frm.A

def UnitFr {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) : Prop := ∀ κ, finE V (P.ψ κ) = km D V.rank κ

def toGf {V : HSp D} {n : ℕ} (P : principalLevelFrame.RowPsi V n) : Formalism.AUTREP.GAf D.host.E n →* Bridge.Gf V :=
  (finHom V).rangeRestrict.comp P.ψ

def RatIso {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V) : Prop :=
  ∀ γ : ReciprocityTheory.Aut.GQ D.host.E V.rank, Bridge.ratF V (e γ) = toGf P γ.1 ∧
    ∀ γ₀ : GL (Fin V.rank) D.host.E,
      (γ.1.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) =
        (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map Algebra.TensorProduct.includeLeftRingHom →
      Bridge.IsRatMat V (e γ) γ₀

def wtRep {V : HSp D} {n : ℕ} (c : CoefA V) (e : ReciprocityTheory.Aut.GQ D.host.E n ≃* Formalism.L2.Theta.GQ V) :
    Representation ℂ (ReciprocityTheory.Aut.GQ D.host.E n) c.W :=
  c.coef.ρ.comp e.toMonoidHom

end GlobalTheory.MtIn

end

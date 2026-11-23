import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix GlobalTheory.MixModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

variable {D : D7}

abbrev VA (S : HSp D) : Type := Fin S.rank → AE D

def form (S : HSp D) (u v : VA S) : AE D := (fun i => cA D (v i)) ⬝ᵥ (gA S *ᵥ u)

def act (S : HSp D) (g : GA D S) (y : VA S) : VA S := mt S g *ᵥ y

def transv (S : HSp D) (w v : VA S) (y : VA S) : VA S :=
  y + form S y v • w - form S y w • v - (half D * form S v v * form S y w) • w

def IsTransv (S : HSp D) (w v : VA S) (g : GA D S) : Prop := ∀ y, act S g y = transv S w v y

def vecX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : Fin ρ → AE D) : VA S := d.jX *ᵥ a

def ratVec {n : ℕ} (a : Fin n → D.host.E) : Fin n → AE D := fun i => incA D (a i)

def TransvUnitary (D : D7) : Prop :=
  ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (a : Fin ρ → AE D) (v : VA S), form S (vecX d a) v = 0 →
    ∃ u : GA D S, IsTransv S (vecX d a) v u

def TransvConj (D : D7) : Prop :=
  ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (a : Fin ρ → AE D) (v : VA S), form S (vecX d a) v = 0 →
    ∀ u g : GA D S, IsTransv S (vecX d a) v u → IsTransv S (act S g (vecX d a)) (act S g v) (g * u * g⁻¹)

def TransvProd (D : D7) : Prop :=
  ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (a : Fin ρ → AE D) (v v' : VA S), form S (vecX d a) v = 0 →
    form S (vecX d a) v' = 0 → ∀ u u' u'' : GA D S, IsTransv S (vecX d a) v u → IsTransv S (vecX d a) v' u' →
      IsTransv S (vecX d a) (v + v') u'' →
        ∃ (κ : AE D) (c : skewA D ρ), c.1 = κ • vecMulVec a (fun j => cA D (a j)) ∧ u * u' = u'' * d.nC c

def TransvTrivial (D : D7) : Prop :=
  ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 →
    ∀ (a : Fin ρ → D.host.E) (v : VA S), form S (vecX d (ratVec a)) v = 0 →
    ∀ u : GA D S, IsTransv S (vecX d (ratVec a)) v u →
    ∀ x : Mx D T.rank ρ, x *ᵥ ratVec a = 0 →
    ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
      d.mixS T ψ μ 𝓕 (om (u, 1) f) x = d.mixS T ψ μ 𝓕 f x

def TransvLemma (D : D7) : Prop := TransvUnitary D ∧ TransvConj D ∧ TransvTrivial D

theorem IsTransv.unique {S : HSp D} {w v : VA S} {g h : GA D S} (hg : IsTransv S w v g) (hh : IsTransv S w v h) :
    g = h := by
  refine mt_injective S (Matrix.ext_of_mulVec_single fun i => ?_)
  exact (hg _).trans (hh _).symm

example (S : HSp D) (w : VA S) : IsTransv S w 0 1 := by
  intro y
  simp [act, transv, form]

example (S : HSp D) (s : AE D) (u v : VA S) : form S (s • u) v = s * form S u v := by
  rw [form, form, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

end GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

end

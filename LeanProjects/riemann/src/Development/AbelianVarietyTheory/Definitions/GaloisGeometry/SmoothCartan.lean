import Mathlib
import GroundTheory.AutomorphicForms.GKModules.SmoothVectors
import GroundTheory.AutomorphicForms.GKModules.RightRegular
import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BasicForm

noncomputable section

open GlobalTheory.BorelCoh GroundTheory.Automorphic

namespace GlobalTheory.Mt

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

structure CartanData (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) where

  lie : IsExpLieAlgebra G 𝔤

  closed : IsClosed (G : Set 𝔸ˣ)

  K : Subgroup G
  compact : IsCompact (K : Set G)

  k : Submodule ℝ 𝔤

  p : Submodule ℝ 𝔤
  isCompl : IsCompl k p
  bracket_kk : ∀ X ∈ k, ∀ Y ∈ k, lie.bracket X Y ∈ k
  bracket_kp : ∀ X ∈ k, ∀ Y ∈ p, lie.bracket X Y ∈ p
  bracket_pp : ∀ X ∈ p, ∀ Y ∈ p, lie.bracket X Y ∈ k
  Ad_p : ∀ κ ∈ K, ∀ Y ∈ p, lie.Ad κ Y ∈ p
  expG_k : ∀ X ∈ k, lie.expG X ∈ K

  cartan : ∀ g : G, ∃! x : p × K, g = lie.expG (x.1 : 𝔤) * (x.2 : G)

  smooth_cartan : ∀ ℓ : 𝔤 →L[ℝ] ℂ, lie.IsSmoothFun (F := ℂ) fun g => ℓ ((cartan g).exists.choose.1 : 𝔤)

  B : LinearMap.BilinForm ℝ 𝔤
  B_symm : ∀ X Y, B X Y = B Y X
  B_Ad : ∀ g X Y, B (lie.Ad g X) (lie.Ad g Y) = B X Y
  B_p : ∀ X ∈ p, X ≠ 0 → 0 < B X X
  B_k : ∀ X ∈ k, X ≠ 0 → B X X < 0
  B_kp : ∀ X ∈ k, ∀ Y ∈ p, B X Y = 0

namespace CartanData

variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (D : CartanData G 𝔤)

def adP (κ : D.K) (Y : D.p) : D.p := ⟨D.lie.Ad (κ : G) Y, D.Ad_p κ κ.2 Y Y.2⟩

section Rel

variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]

def cocyc (L : D.p →ₗ[ℝ] Module.End ℂ M) (κ : D.K → Module.End ℂ M) (q : ℕ) :
    Submodule ℂ (D.p [⋀^Fin q]→ₗ[ℝ] M) :=
  Submodule.span ℂ {f | f ∈ relCo D.adP κ ⊤ q ∧ gd L f = 0}

def cobd (L : D.p →ₗ[ℝ] Module.End ℂ M) (κ : D.K → Module.End ℂ M) : (q : ℕ) → Submodule ℂ (D.p [⋀^Fin q]→ₗ[ℝ] M)
  | 0 => ⊥
  | q + 1 => Submodule.span ℂ (gd L '' relCo D.adP κ ⊤ q)

abbrev Hrel (L : D.p →ₗ[ℝ] Module.End ℂ M) (κ : D.K → Module.End ℂ M) (q : ℕ) : Type _ :=
  D.cocyc L κ q ⧸ (D.cobd L κ q).comap (D.cocyc L κ q).subtype

end Rel

section Unitary

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def toBanach (π : UnitaryRep G H) : BanachRep G H :=
  ⟨(unitary (H →L[ℂ] H)).subtype.comp π.toHom, fun v => π.continuous_orbit' v⟩

abbrev SmV (π : UnitaryRep G H) : Submodule ℂ H := D.lie.smoothVectors (toBanach π)

def dOp (π : UnitaryRep G H) (X : 𝔤) : Module.End ℂ (D.SmV π) where
  toFun v := ⟨D.lie.derivOp (toBanach π) X v, D.lie.isSmoothVector_derivOp (toBanach π) v.2 X⟩
  map_add' v w := Subtype.ext (D.lie.derivOp_add (toBanach π) v.2 w.2 X)
  map_smul' c v := Subtype.ext (D.lie.derivOp_smul (toBanach π) v.2 c X)

def gOp (π : UnitaryRep G H) (g : G) : Module.End ℂ (D.SmV π) :=
  ((toBanach π).toHom g : H →L[ℂ] H).toLinearMap.restrict fun v hv => D.lie.isSmoothVector_map (toBanach π) hv g

variable {d : ℕ}

def dξ (ξ : G →* Matrix (Fin d) (Fin d) ℂ) (X : 𝔤) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => D.lie.rightDeriv (F := ℂ) X (fun g => ξ g i j) 1

def tOp (π : UnitaryRep G H) (ξ : G →* Matrix (Fin d) (Fin d) ℂ) (X : 𝔤) : Module.End ℂ (Fin d → D.SmV π) :=
  LinearMap.pi fun i => (D.dOp π X).comp (LinearMap.proj i) + ∑ j, D.dξ ξ X i j • LinearMap.proj j

def gkL (π : UnitaryRep G H) (ξ : G →* Matrix (Fin d) (Fin d) ℂ) : D.p →ₗ[ℝ] Module.End ℂ (Fin d → D.SmV π) :=
  (Module.finBasis ℝ D.p).constr ℝ fun i => D.tOp π ξ ((Module.finBasis ℝ D.p) i : 𝔤)

def gkK (π : UnitaryRep G H) (ξ : G →* Matrix (Fin d) (Fin d) ℂ) (κ : D.K) : Module.End ℂ (Fin d → D.SmV π) :=
  LinearMap.pi fun i => ∑ j, ξ (κ : G) i j • (D.gOp π κ).comp (LinearMap.proj j)

abbrev HGK (π : UnitaryRep G H) (ξ : G →* Matrix (Fin d) (Fin d) ℂ) (q : ℕ) : Type _ :=
  D.Hrel (D.gkL π ξ) (D.gkK π ξ) q

end Unitary

end CartanData

end GlobalTheory.Mt

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory

namespace PDivGroup

open PDiv

variable {p : ℕ} {k : Type} [CommRing k]

def IsConn (G : PDivGroup p k) : Prop := ∀ n, ∀ a ∈ augIdeal k (G.A n), IsNilpotent a

def IsEt (G : PDivGroup p k) : Prop := ∀ n, IsReduced (G.A n)

end PDivGroup

def WittOn (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (P : PDivGroup p k → Prop) : Prop :=
  ∃ (M : {G // P G} → ModuleCat.{0} (WittVector p k))
    (map : ∀ G H : {G // P G}, (G.1 ⟶ H.1) →+ (M H →ₗ[WittVector p k] M G))
    (red : ∀ G : {G // P G},
      M G →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] G.1.RigExt),
    (∀ G : {G // P G}, Module.Free (WittVector p k) (M G) ∧ Module.Finite (WittVector p k) (M G) ∧
      Function.Surjective (red G) ∧ (∀ m, red G m = 0 ↔ ∃ n, m = p • n) ∧
      map G G (𝟙 G.1) = LinearMap.id) ∧
    (∀ (G H K : {G // P G}) (f : G.1 ⟶ H.1) (g : H.1 ⟶ K.1),
      map G K (f ≫ g) = map G H f ∘ₗ map H K g) ∧
    ∀ (G H : {G // P G}) (f : G.1 ⟶ H.1) (m : M H),
      red G (map G H f m) = PDivGroup.rigExtMap f (red H m)

end GlobalTheory

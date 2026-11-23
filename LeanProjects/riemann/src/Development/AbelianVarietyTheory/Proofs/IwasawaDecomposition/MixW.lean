import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRigFr

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.RayHoriz
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayRosEx

section Weights

variable {S : Type} [CommRing S] {ρ : Type}

def mixW (M : Fin 2 → Fin 3 → S) (W : Fin 2 → ρ → S) : Fin 3 → ρ → S := fun i r => ∑ k, M k i * W k r

def rat3 {U : Type} [CommGroup U] (E : (Fin 3 → ρ → S) → U) (α β : ρ → S) (M : Fin 2 → Fin 3 → S) : U :=
  E (mixW M ![α, fun _ => 1]) * (E (mixW M ![α, fun _ => 0]))⁻¹ * (E (mixW M ![fun _ => 0, fun _ => 1]))⁻¹ *
    (E (mixW M ![fun _ => 1, β]))⁻¹ * E (mixW M ![fun _ => 1, fun _ => 0]) * E (mixW M ![fun _ => 0, β])

def th3 {U : Type} [CommGroup U] (E : (Fin 3 → ρ → S) → U) (s : Fin 3 → ρ → S) : U :=
  ∏ I : Finset (Fin 3), E (fun i r => if i ∈ I then s i r else 0) ^ ((-1 : ℤ) ^ (3 - I.card))

def subL (M : Fin 2 → Fin 3 → S) (m : ℕ) : Jet S (Fin 2 × ρ) m →ₐ[S] Jet S (Fin 3 × ρ) m :=
  jetMap (fun p => ∑ i, MvPolynomial.C (M p.1 i) * MvPolynomial.X (i, p.2)) fun p =>
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (X_mem_orig (i, p.2))

def sc3 (s : Fin 3 → ρ → S) (m : ℕ) : Jet S (Fin 3 × ρ) m →ₐ[S] Jet S (Fin 3 × ρ) m :=
  jetScale fun p => s p.1 p.2

end Weights

end GlobalTheory.RayRosEx

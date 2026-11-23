import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedUniformization
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.ChartMono

section Mono

variable {R : Type} [CommRing R] [IsDomain R]

def TraitMono (Dg : DegPre R) (ℓ : LinearMap.BilinForm ℤ Dg.X →ₗ[ℤ] ℤ) (h : R) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (f : R →+* W)
    (be : LinearMap.BilinForm ℤ Dg.X), (∀ y z, be y z = be z y) → FormAt Dg f ϖ be →
    ∀ k : ℕ, (k : ℤ) = ℓ be → Associated (f h) (ϖ ^ k)

theorem TraitMono.mul {Dg : DegPre R} {ℓ ℓ' : LinearMap.BilinForm ℤ Dg.X →ₗ[ℤ] ℤ} {h h' : R}
    (H : TraitMono Dg ℓ h) (H' : TraitMono Dg ℓ' h') (hn : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W],
      CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (f : R →+* W) (be : LinearMap.BilinForm ℤ Dg.X), (∀ y z, be y z = be z y) →
      FormAt Dg f ϖ be → 0 ≤ ℓ be ∧ 0 ≤ ℓ' be) : TraitMono Dg (ℓ + ℓ') (h * h') := by
  intro W _ _ _ hW ϖ hϖ f be hs hf k hk
  obtain ⟨h1, h2⟩ := hn W hW ϖ hϖ f be hs hf
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le h1
  obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le h2
  have hk' : k = a + b := by
    have : (k : ℤ) = a + b := by rw [hk, LinearMap.add_apply, ha, hb]
    exact_mod_cast this
  rw [map_mul, hk', pow_add]
  exact (H W hW ϖ hϖ f be hs hf a ha.symm).mul_mul (H' W hW ϖ hϖ f be hs hf b hb.symm)

end Mono

section Cone

variable {X : Type} [AddCommGroup X]

def InRealCone {k : ℕ} (γ : Fin k → LinearMap.BilinForm ℤ X) (β : LinearMap.BilinForm ℤ X) : Prop :=
  ∃ c : Fin k → ℝ, (∀ i, 0 ≤ c i) ∧ toReal β = ∑ i, c i • toReal (γ i)

end Cone

end GlobalTheory.ChartMono

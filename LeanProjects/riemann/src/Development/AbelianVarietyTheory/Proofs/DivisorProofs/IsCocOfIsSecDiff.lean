import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem isCoc_of_isSecDiff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ), HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A, (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∀ u : Fn1 A, IsSecDiff n S u → IsCoc (whole A) u := by
  intro R _ A _ _ n hR b _ S _ u hu D _ _ D' _ _ D'' _ _ φ ψ x _
  obtain ⟨E, _, _, χ, z, hχ, hz⟩ := hR D'' (spOver ψ ≫ spOver φ ≫ x)
  apply hχ.injective
  change χ _ = χ (ψ _ + _)
  rw [map_add]
  have h1 := hu D D'' (ψ.comp φ) x E χ z (by rw [hz, ← spOver_comp, Category.assoc])
  have h2 := hu D D' φ x E (χ.comp ψ) z (by rw [hz, ← spOver_comp, Category.assoc])
  have h3 := hu D' D'' ψ (spOver φ ≫ x) E χ z hz
  rw [AlgHom.comp_apply] at h2
  rw [h1, h2, h3, ← spOver_comp, Category.assoc, AlgHom.comp_assoc]
  abel

end GlobalTheory.PtExt

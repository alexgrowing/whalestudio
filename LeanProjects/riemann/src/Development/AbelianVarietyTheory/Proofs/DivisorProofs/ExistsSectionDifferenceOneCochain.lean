import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePushoutTorsorSectionDifferenceStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem isSec_pull {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (n : ℕ) (b : Fn0 A)
    {D : Type} [CommRing D] [Algebra R D] {D' : Type} [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (x : Pt A D) (s : RootFn A D) (hs : IsSec n b x s) :
    IsSec n b (spOver φ ≫ x) (fun E _ _ ψ z ↦ s E (ψ.comp φ) z) := by
  refine ⟨?_, ?_⟩
  · intro E _ _ E' _ _ α β z hz
    have hz' : z ^ n = spOver (α.comp φ) ≫ x := by rw [hz, ← spOver_comp, Category.assoc]
    exact hs.1 E E' (α.comp φ) β z hz'
  · intro E _ _ α z w hz hw
    have hz' : z ^ n = spOver (α.comp φ) ≫ x := by rw [hz, ← spOver_comp, Category.assoc]
    exact hs.2 E (α.comp φ) z w hz' hw

theorem exists_isSecDiff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
    (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∃ u : Fn1 A, IsSecDiff n S u := by
  intro R _ A _ _ n hR b _ S hS
  have key : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (x : Pt A D), ∃ e : D', ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D' →ₐ[R] E)
        (z : Pt A E), z ^ n = spOver ψ ≫ spOver φ ≫ x →
          S D' (spOver φ ≫ x) E ψ z - S D x E (ψ.comp φ) z = ψ e :=
    fun D _ _ D' _ _ φ x ↦ (GlobalTheory.T.existsUnique_pushoutTorsorSection_difference R A n hR b D' (spOver φ ≫ x) (S D' (spOver φ ≫ x))
      (fun E _ _ ψ z ↦ S D x E (ψ.comp φ) z) (hS D' _) (isSec_pull n b φ x _ (hS D x))).exists
  refine ⟨fun D _ _ D' _ _ φ x ↦ Classical.choose (key D D' φ x), ?_⟩
  intro D _ _ D' _ _ φ x E _ _ ψ z hz
  exact (Classical.choose_spec (key D D' φ x) E ψ z hz).symm

end GlobalTheory.PtExt

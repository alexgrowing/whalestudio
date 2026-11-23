import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.HodgeBC_map
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsPowMulPowEqOfIsZeroCechH
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR

namespace PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC

section Alg

variable {k k' : Type} [CommRing k] [CommRing k'] [Algebra k k'] {J : Type} (e : Module.Basis J k k')
  {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k' N]

def bcSum (ψ : M →ₛₗ[algebraMap k k'] N) : (J →₀ M) →+ N :=
  Finsupp.liftAddHom fun j ↦ (DistribSMul.toAddMonoidHom N (e j)).comp ψ.toAddMonoidHom

theorem bcSum_single (ψ : M →ₛₗ[algebraMap k k'] N) (j : J) (m : M) :
    bcSum e ψ (Finsupp.single j m) = e j • ψ m :=
  Finsupp.liftAddHom_apply_single _ j m

def IsBC (ψ : M →ₛₗ[algebraMap k k'] N) : Prop := Function.Bijective (bcSum e ψ)

end Alg

def semiSl {R R' B B' : Type} [CommRing R] [CommRing R'] [CommRing B] [CommRing B'] [Algebra R B]
    [Algebra R' B'] {σ : R →+* R'} {α : B →+* B'} (h : SemiHom σ α) : B →ₛₗ[σ] B' where
  toFun := α
  map_add' := map_add α
  map_smul' := h

def P_basis : Prop :=
  ∀ (k k' : Type) [CommRing k] [CommRing k'] [Algebra k k'] (J : Type) (e : Module.Basis J k k')
    (M N : Type) [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k' N]
    (ψ : M →ₛₗ[algebraMap k k'] N), IsBC e ψ → ∀ (I : Type) (c : Module.Basis I k M),
      ∃ c' : Module.Basis I k' N, ∀ i, c' i = ψ (c i)

def P_equiv : Prop :=
  ∀ (k k' : Type) [CommRing k] [CommRing k'] [Algebra k k'] (J : Type) (e : Module.Basis J k k')
    (M N M₀ N₀ : Type) [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k' N]
    [AddCommGroup M₀] [Module k M₀] [AddCommGroup N₀] [Module k' N₀]
    (ψ : M →ₛₗ[algebraMap k k'] N) (E : M₀ ≃ₗ[k] M) (E' : N ≃ₗ[k'] N₀)
    (ψ₀ : M₀ →ₛₗ[algebraMap k k'] N₀), (∀ x, ψ₀ x = E' (ψ (E x))) → IsBC e ψ → IsBC e ψ₀

def P_cube : Prop :=
  ∀ (k k' : Type) [CommRing k] [CommRing k'] [Algebra k k'] (J : Type) (e : Module.Basis J k k')
    (ι : Type) [LinearOrder ι] [Finite ι] (A : Cube.{0} ι k) (B : Cube.{0} ι k')
    (ψ : Cube.SemiHom (algebraMap k k') A B), (∀ s : Finset ι, s.Nonempty → IsBC e (ψ.app s)) →
      ∀ p : ℕ, IsBC e (ψ.homology p)

def P_forms : Prop :=
  ∀ (k k' : Type) [CommRing k] [CommRing k'] [Algebra k k'] (J : Type) (e : Module.Basis J k k')
    (B B' : Type) [CommRing B] [CommRing B'] [Algebra k B] [Algebra k' B'] (α : B →+* B')
    (hα : SemiHom (algebraMap k k') α), IsBC e (semiSl hα) → ∀ j : ℕ, IsBC e (hα.mOm j)

def P_sections : Prop :=
  ∀ (k k' : Type) [Field k] [Field k'] [Algebra k k'] (J : Type) (e : Module.Basis J k k')
    (X X' : Scheme.{0}) (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X)
    (h : IsPullback g s' s (spMap (algebraMap k k'))) (V : X.Opens), IsAffineOpen V →
      IsBC e (semiSl (semiHom_appSecS h.w V))

def P_affine : Prop :=
  ∀ (k k' : Type) [Field k] [Field k'] (φ : k →+* k') (X X' : Scheme.{0}) (s : X ⟶ Sp k)
    (s' : X' ⟶ Sp k') (g : X' ⟶ X), IsPullback g s' s (spMap φ) → IsAffineHom g

def P_cover : Prop :=
  ∀ (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k) [IsProper s],
    ∃ (n : ℕ) (U : Fin n → X.Opens), ⨆ i, U i = ⊤ ∧
      ∀ S : Finset (Fin n), S.Nonempty → IsAffineOpen (⨅ i ∈ S, U i)

def P_omega : Prop :=
  ∀ (k k' : Type) [Field k] [Field k'] [Algebra k k'] (J : Type) (e : Module.Basis J k k')
    (X X' : Scheme.{0}) (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X)
    (h : IsPullback g s' s (spMap (algebraMap k k'))) (a : ℕ) (V : X.Opens), IsAffineOpen V →
      letI := algΓ s; letI := algΓ s'
      IsBC e (sectionsOn.mapOver (appTop_algebraMapS h.w) (omegaPullS h.w a) V)

def P_cech : Prop :=
  ∀ (k k' : Type) [Field k] [Field k'] [Algebra k k'] (X X' : Scheme.{0}) (s : X ⟶ Sp k)
    (s' : X' ⟶ Sp k') (g : X' ⟶ X) (hg : g ≫ s = s' ≫ spMap (algebraMap k k')) (a b : ℕ)
    [(Omega s a).IsQuasicoherent] [(Omega s' a).IsQuasicoherent] (n : ℕ) (U : Fin n → X.Opens)
    (hc : ⨆ i, U i = ⊤) (hU : ∀ S : Finset (Fin n), S.Nonempty → IsAffineOpen (⨅ i ∈ S, U i))
    (hc' : ⨆ i, g ⁻¹ᵁ U i = ⊤) (hU' : ∀ S : Finset (Fin n), S.Nonempty → IsAffineOpen (⨅ i ∈ S, g ⁻¹ᵁ U i)),
    letI := algΓ s; letI := algΓ s'
    ∀ y : cechH k (Omega s a) ⊤ U b,
      hodgePullS hg a b (cechHEquivCoh k hc hU (Omega s a) b y) =
        cechHEquivCoh k' hc' hU' (Omega s' a) b
          ((cechCubeMapOver ⊤ U (appTop_algebraMapS hg) (omegaPullS hg a)).homology b y)

end PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC

end

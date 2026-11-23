import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValuesDetOmegaDeltaUnitAffineOpens
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyValues_detOmega_delta_unit_affineOpens : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ →
  ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → IsLocallyNoetherian S →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → NzFib σ →
    (∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (ξ : Sp A ⟶ S),
      IsOpenImmersion ξ → ∀ [IsCommMonObj ((Over.pullback ξ).obj G)] (L' : RigLB ((Over.pullback ξ).obj G)) (σ' : L'.L.Sec)
      (x : KeyIn (FractionRing A)) (y : Fin x.P.g → (epsR A ⟶ (Over.pullback ξ).obj G)),
      LBIso (L.L.pull (pullback.fst G.hom ξ)) L'.L → SmoothOfRelativeDimension x.P.g ((Over.pullback ξ).obj G).hom →
      IsOpen (abLocus ((Over.pullback ξ).obj G)) → L'.IsSymmetric → PolOnAb ((Over.pullback ξ).obj G) L'.L →
      IsLieBasis y → NzFib σ' → KeyOn (algebraMap A (FractionRing A)) x ((Over.pullback ξ).obj G) L' σ' y →
      ∃ u : Aˣ, (κ (FractionRing A) x : FractionRing A) = algebraMap A (FractionRing A) u) →
    ∃ f : (VB.det (LieVB.omega G) g).ι → δ.ι → S.presheaf.stalk (genericPoint S),
      (∀ c i, ∀ x ∈ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i, ∃ (V : S.Opens) (_ : V ≤ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i)
        (_ : x ∈ V) (u : Γ(S, V)ˣ), ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f c i) ∧
      (∀ c c' i i' (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
        (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i'),
        f c i * S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) ^ 8 =
          S.presheaf.germ _ (genericPoint S) h1
            ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) ^ 4 * f c' i') := by
  first | exact @GlobalTheory.KeyValsGen.keyVals | exact GlobalTheory.KeyValsGen.keyVals | (intros; apply GlobalTheory.KeyValsGen.keyVals <;> assumption)

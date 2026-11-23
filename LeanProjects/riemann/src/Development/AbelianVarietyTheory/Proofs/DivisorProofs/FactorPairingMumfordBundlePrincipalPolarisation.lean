import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamPush
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPairingAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPairingDiagRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingKernelTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionMumfordBundlePolarisationStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem pairing_factor_mumford : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂) := by
  intro R _ _ _ hR D D' F hA A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi
  exact GlobalTheory.T.exists_finite_extension_mumford_bundle_polarisation R hR G
    (RetractGeneric.isAbelianScheme_generic R A' G' hG' U'.gen G hG inc pr hinc hpr hip) _
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb U'.LG.isLB _ _) _)
    (FactorSym.main R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)
    (factorPairing_add R hR D D' F A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)
    (factorPairing_diag_relAmple R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)
    (pairing_kernel_trivial R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)

end GlobalTheory.Mum

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AppCompEqZeroOfGermDvd
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtCancelNonzeroScalarStatement

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_sec_expandsAt_of_integral_family : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) [QuasiCompact G.hom], (∀ F : Fam D.toPre (FractionRing R) k, ∃ s : U.SecK k, U.Expands k s F) → ∀ (F : Fam D.toPre (FractionRing R) k) (f : ∀ α, D.toPre.SecB k α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α) (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left 1) → ∃ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))), ∀ e, U.ExpandsAt e k σ f := by
  intro R _ _ I hR D A G _ _ _ U k _ hall F f hf
  obtain ⟨s, r, hr, σ₀, f₀, -, hf₀, hE⟩ := hall F
  have hw : (D.toPre.prB (FractionRing R)).left ≫ D.toPre.P.A.hom = (D.toPre.BF (FractionRing R)).hom := Over.w _
  have hm : ∀ α, DVR.SecIsMul D.toPre.P.A.hom r (f₀ α) (f α) := fun α =>
    GlobalTheory.IntegralExpansion.secIsMul_of_secScal D.toPre.P.isLB D.toPre.P.A.hom
      (fun W => GlobalTheory.IntegralExpansion.prB_app_injective D.toPre W) (hf α) (by rw [hw]; exact hf₀ α)
  have hm' : ∀ α, ∀ j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j := fun α j => hm α j
  obtain ⟨σ, hσ⟩ := GlobalTheory.sec_div_of_expandsAt R I hR D A G U k r hr σ₀ f₀ f hm' hE
  exact ⟨σ, GlobalTheory.T.expandsAt_cancel_nonzero_scalar R I hR D A G U k r hr σ₀ σ f₀ f hm' hσ hE⟩

end GlobalTheory

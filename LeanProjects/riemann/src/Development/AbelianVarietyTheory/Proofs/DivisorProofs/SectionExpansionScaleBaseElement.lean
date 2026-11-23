import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSecIsMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.UU.expT_scale : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU I D A G) (k : ℕ) (q : R) (σ τ : U.SecGT (𝟙_ _) k) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) k α), ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ G).hom q σ τ → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → U.ExpT (𝟙_ _) k τ g → U.ExpT (𝟙_ _) k σ f := by
  intro R _ _ I D A G _ _ U k q σ τ f g hσ hf hE e
  obtain ⟨s, hs⟩ := hE e
  refine ⟨s, fun Z x rG rB h1 h2 h3 z JG J hG hB => ?_⟩
  obtain ⟨H1, H2⟩ := hs Z x rG rB h1 h2 h3 z JG J hG hB
  have hc : cst (rB ≫ (𝟙_ _ ⊗ D.P.A).hom) z q = cst (rG ≫ (𝟙_ _ ⊗ G).hom) z q := by
    rw [← Over.w (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) D.P.A), ← Over.w (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G),
      ← Category.assoc, ← Category.assoc, h3]
  have hF : ∀ α, sval (f α) rB z J = cst (rG ≫ (𝟙_ _ ⊗ G).hom) z q * sval (g α) rB z J := fun α => by
    rw [← hc]
    exact GlobalTheory.secIsMul_gs (hf α) rB z _ (hB.mem _ _)
  have hS : sval σ rG z JG = cst (rG ≫ (𝟙_ _ ⊗ G).hom) z q * sval τ rG z JG :=
    GlobalTheory.secIsMul_gs hσ rG z _ (hG.mem _ _)
  refine ⟨fun α hα => by rw [hF, H1 α hα, mul_zero], ?_⟩
  rw [hS, mul_left_comm, H2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by rw [hF, _root_.mul_assoc]

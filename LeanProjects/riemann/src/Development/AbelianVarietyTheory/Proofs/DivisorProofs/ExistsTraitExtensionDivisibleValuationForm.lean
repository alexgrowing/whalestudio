import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLevelPointsOfLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelOKOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrExtensionQkPointsRational
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QValPullbackMulRamificationCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataPullbackInjectiveLocalHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TraitInputExt

theorem exists_ext_dvd_rational : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (O : Type) [CommRing O] (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ₁ : R →+* V₁) (b₁ : O →+* V₁), GlobalTheory.LN.CDvr V₁ → Function.Injective ρ₁ → ρ₁.Finite → IsLocalHom ρ₁ → Function.Injective b₁ → ∀ N : ℕ, 0 < N → ∃ (T : Formalism.L2.Pj.CDVR) (ρ : R →+* T.V) (b : O →+* T.V) (ϖ : T.V) (D' : DegData T.V (maximalIdeal T.V)), Function.Injective ρ ∧ ρ.Finite ∧ Function.Injective b ∧ Irreducible ϖ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ (∀ Q : D'.toPre.X → ℤ, ReciprocityTheory.ChartRestriction.G.DVR.QForm.IsQ D'.toPre ϖ Q → ∀ u v, (N : ℤ) ∣ ReciprocityTheory.ChartRestriction.G.DVR.QForm.bOf D'.toPre Q u v) ∧ ∀ k : ℕ, k ∣ N → ∀ q : QkPt D'.toPre (AlgebraicClosure (FractionRing T.V)) k, ∃ p : QkPt D'.toPre (FractionRing T.V) k, QkExt (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) p q := by
  intro R _ _ _ D O _ V₁ _ _ _ ρ₁ b₁ hV₁ iρ₁ fρ₁ lρ₁ ib₁ N hN
  obtain ⟨D₁, ⟨h₁⟩⟩ := GlobalTheory.MumPull.exists_pull R V₁ ρ₁ iρ₁ lρ₁ D
  obtain ⟨hdvr, hcpl, hch⟩ := (GlobalTheory.LN.cDvr_iff V₁).1 hV₁
  let T₁ : Formalism.L2.Pj.CDVR := { V := V₁ }
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V₁
  obtain ⟨T', g, ϖ, e, ig, fg, hϖ, he, hass, rat⟩ :=
    GlobalTheory.QkRationalExt.exists_cdvr_ext_rational T₁ D₁.toPre D₁.tau_bimult N hN π hπ
  have lg : IsLocalHom g := fg.to_isIntegral.isLocalHom ig
  obtain ⟨D', ⟨hD⟩⟩ := GlobalTheory.MumPull.exists_pull V₁ T'.V g ig lg D₁
  have hc : Nonempty (IsPullDeg (g.comp ρ₁) D.toPre D'.toPre) :=
    GlobalTheory.Mum.nonempty_isPullDeg_comp_of_injective R V₁ T'.V ρ₁ g D.toPre D₁.toPre D'.toPre ig ⟨h₁⟩ ⟨hD⟩
  choose Q₁ hQ₁ using ReciprocityTheory.ChartRestriction.G.DVR.QForm.exists_QVal hπ D₁
  have hNe : (N : ℤ) ∣ (e : ℤ) := by exact_mod_cast he
  refine ⟨T', g.comp ρ₁, g.comp b₁, ϖ, D', ig.comp iρ₁, fg.comp fρ₁, ig.comp ib₁, hϖ, hc, ?_, ?_⟩
  · intro Q hQ u v
    have hq : ∀ y, Q y = e * Q₁ (hD.xe y) := fun y =>
      ReciprocityTheory.ChartRestriction.G.DVR.QForm.QVal_unique hϖ D' (hQ y)
        (GlobalTheory.QValPull.main T₁ T' g D₁.toPre D'.toPre hD π ϖ e ig hπ hϖ hass y _ (hQ₁ _))
    rw [ReciprocityTheory.ChartRestriction.G.DVR.QForm.bOf, hq, hq, hq]
    exact dvd_sub (dvd_sub (hNe.mul_right _) (hNe.mul_right _)) (hNe.mul_right _)
  · intro k hk
    exact rat D'.toPre hD D'.tau_bimult k hk

end GlobalTheory.TraitInputExt

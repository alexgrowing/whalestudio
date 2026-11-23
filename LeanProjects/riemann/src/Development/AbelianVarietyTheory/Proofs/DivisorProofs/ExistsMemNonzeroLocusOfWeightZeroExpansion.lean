import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNzOfPolAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelOfExpT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroOnClosedFibreCompleteLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PreUTheta

theorem exists_mem_nonzeroLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (τ : U.SecGT (𝟙_ _) 1) (g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α), U.ExpT (𝟙_ _) 1 τ g → GlobalTheory.PsiRing.FibNZ (𝟙_ _ ⊗ D.P.A).hom (g 0) → (∀ α, α ≠ 0 → ∃ a ∈ maximalIdeal R, ∃ h : GlobalTheory.UU.SecBT D (𝟙_ _) 1 α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom a (g α) h) → ∃ θ : LB.Sec U.P.L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = closedPoint R := by
  intro R _ _ _ D A G _ _ U τ g hE hnz hmul
  obtain ⟨z₀, hz₀, hn₀⟩ := hnz (closedPoint R)
  have hx : D.P.A.hom ((snd (𝟙_ (Over (Sp R))) D.P.A).left z₀) = closedPoint R :=
    (congrArg (fun q => q z₀) (Over.w (snd (𝟙_ (Over (Sp R))) D.P.A))).trans hz₀
  obtain ⟨y', hy'⟩ := GlobalTheory.ThetaUnit.exists_thick_pt le_rfl 0 D.P.A _ hx
  obtain ⟨y, rfl⟩ := (U.gt 0).q_surj.surj y'
  have hpG : (U.gt 0).pG.left y = (snd (𝟙_ (Over (Sp R))) D.P.A).left z₀ := hy'
  let rG : (thickObj R (maximalIdeal R) 0 G).left ⟶ (𝟙_ (Over (Sp R)) ⊗ G).left :=
    (lift (toUnit _) (fstG (maximalIdeal R) 0 G)).left
  let rB : (thickObj R (maximalIdeal R) 0 G).left ⟶ (𝟙_ (Over (Sp R)) ⊗ D.P.A).left :=
    (lift (toUnit _) (U.gt 0).pG).left
  have h₁ : rG ≫ (snd _ G).left = (fstG (maximalIdeal R) 0 G).left := by
    rw [← Over.comp_left, lift_snd]
  have h₂ : rB ≫ (snd _ D.P.A).left = (U.gt 0).pG.left := by
    rw [← Over.comp_left, lift_snd]
  have h₃ : rB ≫ (fst _ D.P.A).left = rG ≫ (fst _ G).left := by
    rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
  have hinj : ∀ a b : (𝟙_ (Over (Sp R)) ⊗ D.P.A).left,
      (snd (𝟙_ (Over (Sp R))) D.P.A).left a = (snd (𝟙_ (Over (Sp R))) D.P.A).left b → a = b := by
    intro a b hab
    have e := GlobalTheory.PsiExpansion.snd_lift_unit D.P.A
    have key : ∀ c, (lift (toUnit D.P.A) (𝟙 D.P.A)).left ((snd (𝟙_ (Over (Sp R))) D.P.A).left c) = c :=
      fun c => by rw [← Scheme.Hom.comp_apply, e]; rfl
    rw [← key a, ← key b, hab]
  have hrB : rB y = z₀ := hinj _ _ ((congrArg (fun q => q y) h₂).trans hpG)
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' D.P.isLB y
  obtain ⟨JG, hJG⟩ := GlobalTheory.ConstFam.exists_good' U.P.L.isLB y
  obtain ⟨s, hs⟩ := hE 0
  obtain ⟨H₁, H₂⟩ := hs _ (𝟙 _) rG rB (by rw [Category.id_comp]; exact h₁) (by rw [Category.id_comp]; exact h₂) h₃
    y JG J hJG hJ
  have hu : IsUnit (sval (g 0) rB y J) :=
    (GlobalTheory.Ex.OneGen.isUnit_sval_iff (g 0) rB y hJ).2 (by rw [hrB]; exact hn₀)
  have hc' : rB ≫ (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom =
      (thickObj R (maximalIdeal R) 0 G).hom ≫ spMap (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))) :=
    Over.w (lift (toUnit _) (U.gt 0).pG)
  rw [Finset.sum_eq_single 0 (fun α _ hα => by
    obtain ⟨a, ha, h, hh⟩ := hmul α hα
    rw [GlobalTheory.IndivisibleSection.sval_of_secIsMul hh _ y hJ, hc', cst_comp,
      Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha), GlobalTheory.GermDiv.cst_zero, zero_mul, zero_mul])
    (fun h => absurd (H₁ 0 h) hu.ne_zero)] at H₂
  have hτ : IsUnit (sval τ rG y JG) :=
    isUnit_of_mul_isUnit_right (H₂ ▸ hu.mul (Units.isUnit _))
  obtain ⟨σ, hσ⟩ := GlobalTheory.PsiExpansion.exists_sameG U.P.L.isLB τ
  rw [hσ _ rG y JG hJG, h₁] at hτ
  have hm := (GlobalTheory.Ex.OneGen.isUnit_sval_iff σ _ y hJG).1 hτ
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.secOfH0 σ, _, GlobalTheory.ThetaClosed.nonzeroLocus_firstPower_section_subset σ hm, ?_⟩
  have hc : (fstG (maximalIdeal R) 0 G).left ≫ G.hom = (U.gt 0).pG.left ≫ D.P.A.hom :=
    (Over.w (fstG (maximalIdeal R) 0 G)).trans (Over.w (U.gt 0).pG).symm
  exact (congrArg (fun q => q y) hc).trans ((congrArg D.P.A.hom hpG).trans hx)

end GlobalTheory.PreUTheta

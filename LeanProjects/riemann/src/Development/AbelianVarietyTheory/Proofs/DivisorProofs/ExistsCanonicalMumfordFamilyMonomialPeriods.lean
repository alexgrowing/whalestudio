import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedDegenerationTensorPowerMonomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionExtensionToUniformisedSemiAbeliaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationCompleteNormalBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBundleBirigidSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyOfTensorDataPosDefUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegDataTensorPosDefUnimodularFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalMumfordFamilyUniformisesRefinementsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_canonOn_of_isMonomialTau : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ Q : Data R, Q.IsPos (maximalIdeal R) → ∀ (m : ℕ) (t : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ Q.X), Q.IsMonomialTau t β → (∀ i, t i ≠ 0) → (∀ i y z, β i y z = β i z y) → (∀ i y, 0 ≤ β i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (P : LB (G2 G).left), IsMumPol Q G P ∧ CanonOn Q (PrimeSpectrum.basicOpen (∏ i, t i)) G P := by
  intro R _ _ _ hR Q hQ m t β hm ht hs h0 h1
  have hpd : ((GlobalTheory.W8 + GlobalTheory.W8.transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
    rw [GlobalTheory.w8_add_transpose_eq_e8]; exact GlobalTheory.e8_posDef
  have hdet : IsUnit (GlobalTheory.W8 + GlobalTheory.W8.transpose).det := by
    rw [GlobalTheory.w8_add_transpose_eq_e8, GlobalTheory.e8_det_eq_one]; exact isUnit_one
  obtain ⟨D', pr, xe, w, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.exists_degData_tensor_posDef_unimodular_form R hR Q hQ GlobalTheory.W8 hpd hdet
  obtain ⟨F⟩ := GlobalTheory.T.nonempty_of_tensorData_posDef_unimodular R hR Q D' GlobalTheory.W8 hpd hdet (by norm_num) pr xe w h₁ h₂ h₃ h₄ h₅
  obtain ⟨β', hβ', -⟩ := GlobalTheory.T.polarisedDegeneration_tensorPower_monomial R Q D'.toPre GlobalTheory.W8 pr xe hpd ⟨h₁, h₂, h₃, w, h₄, h₅⟩ m t β hm ht hs h0 h1
  have hB : Base R := ⟨⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩, hR.2.2.2⟩
  obtain ⟨G', iG, cG, A', hsa, ⟨U'⟩⟩ := GlobalTheory.T.hasSemiAbelianUniformisation_complete_normal_base R hB D'
  obtain ⟨oA, oG, hlin⟩ := GlobalTheory.T.exists_ringAction_extension_to_uniformised_semiAbelian R hB D' A' G' hsa U' F.O F.o
  have hidem : oG.act F.e ≫ oG.act F.e = oG.act F.e := by rw [← oG.map_mul, F.idem]
  obtain ⟨G, iG2, cutoffSecondDeriv, inc, pr', hsaG, hinc, hpr, e₁, e₂⟩ :=
    GlobalTheory.Mum.IdemImage.isSemiAbelian_image (Sp R) G' hsa (oG.act F.e) (oG.hom F.e) hidem
  have hL : (abelian₂ G' U'.LG.L).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ U'.LG.isLB _ _
  have hC : CanonOn Q (PrimeSpectrum.basicOpen (∏ i, t i)) G _ := ⟨pull_isLB hL _, D', F, A', G', iG, cG, U', oA, oG, inc, pr',
    fun y => hβ'.psiUnitOn y fun p hp => hp, hsa, hlin, hinc, hpr, e₁, e₂, ⟨idIso _, idIso_isGen (pull_isLB hL _)⟩⟩
  exact ⟨G, iG2, cutoffSecondDeriv, _, ⟨hR, hQ, hsaG, GlobalTheory.T.canonicalFamily_bundle_birigid_symmetric R hR Q G _ hC.canon, GlobalTheory.T.canonical_mumford_family_uniformises_refinements R hR Q G _ hsaG hC.canon⟩, hC⟩

end GlobalTheory.Mum

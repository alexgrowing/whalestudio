import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNzOfPolAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniversalSectionBasisPolarisedFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFiniteExtensionSplitSpecialFibrePoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsPrimitivePrincipallyPolarisedTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueAndLinearInSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.OmDvr

theorem exists_unit_of_prim {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {J : Type}
    {c : J → FractionRing V} (b : FractionRing V) (hc : Prim (algebraMap V (FractionRing V)) c)
    (hb : Prim (algebraMap V (FractionRing V)) (fun j => b * c j)) :
    ∃ u : Vˣ, algebraMap V (FractionRing V) u = b := by
  obtain ⟨hc₁, j₀, hj₀, hj₀'⟩ := hc
  obtain ⟨hb₁, j₁, hj₁, hj₁'⟩ := hb
  have I1 : IsIntegral V b := by
    have := IsIntegral.mul (show IsIntegral V (b * c j₀) from hb₁ j₀) (show IsIntegral V (c j₀)⁻¹ from hj₀')
    rwa [_root_.mul_assoc, mul_inv_cancel₀ hj₀, _root_.mul_one] at this
  have hcne : c j₁ ≠ 0 := right_ne_zero_of_mul hj₁
  have I2 : IsIntegral V b⁻¹ := by
    have := IsIntegral.mul (show IsIntegral V (c j₁) from hc₁ j₁) (show IsIntegral V (b * c j₁)⁻¹ from hj₁')
    rwa [mul_inv, mul_left_comm, mul_inv_cancel₀ hcne, _root_.mul_one] at this
  obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 I1
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 I2
  have hb0 : b ≠ 0 := left_ne_zero_of_mul hj₁
  have hvw : v * w = 1 := IsFractionRing.injective V (FractionRing V) (by
    rw [map_mul, hv, hw, mul_inv_cancel₀ hb0, map_one])
  exact ⟨⟨v, w, hvw, by rw [mul_comm, hvw]⟩, hv⟩

theorem polAt_of_polFib {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    {g : ℕ} {K : Type} [Field K] {x : Sp K ⟶ S} (h : PolFib t.G t.PP.L g x) : GlobalTheory.LN.PolAt t x := by
  obtain ⟨P, α, -, hp, hw⟩ := h
  have hN := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := x)
    ((isGrpPullback_pullback t.G x).congr (Category.id_comp _).symm rfl) hp t.PP.isLB P.isLB hN
    ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hN⟩ hw
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) hφ.1 P.isAb.proper,
    amplePt _ _ _ _ _ _ hφ _ _ P.isLB hN e P.ample P.ktriv⟩

end GlobalTheory.UMin.OmDvr

set_option maxHeartbeats 1000000 in
open GlobalTheory.UMin.OmDvr in

theorem GlobalTheory.UMin.exists_sec_nz_of_prim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (θ : SecAt t.G t.PP.L (spMap (algebraMap V (FractionRing V)) ≫ χ)) (pt : Fin N → (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ χ) ⟶ t.G)) (c : Fin N → FractionRing V), Odd m → 3 ≤ m → IsUnit (m : V) → PolFib t.G t.PP.L g (spMap (algebraMap V (FractionRing V)) ≫ χ) → ThList t.G t.PP.L t.PP.rig m _ θ pt c → Prim (algebraMap V (FractionRing V)) c → ∃ σ : SecAt t.G t.PP.L χ, SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap V (FractionRing V))) = SecM.ofSec t.G θ ∧ NZ t.G t.PP.L χ σ := by
  intro E _ _ _ H S t g m N V _ _ _ hV χ θ pt c hm h3 hu hP hT hc
  have hL := t.PP.isLB
  have : IsDiscreteValuationRing V := hV.1
  have := t.semi.comm
  have hpa := GlobalTheory.UMin.OmDvr.polAt_of_polFib t hP
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull Out.CubePf.cubePull χ t
  have hp' := GlobalTheory.SplitPoint.polAt_pullback m₁ hpa (jK V) (𝟙 _) (Category.id_comp _).symm
  obtain ⟨σ₀, hσ₀⟩ := exists_nz_of_polAt abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 E H S t V χ _ m₁ hp'
  have h0V : spMap (RingHom.id V) ≫ χ = χ := (congrArg (· ≫ χ) (Spec.map_id _)).trans (Category.id_comp _)
  have hNZ := hσ₀ V (RingHom.id V) χ h0V
  obtain ⟨P, α, hg, hp, hw⟩ := hP
  have hx0 : spMap (RingHom.id (FractionRing V)) ≫ (spMap (algebraMap V (FractionRing V)) ≫ χ) =
      spMap (algebraMap V (FractionRing V)) ≫ χ :=
    (congrArg (· ≫ _) (Spec.map_id _)).trans (Category.id_comp _)
  obtain ⟨e, he⟩ := exists_univBasis_of_fibre abelianSchemeLaws_all.2 S (Sp (FractionRing V)) t.G t.PP.L hL P _ α hp hw
    (FractionRing V) (𝟙 _) _ (Category.id_comp _)
  obtain ⟨a, ha⟩ := he.ex (RingHom.id _) hx0 (SecM.ofSec t.G θ)
  generalize VVRank.pullS t.G _ (Over.homMk (spMap (RingHom.id V)) h0V : Over.mk χ ⟶ Over.mk χ) σ₀ = σ₁ at hNZ
  obtain ⟨s, hs⟩ := he.ex (RingHom.id _) hx0 (pl (algebraMap V (FractionRing V)) rfl (SecM.ofSec t.G σ₁))
  have hmK : ((m : ℕ) : FractionRing V) ≠ 0 := by
    have := (hu.map (algebraMap V (FractionRing V))).ne_zero
    rwa [map_natCast] at this
  obtain ⟨j₀, hj₀, -⟩ := hc.2
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h00 : SecM.ofSec t.G θ = @id Γ((Over.mk (spMap (algebraMap V (FractionRing V)) ≫ χ)).left, ⊤)
        (GlobalTheory.ZH.fn (0 : FractionRing V)) • SecM.ofSec t.G θ := by
      change _ = fnR (spMap (algebraMap V (FractionRing V)) ≫ χ) 0 • _
      rw [map_zero, zero_smul, ha, map_zero, zero_smul]
    have q := (GlobalTheory.UMin.thG_smul_iff S t.G t.PP.L t.PP.rig hL t.PP.rigGen g m (FractionRing V) _ θ θ (pt j₀) 0 (c j₀) (c j₀) hm
      hmK ⟨P, α, hg, hp, hw⟩ h00 (hT.2.1 j₀)).1 (hT.2.1 j₀)
    exact hj₀ (by simpa using q)

  have hrel : pl (algebraMap V (FractionRing V)) rfl (SecM.ofSec t.G σ₁) =
      fnR (spMap (algebraMap V (FractionRing V)) ≫ χ) (s * a⁻¹) • SecM.ofSec t.G θ := by
    have key : s = (s * a⁻¹) * a := by rw [_root_.mul_assoc, inv_mul_cancel₀ ha0, _root_.mul_one]
    rw [hs, ha, smul_smul, ← map_mul, ← key]
  have hT' : ThList t.G t.PP.L t.PP.rig m (spMap (algebraMap V (FractionRing V)) ≫ χ)
      (SecAt.pull t.G t.PP.L σ₁ (algebraMap V (FractionRing V))) pt (fun j => (s * a⁻¹) * c j) := by
    refine ⟨hT.1, fun j => ?_, hT.2.2⟩
    show ThG t.G t.PP.L t.PP.rig m _ (pt j) (fnR (spMap (algebraMap V (FractionRing V)) ≫ χ) ((s * a⁻¹) * c j))
    rw [map_mul]
    exact ThG.smul hL hrel (hT.2.1 j)
  have hprim := GlobalTheory.UMin.prim_of_polFib E H S t g V hV χ ⟨P, α, hg, hp, hw⟩ _ hNZ m N hm h3 hu (FractionRing V)
    (algebraMap V (FractionRing V)) pt _ (IsFractionRing.injective V (FractionRing V)) hT'
  obtain ⟨u, hu'⟩ := exists_unit_of_prim (s * a⁻¹) hc hprim
  have hpull : pl (algebraMap V (FractionRing V)) rfl (fnR χ (u⁻¹ : Vˣ).val • SecM.ofSec t.G σ₁) = SecM.ofSec t.G θ := by
    rw [pl_smul, hrel, smul_smul, ← map_mul, ← hu', ← map_mul, Units.inv_mul, map_one, map_one, one_smul]
  refine ⟨SecM.toSec t.G (fnR χ (u⁻¹ : Vˣ).val • SecM.ofSec t.G σ₁), hpull, ?_⟩
  obtain ⟨g₀, h₁, h₂⟩ := hNZ
  refine ⟨g₀, h₁, ?_⟩
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h₂
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  change g₀ ∈ Scheme.basicOpen _ (liftHom t.G _ (fnR χ (u⁻¹ : Vˣ).val) * σ₁.f k)
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (((u⁻¹).isUnit.map (fnR χ)).map (liftHom t.G _))]
  exact ⟨Scheme.basicOpen_le _ _ hk, hk⟩

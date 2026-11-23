import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTranslatedBundleIntegralPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameIdentityOfGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionThetaSectionIntegralPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTermZeroIntegralTorusPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

noncomputable section
namespace GlobalTheory.Poinc.Sep.FrameInt

theorem exists_rescale_gen {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (u : Γ(Y, ⊤)ˣ) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val t' r z J = gm r z ⊤ u * val t r z J := by
  refine ⟨⟨fun j => t.s j * res le_top u⟩, fun i j => ?_, fun Z r z J hJ => ?_⟩
  · rw [map_mul, map_mul, ht i j, _root_.mul_assoc]
    refine congrArg (fun q => _ * (_ * q)) (unit_ext fun y hy => ?_)
    exact ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.1 _)).trans
      ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.2 _)).symm
  · exact (map_mul _ _ _).trans ((mul_comm _ _).trans (congrArg (· * _) (gm_res r z le_top (hJ.mem φ r) u)))

end GlobalTheory.Poinc.Sep.FrameInt

namespace GlobalTheory.Poinc.Sep.FrameInt

theorem gs_top_eq {V : Type} [CommRing V] [IsDomain V] (a : V) (z : (TF (R := V) (FractionRing V)).left) :
    gs (toUnit (TF (R := V) (FractionRing V))).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      cst (FractionRing V) z (algebraMap V (FractionRing V) a) := by
  rw [toUnit_left_eq, GlobalTheory.RatioVal.gs_specMap, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  exact (GlobalTheory.RatioVal.gs_id_const z _).symm

theorem map_map_unit {V : Type} [CommRing V] (ε : Vˣ) :
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.toMonoidHom ε) : Vˣ) : V) = ε := by
  show (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ε) = ε
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end GlobalTheory.Poinc.Sep.FrameInt

open GlobalTheory.Poinc.Sep.FrameInt in

theorem GlobalTheory.Poinc.Sep.FrameInt.integral_terms : ∀ (m : ℕ), Odd m → 3 ≤ m → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ k : ℕ, k ≠ 0 → IsUnit (k : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∃ (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)) (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1))) (s₀ : V₁), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ (m ^ 2) = 1 → ∃ c, p = toUnit _ ≫ b c) ∧ (∀ c, (t c).IsGen) ∧ (∀ c (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ (m ^ 2)) ((m ^ 2) ^ 2) 1)), Normd κ → ∀ (Z : Scheme) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J → val (t c) r z J ^ ((m ^ 2) ^ 2) * val κ (r ≫ (b c).left) z J = 1) ∧ (∀ c (Z : Scheme) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J → sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c).left) z J * (val (t c) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (s₀ * u 0 c)) * (val ρ₀ r z J).val) := by
  intro m hm hm3 V₁ _ _ _ hV hk D X C _ e u mo hmo hT θ hθ ρ₀ hρ₀
  haveI : IsNoetherianRing V₁ := hV.1
  haveI : IsIntegrallyClosed V₁ := hV.2.1
  have hN1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨th, g, b, w, hgb, -, hcov, hw, hcoef, ⟨c₀, hc₀⟩, hbN, hfr, -⟩ :=
    thetaTerms_integral D hN1 e _ hT

  have ht : ∀ c, ∃ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1)), t.IsGen ∧
      ∀ z J, Good D.P.L z J → val t (toUnit (TF (R := V₁) (FractionRing V₁))).left z J = val (w c) (𝟙 _) z J := by
    intro c
    obtain ⟨t', ht'⟩ := GlobalTheory.T.exists_generator_translatedBundle_integralPoint V₁ D (b c)
    obtain ⟨ε, hε⟩ := hfr c t' ht'
    obtain ⟨t, htg, htv⟩ := exists_rescale_gen D.P.L _ _ t' ht'
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom.toMonoidHom ε)
    refine ⟨t, htg, fun z J hJ => Units.ext ?_⟩
    rw [htv _ _ z J hJ, Units.val_mul, hε z J hJ, gm_top_eq, map_map_unit]
  choose t htg htv using ht

  obtain ⟨ν, hν⟩ := exists_ratio (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.P.isLB rfl ρ₀ D.rig hρ₀ D.rig_gen
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.thetaFamily_term_zero_integral_torusPoint V₁ D θ hθ th
  choose f hf using fun c => GlobalTheory.T.exists_function_thetaSection_integralPoint V₁ D θ (b c) (t c) (htg c) ρ₀ hρ₀
  obtain ⟨z⟩ := exists_pt (R := V₁) (F := FractionRing V₁)
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB z
  have hTF : (TF (R := V₁) (FractionRing V₁)).hom = (toUnit (TF (R := V₁) (FractionRing V₁))).left := by
    simpa using (Over.w (toUnit (TF (R := V₁) (FractionRing V₁)))).symm
  set ν' : V₁ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of V₁)).hom.hom.toMonoidHom ν with hν'
  have key : ∀ c, algebraMap V₁ (FractionRing V₁) (u 0 c * mo 0) =
      lam * algebraMap V₁ (FractionRing V₁) (f c) * algebraMap V₁ (FractionRing V₁) ν' := by
    intro c
    have h0 := hcoef 0 c
    rw [show e 0 = 0 from map_zero e] at h0
    have a := hlam (g c) (b c) (hgb c) (w c) _ h0 z J hJ
    rw [← htv c z J hJ, _root_.mul_assoc, hf c _ _ z J hJ, gs_top_eq,
      hν _ _ z J hJ, Units.val_mul, gm_top_eq, rigV, hTF] at a
    have a' : cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (u 0 c * mo 0)) *
        (val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
          (toUnit (TF (R := V₁) (FractionRing V₁))).left z J).val =
        cst (FractionRing V₁) z (lam * algebraMap V₁ (FractionRing V₁) (f c) * algebraMap V₁ (FractionRing V₁) ν') *
        (val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
          (toUnit (TF (R := V₁) (FractionRing V₁))).left z J).val := by
      rw [a, cst_eq, cst_eq, cst_eq, cst_eq, map_mul, map_mul]
      ring
    exact cst_inj z ((Units.isUnit _).mul_left_inj.1 a')

  obtain ⟨c₁, hc₁⟩ := (hmo 0).2
  have hinj := IsFractionRing.injective V₁ (FractionRing V₁)
  have hlam0 : lam ≠ 0 := by
    intro h
    have := key c₀
    rw [h, zero_mul, zero_mul] at this
    have h1 : u 0 c₀ * mo 0 = 1 := hc₀
    rw [h1, map_one] at this
    exact one_ne_zero this
  have hν0 : algebraMap V₁ (FractionRing V₁) (ν' : V₁) ≠ 0 :=
    (IsUnit.map (algebraMap V₁ (FractionRing V₁)) ν'.isUnit).ne_zero
  have cross : ∀ c, f c * u 0 c₁ = f c₁ * u 0 c := by
    intro c
    apply hinj
    have k1 := key c
    have k2 := key c₁
    have : lam * algebraMap V₁ (FractionRing V₁) ν' *
        algebraMap V₁ (FractionRing V₁) (f c * u 0 c₁) =
        lam * algebraMap V₁ (FractionRing V₁) ν' * algebraMap V₁ (FractionRing V₁) (f c₁ * u 0 c) := by
      rw [map_mul, map_mul]
      have e1 : lam * algebraMap V₁ (FractionRing V₁) (f c) * algebraMap V₁ (FractionRing V₁) ν' *
          algebraMap V₁ (FractionRing V₁) (u 0 c₁) = algebraMap V₁ (FractionRing V₁) (u 0 c * mo 0) *
          algebraMap V₁ (FractionRing V₁) (u 0 c₁) := by rw [k1]
      have e2 : lam * algebraMap V₁ (FractionRing V₁) (f c₁) * algebraMap V₁ (FractionRing V₁) ν' *
          algebraMap V₁ (FractionRing V₁) (u 0 c) = algebraMap V₁ (FractionRing V₁) (u 0 c₁ * mo 0) *
          algebraMap V₁ (FractionRing V₁) (u 0 c) := by rw [k2]
      simp only [map_mul] at e1 e2
      linear_combination e1 - e2
    exact mul_left_cancel₀ (mul_ne_zero hlam0 hν0) this
  refine ⟨b, t, f c₁ * ↑(hc₁.unit⁻¹), hcov, htg, ?_, ?_⟩
  · intro c κ hκ Z r z' J' hJ'
    refine GlobalTheory.T.integralFrame_identity_of_genericPoint V₁ D (m ^ 2) (b c) (hbN c) (t c) (htg c) κ hκ (fun y I hI => ?_) Z r z' J' hJ'
    rw [htv c y I hI]
    have := (hw c).2 κ hκ y I hI
    rwa [show (g c).b.left = (toUnit (TF (R := V₁) (FractionRing V₁))).left ≫ (b c).left from
      congrArg (fun q => q.left) (hgb c)] at this
  · intro c Z r z' J' hJ'
    have hs : f c = f c₁ * ↑(hc₁.unit⁻¹) * u 0 c := by
      rw [mul_right_comm, ← cross c, _root_.mul_assoc, IsUnit.mul_val_inv, _root_.mul_one]
    rw [hf c Z r z' J' hJ', hs]

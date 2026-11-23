import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoCarriesSharpPointsToConjugates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameIdentityOfGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiZeroMulRigidificationKEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiSqGenericPointEqMonomialMulSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyCoefficientIntegralTorusPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSquareProductIsFunctionOnSpecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalProductIdentityOfGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitCoefficientOfThetaSquareIntegralTorsionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

noncomputable section

namespace GlobalTheory.Poinc.Sep.CoefInt

theorem rescale_gen {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (u : Γ(Y, ⊤)ˣ) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val t' r z J = gm r z ⊤ u * val t r z J := by
  refine ⟨⟨fun j => t.s j * res le_top u⟩, fun i j => ?_, fun Z r z J hJ => ?_⟩
  · rw [map_mul, map_mul, ht i j, _root_.mul_assoc]
    refine congrArg (fun q => _ * (_ * q)) (unit_ext fun y hy => ?_)
    exact ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.1 _)).trans
      ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.2 _)).symm
  · exact (map_mul _ _ _).trans ((mul_comm _ _).trans (congrArg (· * _) (gm_res r z le_top (hJ.mem φ r) u)))

theorem gs_top {V : Type} [CommRing V] [IsDomain V] (a : V) (z : (TF (R := V) (FractionRing V)).left) :
    gs (toUnit (TF (R := V) (FractionRing V))).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      cst (FractionRing V) z (algebraMap V (FractionRing V) a) := by
  rw [toUnit_left_eq, GlobalTheory.RatioVal.gs_specMap, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  exact (GlobalTheory.RatioVal.gs_id_const z _).symm

theorem unit_map_map {V : Type} [CommRing V] (ε : Vˣ) :
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.toMonoidHom ε) : Vˣ) : V) = ε := by
  show (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ε) = ε
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end GlobalTheory.Poinc.Sep.CoefInt

namespace GlobalTheory.Poinc.Sep.CoefInt

theorem integral_sq_terms : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ →
    (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.PsiEven → D.TauBimult →
    ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁),
    (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D N₁ e (fun mu c => u mu c * mo mu) →
    ∀ (τ₀ : GlobalTheory.UChart.Gens D) (m N : ℕ) (s : Fin m ⊕ Fin N → V₁) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ D.X)
      (hs : ∀ k, IsUnit (s (.inr k))),
    GlobalTheory.UChart.TauIn D τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) →
    (∀ mu, algebraMap V₁ (FractionRing V₁) (mo mu) ^ 2 =
      ∏ k, algebraMap V₁ (FractionRing V₁) (s (.inl k)) ^ ε (.inl k) (e mu) (e mu)) →
    ∃ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
      (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A))
      (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1)))
      (χt : ∀ (mu : X) (c : C), LB.Gen (LB.LinComb D.P.L
        ![(D.c (e mu) * b c).left, (D.c (e mu)).left, (b c).left, (η[D.P.A]).left] DegPre.gtε))
      (s₀ : V₁) (G : X → C → V₁),
      (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
        IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
        GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') ∧
      (∀ c, b c ^ N₁ = 1) ∧
      (∀ c, (t c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
          val (t c) r z J ^ (N₁ ^ 2) * val κ (r ≫ (b c).left) z J = 1) ∧
      (∀ mu c, (χt mu c).IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c (e mu)) (toUnit T ≫ b c ^ i) (toUnit T ≫ b c) =
          val (χt mu c) T.hom z J ^ N₁) ∧
      IsUnit s₀ ∧
      (∀ mu c, u mu c ^ 2 * s₀ = ((∏ k, (hs k).unit ^ ε (.inr k) (e mu) (e mu) : V₁ˣ) : V₁) * G mu c) ∧
      ∀ mu c (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
        gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c)) =
          sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c * D.c (e mu)).left) z J ^ 2 *
            (val (t c) r z J ^ 2 * val (χt mu c) r z J ^ 2 * val D.sym (r ≫ (D.c (e mu)).left) z J *
              (val (τ₀ (e mu) (-e mu)) r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val := by
  intro N₁ hN₁ V₁ _ _ _ hV hunit D hPE hTB X C _ e u mo hmo hT τ₀ m N s ε hs hτ hmo2
  haveI : IsNoetherianRing V₁ := hV.1
  haveI : IsIntegrallyClosed V₁ := hV.2.1
  have hN1 : 1 ≤ N₁ := by omega
  obtain ⟨th, g, b, w, hgb, ho, hcov, hw, hcoef, ⟨c₀, hc₀⟩, hbN, hfr, -⟩ := thetaTerms_integral D hN1 e _ hT
  obtain ⟨θ, hθ, -, hlamE, -, -⟩ := ThetaOne.main hV D
  obtain ⟨lam, hlam, -⟩ := hlamE (FractionRing V₁) th
  have hψ0 := GlobalTheory.T.psi_zero_mul_rigidificationK_eq_one V₁ D hTB

  have ht : ∀ c, ∃ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1)), t.IsGen ∧
      ∀ z J, Good D.P.L z J → val t (toUnit (TF (R := V₁) (FractionRing V₁))).left z J = val (w c) (𝟙 _) z J := by
    intro c
    obtain ⟨t', ht'⟩ := GlobalTheory.Poinc.Sep.ConjPt.exists_gen_local (D := D) ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1)
    obtain ⟨ε', hε'⟩ := hfr c t' ht'
    obtain ⟨t, htg, htv⟩ := rescale_gen D.P.L _ _ t' ht'
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom.toMonoidHom ε')
    refine ⟨t, htg, fun z J hJ => Units.ext ?_⟩
    rw [htv _ _ z J hJ, Units.val_mul, hε' z J hJ, gm_top_eq, unit_map_map]
  choose t htg htv using ht

  have hχ : ∀ mu c, ∃ χt : LB.Gen (LB.LinComb D.P.L
        ![(D.c (e mu) * b c).left, (D.c (e mu)).left, (b c).left, (η[D.P.A]).left] DegPre.gtε), χt.IsGen ∧
      (∀ z J, Good D.P.L z J → val χt (toUnit (TF (R := V₁) (FractionRing V₁))).left z J =
        val ((g c).s (e mu)) (𝟙 _) z J) ∧
      (∀ z J, Good D.P.L z J → ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit (TF (R := V₁) (FractionRing V₁)) ≫ D.c (e mu))
        (toUnit (TF (R := V₁) (FractionRing V₁)) ≫ b c ^ i) (toUnit (TF (R := V₁) (FractionRing V₁)) ≫ b c) =
        val χt (toUnit (TF (R := V₁) (FractionRing V₁))).left z J ^ N₁) := by
    intro mu c
    obtain ⟨t', ht'⟩ := GlobalTheory.Poinc.Sep.ConjPt.exists_gen_local (D := D)
      ![(D.c (e mu) * b c).left, (D.c (e mu)).left, (b c).left, (η[D.P.A]).left] DegPre.gtε
    obtain ⟨ε', h1, h2⟩ := char_unit hN1 (g c) (b c) (hgb c) (ho c) (e mu) t' ht'
    obtain ⟨χt, hg, hv⟩ := rescale_gen D.P.L _ _ t' ht'
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom.toMonoidHom ε')
    refine ⟨χt, hg, fun z J hJ => Units.ext ?_, fun z J hJ => Units.ext ?_⟩
    · rw [hv _ _ z J hJ, Units.val_mul, h1 z J hJ, gm_top_eq, unit_map_map]
    · rw [h2 z J hJ, hv _ _ z J hJ, mul_pow, Units.val_mul]
      simp only [Units.val_pow_eq_pow_val]
      rw [gm_top_eq, unit_map_map]
  choose χt hχg hχv hχc using hχ

  have hG : ∀ mu c, ∃ G : V₁, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
      gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom G) =
        sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c * D.c (e mu)).left) z J ^ 2 *
          (val (t c) r z J ^ 2 * val (χt mu c) r z J ^ 2 * val D.sym (r ≫ (D.c (e mu)).left) z J *
            (val (τ₀ (e mu) (-e mu)) r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val := fun mu c =>
    GlobalTheory.T.thetaSquare_product_isFunction_on_spec V₁ D θ (b c) (e mu) (t c) (htg c) (χt mu c) (hχg mu c) (τ₀ (e mu) (-e mu)) (hτ _ _).1
  choose G hGv using hG
  have hk := fun mu => GlobalTheory.T.psi_sq_genericPoint_eq_monomial_mul_symmetric V₁ D hPE hψ0 τ₀ _ _ _ hτ (e mu)
  choose k hkv hkψ using hk
  obtain ⟨z⟩ := exists_pt (R := V₁) (F := FractionRing V₁)
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB z
  have key : ∀ mu c, algebraMap V₁ (FractionRing V₁) (u mu c * mo mu) ^ 2 =
      lam ^ 2 * (k mu : FractionRing V₁) * algebraMap V₁ (FractionRing V₁) (G mu c) := by
    intro mu c
    have E1 := GlobalTheory.T.thetaFamily_coefficient_integral_torusPoint V₁ D θ lam th hlam hψ0 (e mu) (g c) (b c) (hgb c) (w c) _ (hcoef mu c) z J hJ
    have E2 := hkψ mu z J hJ
    have E3 := hGv mu c _ (toUnit (TF (R := V₁) (FractionRing V₁))).left z J hJ
    rw [gs_top, htv c z J hJ, hχv mu c z J hJ] at E3
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at E2 E3
    apply cst_inj z
    rw [cst_eq] at E2 E3
    rw [cst_eq, cst_eq] at E1
    rw [cst_eq, cst_eq, map_pow (cstH z), E1, map_mul (cstH z), map_mul (cstH z), map_pow (cstH z), E3,
      mul_pow, mul_pow, mul_pow, mul_pow, E2]
    ring

  have hinj := IsFractionRing.injective V₁ (FractionRing V₁)
  have hsplit : ∀ mu, (k mu : FractionRing V₁) =
      (∏ j, algebraMap V₁ (FractionRing V₁) (s (.inl j)) ^ ε (.inl j) (e mu) (e mu)) *
      ∏ j, algebraMap V₁ (FractionRing V₁) (s (.inr j)) ^ ε (.inr j) (e mu) (e mu) := by
    intro mu
    rw [hkv mu, ← Fintype.prod_sum_type (fun j => algebraMap V₁ (FractionRing V₁) (s j) ^ ε j (e mu) (e mu))]
    exact Fintype.prod_equiv finSumFinEquiv.symm _ _ (fun _ => rfl)
  have hk0 : (k 0 : FractionRing V₁) = 1 := by
    rw [hkv]; simp
  have hl0 : lam ^ 2 * algebraMap V₁ (FractionRing V₁) (G 0 c₀) = 1 := by
    have := key 0 c₀
    rw [hc₀, map_one, one_pow, hk0, _root_.mul_one] at this
    exact this.symm
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.isUnit_coefficient_of_thetaSquare_integralTorsion N₁ hN₁ V₁ hV hunit D θ hθ C b hcov
  have hb1 : b c₁ * D.c (e 0) = b c₁ := by rw [map_zero, ThetaOne.c_zero, _root_.mul_one]
  have hG1 : IsUnit (G 0 c₁) := hc₁ (G 0 c₁) (fun Z r z J => val (t c₁) r z J ^ 2 * val (χt 0 c₁) r z J ^ 2 *
      val D.sym (r ≫ (D.c (e 0)).left) z J * (val (τ₀ (e 0) (-e 0)) r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹)
    (fun Z r z J hJ => by rw [hGv 0 c₁ Z r z J hJ, hb1])
  have hs₀u : IsUnit (G 0 c₀) := by
    have k1 := key 0 c₁
    rw [hk0, _root_.mul_one] at k1
    refine IsUnit.of_mul_eq_one ((u 0 c₁ * mo 0) ^ 2 * ↑hG1.unit⁻¹) (hinj ?_)
    rw [map_mul, map_mul, map_one, map_pow, k1]
    have hGne : algebraMap V₁ (FractionRing V₁) (G 0 c₁) * algebraMap V₁ (FractionRing V₁) ↑hG1.unit⁻¹ = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    linear_combination (algebraMap V₁ (FractionRing V₁) (G 0 c₀) * lam ^ 2) * hGne + hl0
  have hP : ∀ mu, algebraMap V₁ (FractionRing V₁) ((∏ k, (hs k).unit ^ ε (.inr k) (e mu) (e mu) : V₁ˣ) : V₁) =
      ∏ k, algebraMap V₁ (FractionRing V₁) (s (.inr k)) ^ ε (.inr k) (e mu) (e mu) := by
    intro mu
    rw [Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    change (((Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom ((hs k).unit ^ ε (.inr k) (e mu) (e mu)) :
      (FractionRing V₁)ˣ)) : FractionRing V₁) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map, IsUnit.unit_spec]
    rfl
  refine ⟨θ, b, t, χt, G 0 c₀, G, hθ, hbN, fun c => ⟨htg c, fun κ hκ Z r z' J' hJ' => ?_⟩,
    fun mu c => ⟨hχg mu c, fun T z' J' hJ' =>
      GlobalTheory.T.cubicalProduct_identity_of_genericPoint V₁ D N₁ (b c) (D.c (e mu)) (hbN c) (χt mu c) (hχg mu c) (hχc mu c) T z' J' hJ'⟩,
    hs₀u, fun mu c => ?_, hGv⟩
  · refine GlobalTheory.T.integralFrame_identity_of_genericPoint V₁ D N₁ (b c) (hbN c) (t c) (htg c) κ hκ (fun y I hI => ?_) Z r z' J' hJ'
    rw [htv c y I hI]
    have := (hw c).2 κ hκ y I hI
    rwa [show (g c).b.left = (toUnit (TF (R := V₁) (FractionRing V₁))).left ≫ (b c).left from
      congrArg (fun q => q.left) (hgb c)] at this
  · apply hinj
    have km := key mu c
    rw [hsplit, map_mul, mul_pow, ← hmo2 mu] at km
    have hmo0 : algebraMap V₁ (FractionRing V₁) (mo mu) ^ 2 ≠ 0 :=
      pow_ne_zero _ ((map_ne_zero_iff _ hinj).2 (hmo mu).1)
    have h3 : algebraMap V₁ (FractionRing V₁) (u mu c) ^ 2 =
        lam ^ 2 * (∏ j, algebraMap V₁ (FractionRing V₁) (s (.inr j)) ^ ε (.inr j) (e mu) (e mu)) *
          algebraMap V₁ (FractionRing V₁) (G mu c) :=
      mul_left_cancel₀ hmo0 (by linear_combination km)
    rw [map_mul, map_mul, map_pow, hP, h3]
    linear_combination ((∏ j, algebraMap V₁ (FractionRing V₁) (s (.inr j)) ^ ε (.inr j) (e mu) (e mu)) *
      algebraMap V₁ (FractionRing V₁) (G mu c)) * hl0

end GlobalTheory.Poinc.Sep.CoefInt

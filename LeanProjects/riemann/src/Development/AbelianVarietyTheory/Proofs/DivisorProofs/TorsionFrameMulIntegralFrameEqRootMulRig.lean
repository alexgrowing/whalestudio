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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT

namespace GlobalTheory.USep.FrameRoot

theorem exists_normd {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (ρ : LB.Gen (D.P.L.pull (eSec D.P.A)))
    (hρ : ρ.IsGen) (n : ℕ)
    (α : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![𝟙 D.P.A.left, (mulA D.P.A n).left] ![(n : ℤ) ^ 2, -1]))
    (hα : α.IsGen) (hn : IsNormMul D.P.A D.P.L ρ n α) :
    ∃ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
        val κ r z J = val α r z J * val ρ (r ≫ D.P.A.hom) z J * (val ρ (r ≫ D.P.A.hom) z J ^ (n ^ 2))⁻¹ := by
  have hL := D.P.isLB
  let p := LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) ρ D.P.A.hom
  have hp : p.IsGen := DVR.pullGen_isGen _ _ _ _ hρ _
  let u := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ α p) (LB.invGen D.P.L _ _ (GeneratorPullback.powGen D.P.L _ _ p (n ^ 2)))
  have hu : u.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hα hp)
    (DVR.invGen_isGen _ _ _ _ (DVR.SectionScalarValuation.powGen_isGen' _ _ _ _ hp _))
  have h1 : (1 : D.P.A ⟶ D.P.A).left = D.P.A.hom ≫ eSec D.P.A := rfl
  obtain ⟨κ, hκ, hv⟩ := exists_gen hL
    (φ' := (![𝟙 _, (𝟙 D.P.A ^ n).left, (1 : D.P.A ⟶ D.P.A).left] : Fin 3 → (D.P.A.left ⟶ D.P.A.left)))
    (ε' := ![((n ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - ((n ^ 2 : ℕ) : ℤ)]) (by
      intro U _ h
      rw [h1]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module) u hu
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
      val κ r z J = val α r z J * val ρ (r ≫ D.P.A.hom) z J * (val ρ (r ≫ D.P.A.hom) z J ^ (n ^ 2))⁻¹ :=
    fun Z r z J hJ => by
      have a : val p r z J = val ρ (r ≫ D.P.A.hom) z J := val_pull hJ _ _ _
      refine (hv Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg _ a)) ((val_inv _ _).trans (congrArg (·⁻¹) ?_))))
      exact (GlobalTheory.RatioVal.val_powGen _ _ _ _ _).trans (congrArg (· ^ (n ^ 2)) a)
  refine ⟨κ, ⟨hκ, corr_of_val hL fun y J hJ => ?_⟩, key⟩
  have a₃ : val (rigPow D.P.A D.P.L ρ ((n : ℤ) ^ 2)) (𝟙 _) y J = val ρ (𝟙 _) y J ^ ((n : ℤ) ^ 2) := map_zpow _ _ _
  have e₁ : (𝟙 _ ≫ eSec D.P.A) ≫ D.P.A.hom = 𝟙 _ := by
    rw [Category.id_comp]; exact Over.w η[D.P.A]
  have b := (val_pull hJ α (eSec D.P.A) (𝟙 _)).symm.trans ((val_corr hJ hn (𝟙 _)).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) a₃ (val_inv ρ (𝟙 _)))))
  refine (val_pull hJ κ _ _).trans ((key _ _ y J hJ).trans (Eq.trans ?_ (val_one _).symm))
  rw [b]
  refine (congrArg (fun q => val ρ (𝟙 _) y J ^ ((n : ℤ) ^ 2) * (val ρ (𝟙 _) y J)⁻¹ * val ρ q y J *
    (val ρ q y J ^ (n ^ 2))⁻¹) e₁).trans ?_
  rw [← Nat.cast_pow, zpow_natCast, inv_mul_cancel_right, mul_inv_cancel]

theorem val_rigT {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (T : Over S) (k : ℤ) {Z : Scheme.{0}}
    (r : Z ⟶ T.left) {z : Z} {J : (Z ⟶ P.A.left) → P.L.ι} (hJ : Good P.L z J) :
    val (rigT P.A P.L rig T k) r z J = val rig (r ≫ T.hom) z J ^ k := by
  rw [val_of rig (r ≫ T.hom) z J (fun _ => J (r ≫ T.hom ≫ eSec P.A))
    (fun _ => by rw [Category.assoc])]
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec P.A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ?_)
  exact (gm_res r z _ hm _).trans (gm_pull r T.hom z
    (LB.wchart P.L (fun _ : PUnit => eSec P.A) (fun _ => J (r ≫ T.hom ≫ eSec P.A)))
    (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hm 0) _)

theorem exists_root {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (T : Over (Sp V))
    (ρ : LB.Gen (D.P.L.pull (eSec D.P.A))) (hρ : ρ.IsGen) (n : ℕ) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A)
    (τ : LB.Gen (LB.LinComb D.P.L (Y := T.left) (K := Fin 1) (fun _ => (toUnit T ≫ b).left) (fun _ => 1)))
    (hτ : IsTorsFrame D.P ρ n (toUnit T ≫ b) τ)
    (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))) (ht : t.IsGen)
    (H : ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ → ∀ (z : T.left) J, Good D.P.L z J →
      val t T.hom z J ^ (n ^ 2) * val κ (T.hom ≫ b.left) z J = 1) :
    ∃ c : Γ(T.left, ⊤)ˣ, c ^ (n ^ 2) = 1 ∧ ∀ (z : T.left) J, Good D.P.L z J →
      val τ (𝟙 _) z J * val t T.hom z J = gm (𝟙 T.left) z ⊤ c * val ρ T.hom z J := by
  have hL := D.P.isLB
  obtain ⟨-, hτg, α, hα, hn, hc⟩ := hτ
  obtain ⟨κ, hκ, hv⟩ := exists_normd D ρ hρ n α hα hn
  have hx : (toUnit T ≫ b).left = T.hom ≫ b.left := rfl
  let p := LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) ρ T.hom
  have hp : p.IsGen := DVR.pullGen_isGen _ _ _ _ hρ _
  let q := LB.pullGen D.P.L _ _ t T.hom
  have hq : q.IsGen := DVR.pullGen_isGen _ _ _ _ ht _
  obtain ⟨u, hu, hw⟩ := exists_gen hL (φ' := fun _ : PUnit => T.hom ≫ eSec D.P.A) (ε' := fun _ => 1) (by
      intro U _ h
      rw [hx]
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, DegPre.lineε, eSec, mul_comm, mul_left_comm])
    (LB.mulGen D.P.L _ _ _ _ τ q) (DVR.mulGen_isGen _ _ _ _ _ _ _ hτg hq)
  obtain ⟨c, hcv⟩ := GlobalTheory.CoordSep.exists_ratio_base hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _)
    (fun a => ⟨a, rfl⟩) hu hp
  have key : ∀ (z : T.left) J, Good D.P.L z J →
      val τ (𝟙 _) z J * val t T.hom z J = gm (𝟙 T.left) z ⊤ c * val ρ T.hom z J := fun z J hJ => by
    have a : val p (𝟙 _) z J = val ρ T.hom z J := (val_pull hJ _ _ _).trans (by rw [Category.id_comp])
    have a' : val q (𝟙 _) z J = val t T.hom z J := (val_pull hJ _ _ _).trans (by rw [Category.id_comp])
    have e := hcv _ (𝟙 _) z J hJ
    rw [hw _ _ z J hJ, val_mul hJ, a, a', Category.id_comp, mul_comm (val ρ T.hom z J)] at e
    exact e
  refine ⟨c, unit_ext fun z _ => ?_, key⟩
  choose J hJ using fun χ : T.left ⟶ D.P.A.left => exists_chart hL (χ z)
  replace hJ : Good D.P.L z J := hJ
  have e₁ : (T.hom ≫ b.left) ≫ D.P.A.hom = T.hom := Over.w (toUnit T ≫ b)
  have h₁ := H κ hκ z J hJ
  rw [hv _ _ z J hJ, e₁] at h₁
  have a₃ : val (powFrame D.P.A D.P.L _ τ ((n : ℤ) ^ 2)) (𝟙 _) z J = val τ (𝟙 _) z J ^ ((n : ℤ) ^ 2) := map_zpow _ _ _
  have h₂ := a₃.symm.trans ((val_corr hJ hc (𝟙 _)).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_pull hJ α _ _) (val_rigT D.P ρ T 1 _ hJ))))
  replace h₂ : val τ (𝟙 _) z J ^ (n ^ 2) = val α (T.hom ≫ b.left) z J * val ρ T.hom z J := by
    rw [← zpow_natCast, Nat.cast_pow, h₂, zpow_one, Category.id_comp, Category.id_comp, hx]
  have h₃ := congrArg (· ^ (n ^ 2)) (key z J hJ)
  simp only [mul_pow] at h₃
  rw [map_pow, map_one]
  have aux : ∀ {U : Type} [CommGroup U] (a s g r r' w : U), s * (w * r' * r⁻¹) = 1 → a = w * r' → a * s = g * r →
      g = 1 := by
    rintro U _ a s g r r' w h rfl h'
    rw [← h, ← _root_.mul_assoc, mul_comm s, h', mul_inv_cancel_right]
  exact aux _ _ _ _ _ _ h₁ h₂ h₃

theorem frame_mul_eq_root : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (n : ℕ), 1 ≤ n → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A) (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => (toUnit (Over.mk (spMap ev)) ≫ b).left) (fun _ => 1))), IsTorsFrame D.P ρ₀ n (toUnit (Over.mk (spMap ev)) ≫ b) τ → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → (∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ → ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → val t (Over.mk (spMap ev)).hom z J ^ (n ^ 2) * val κ ((Over.mk (spMap ev)).hom ≫ b.left) z J = 1) → ∃ ζ : K, ζ ^ (n ^ 2) = 1 ∧ ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → (val τ (𝟙 _) z J).val * (val t (Over.mk (spMap ev)).hom z J).val = gs (𝟙 (Over.mk (spMap ev)).left) z ⊤ (GlobalTheory.Ex.fnOf ζ) * (val ρ₀ (Over.mk (spMap ev)).hom z J).val := by
  intro V₁ _ _ D K _ ev ρ₀ hρ n _ b τ hτ t ht H
  obtain ⟨c, hc, hv⟩ := exists_root D (Over.mk (spMap ev)) ρ₀ hρ n b τ hτ t ht H
  let e : Γ((Over.mk (spMap ev)).left, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have he : ∀ a : K, GlobalTheory.Ex.fnOf a = e.symm a := fun _ => rfl
  refine ⟨e c.val, ?_, fun z J hJ => ?_⟩
  · rw [← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]
  · rw [he, e.symm_apply_apply, gs_unit _ _ ⊤ trivial, ← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val (hv z J hJ)

end GlobalTheory.USep.FrameRoot
